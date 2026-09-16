"""Independent certificate and trace checker; no search imports, no dependencies.

Checks finite exact-region receipts, not Lean proof terms. Its mathematical
justification is in article/forge_ordered.tex. Resource limits are refusal
conditions. They never change the mathematical interpretation of an input.
"""
from __future__ import annotations
import json
from typing import Any

MAX_ITEMS = 200000
MAX_BITS = 4096
MAX_WORD = 8192
MAX_BYTES = 64 * 1024 * 1024


class Reject(ValueError):
    pass


def need(condition: bool, message: str) -> None:
    if not condition:
        raise Reject(message)


def nat(x: Any, label: str = 'natural') -> int:
    need(type(x) is int and x >= 0, f'{label}: expected natural integer, not float/bool')
    need(x.bit_length() <= MAX_BITS, f'{label}: integer too large')
    return x


def idx(x: Any, bound: int, label: str = 'index') -> int:
    x = nat(x, label)
    need(x < bound, f'{label}: out of range')
    return x


def obj(x: Any, keys: set[str], label: str) -> None:
    need(type(x) is dict and set(x) == keys, f'{label}: wrong fields')


def arr(x: Any, length: int | None = None, label: str = 'array') -> list:
    need(type(x) is list, f'{label}: expected array')
    need(len(x) <= MAX_ITEMS, f'{label}: too many entries')
    if length is not None:
        need(len(x) == length, f'{label}: wrong dimension')
    return x


def canon(x: Any) -> str:
    return json.dumps(x, sort_keys=True, separators=(',', ':'), ensure_ascii=True,
                      allow_nan=False)


def load_json(path: str) -> Any:
    """Reject duplicate keys, floating-point tokens and nonfinite constants."""
    def pairs(ps):
        out = {}
        for k, v in ps:
            need(k not in out, 'duplicate JSON object key')
            out[k] = v
        return out
    def no_float(text):
        raise Reject('floating-point/nonfinite JSON token')
    with open(path, 'rb') as f:
        data = f.read(MAX_BYTES + 1)
    need(len(data) <= MAX_BYTES, 'JSON input exceeds byte limit')
    try:
        return json.loads(data, object_pairs_hook=pairs,
                          parse_float=no_float, parse_constant=no_float)
    except (UnicodeError, json.JSONDecodeError, RecursionError) as ex:
        raise Reject(f'invalid or overly deep JSON: {ex}') from ex


def subseq(s: str, t: str) -> bool:
    """Dynamic programming, deliberately not the producer's greedy routine."""
    n = len(s)
    if n > len(t):
        return False
    # possible[k]: first k symbols of s embed into the processed part of t.
    possible = [False] * (n + 1)
    possible[0] = True
    for letter in t:
        for k in range(n, 0, -1):
            if letter == s[k - 1] and possible[k - 1]:
                possible[k] = True
    return possible[n]


def validate_problem(p: Any) -> None:
    need(type(p) is dict and p.get('kind') in ('resource', 'lossy'), 'unknown model language')
    if p['kind'] == 'resource':
        obj(p, {'kind', 'controls', 'dimension', 'transitions', 'bad'}, 'resource model')
        d = nat(p['dimension'])
    else:
        obj(p, {'kind', 'controls', 'channels', 'alphabet', 'transitions', 'bad'}, 'lossy model')
        d = nat(p['channels'])
        alphabet = arr(p['alphabet'])
        need(all(type(x) is str and len(x) == 1 for x in alphabet), 'alphabet: single symbols required')
        need(len(set(alphabet)) == len(alphabet), 'duplicate alphabet symbol')
    need(1 <= d <= 64, 'supported dimension/channel count is 1..64')
    q = nat(p['controls'])
    need(1 <= q <= MAX_ITEMS, 'invalid finite control count')
    for t in arr(p['transitions']):
        if p['kind'] == 'resource':
            obj(t, {'source', 'target', 'consume', 'matrix', 'produce'}, 'resource transition')
            for v in (t['consume'], t['produce']):
                for x in arr(v, d):
                    nat(x)
            for row in arr(t['matrix'], d):
                for x in arr(row, d):
                    nat(x)
        else:
            obj(t, {'source', 'target', 'op', 'channel', 'symbol'}, 'channel transition')
            need(t['op'] in ('send', 'recv', 'tau'), 'unsupported channel operation')
            idx(t['channel'], d, 'channel')
            need(type(t['symbol']) is str, 'symbol must be a string')
            if t['op'] == 'tau':
                need(t['symbol'] == '', 'tau has no symbol')
            else:
                need(t['symbol'] in p['alphabet'], 'symbol outside alphabet')
        idx(t['source'], q, 'source control')
        idx(t['target'], q, 'target control')
    for b in arr(p['bad']):
        validate_state(p, b)


def validate_words(p: dict, words: Any) -> None:
    for w in arr(words, p['channels']):
        need(type(w) is str and len(w) <= MAX_WORD, 'invalid/oversized word')
        need(all(a in p['alphabet'] for a in w), 'word contains unknown symbol')


def validate_state(p: dict, s: Any) -> None:
    obj(s, {'q', 'v'}, 'state')
    idx(s['q'], p['controls'], 'state control')
    if p['kind'] == 'resource':
        for n in arr(s['v'], p['dimension']):
            nat(n)
    else:
        validate_words(p, s['v'])


def below(p: dict, a: dict, b: dict) -> bool:
    if a['q'] != b['q']:
        return False
    if p['kind'] == 'resource':
        return all(a['v'][i] <= b['v'][i] for i in range(p['dimension']))
    return all(subseq(a['v'][i], b['v'][i]) for i in range(p['channels']))


def resource_step(t: dict, x: list[int]) -> list[int] | None:
    if any(x[i] < t['consume'][i] for i in range(len(x))):
        return None
    return [t['produce'][j] + sum(t['matrix'][j][i] * (x[i] - t['consume'][i])
                                  for i in range(len(x)))
            for j in range(len(x))]


def can_cover(p: dict, t: dict, x: dict, y: dict) -> bool:
    if t['source'] != x['q'] or t['target'] != y['q']:
        return False
    if p['kind'] == 'resource':
        v = resource_step(t, x['v'])
        return v is not None and all(v[i] >= y['v'][i] for i in range(len(v)))
    c = t['channel']
    if not all(subseq(y['v'][i], x['v'][i]) for i in range(p['channels']) if i != c):
        return False
    w, u, a = x['v'][c], y['v'][c], t['symbol']
    if t['op'] == 'send':
        return subseq(u, w + a)
    if t['op'] == 'recv':
        return any(letter == a and subseq(u, w[k+1:]) for k, letter in enumerate(w))
    return subseq(u, w)


def verify_box(t: dict, target: list[int], rec: dict) -> list[list[int]]:
    obj(rec, {'kind', 'caps', 'minima', 'tree'}, 'box predecessor receipt')
    A, a, b = t['matrix'], t['consume'], t['produce']
    d = len(a)
    demand = [max(0, target[j] - b[j]) for j in range(d)]
    caps = arr(rec['caps'], d)
    for c in caps:
        nat(c)
    # A sufficient clipping bound, checked by multiplication; no ceil algorithm.
    for i in range(d):
        for j in range(d):
            if A[j][i] > 0:
                need(A[j][i] * caps[i] >= demand[j], 'invalid clipping bound')
    mins = arr(rec['minima'])
    for z in mins:
        for i, zi in enumerate(arr(z, d)):
            nat(zi)
            need(zi <= caps[i], 'minimum lies outside clipping box')
        for j in range(d):
            need(sum(A[j][i] * z[i] for i in range(d)) >= demand[j],
                 'infeasible predecessor minimum')
    need(mins == sorted(mins), 'noncanonical local minimum order')
    for i, x in enumerate(mins):
        for k, y in enumerate(mins):
            if i != k:
                need(not all(x[j] <= y[j] for j in range(d)), 'redundant local minimum')
    pending = [(rec['tree'], [0] * d, list(caps))]
    count = 0
    while pending:
        node, lo, hi = pending.pop()
        count += 1
        need(count <= MAX_ITEMS * 10, 'box tree too large')
        arr(node)
        need(len(node) > 0 and type(node[0]) is str, 'bad box node')
        if node[0] == 'covered':
            need(len(node) == 2, 'covered leaf arity')
            z = mins[idx(node[1], len(mins), 'minimum reference')]
            need(all(z[i] <= lo[i] for i in range(d)), 'box not covered by claimed minimum')
        elif node[0] == 'impossible':
            need(len(node) == 2, 'impossible leaf arity')
            j = idx(node[1], d, 'infeasible row')
            need(sum(A[j][i] * hi[i] for i in range(d)) < demand[j],
                 'box incorrectly declared impossible')
        elif node[0] == 'split':
            need(len(node) == 5, 'split arity')
            i = idx(node[1], d, 'split coordinate')
            k = nat(node[2], 'split point')
            need(lo[i] <= k < hi[i], 'invalid partition split')
            left_hi, right_lo = hi.copy(), lo.copy()
            left_hi[i], right_lo[i] = k, k + 1
            pending.append((node[3], lo.copy(), left_hi))
            pending.append((node[4], right_lo, hi.copy()))
        else:
            raise Reject('unknown box node tag')
    return [[a[i] + z[i] for i in range(d)] for z in mins]


def checked_predecessors(p: dict, t: dict, target: dict, rec: Any) -> list[dict]:
    need(type(rec) is dict and type(rec.get('kind')) is str, 'invalid predecessor receipt')
    if p['kind'] == 'resource':
        d, A = p['dimension'], t['matrix']
        if rec['kind'] == 'diagonal':
            obj(rec, {'kind'}, 'diagonal receipt')
            need(all(A[i][j] == 0 for i in range(d) for j in range(d) if i != j),
                 'diagonal rule applied to nondiagonal matrix')
            result = []
            for j in range(d):
                required = max(0, target['v'][j] - t['produce'][j])
                coefficient = A[j][j]
                if coefficient == 0:
                    if required > 0:
                        return []
                    result.append(t['consume'][j])
                else:
                    quotient, remainder = divmod(required, coefficient)
                    result.append(t['consume'][j] + quotient + int(remainder != 0))
            vectors = [result]
        elif rec['kind'] == 'box':
            vectors = verify_box(t, target['v'], rec)
        else:
            raise Reject('unknown resource predecessor receipt')
    else:
        obj(rec, {'kind'}, 'lossy word receipt')
        need(rec['kind'] == 'lossy-word', 'wrong channel predecessor rule')
        vectors = [list(target['v'])]
        c, u = t['channel'], target['v'][t['channel']]
        if t['op'] == 'send':
            # The sole last position is the only position the appended symbol can fill.
            vectors[0][c] = u[:len(u)-1] if len(u) > 0 and u[-1] == t['symbol'] else u
        elif t['op'] == 'recv':
            vectors[0][c] = ''.join([t['symbol'], u])
    return [{'q': t['source'], 'v': v} for v in vectors]


def verify_direct_cover(p: dict, t: dict, target: dict, rec: dict, basis: list[dict]) -> None:
    """Check a global-region cover of every predecessor, without local minima."""
    need(p['kind'] == 'resource', 'direct resource cover used for non-resource model')
    obj(rec, {'kind', 'caps', 'tree'}, 'direct resource cover')
    d, A = p['dimension'], t['matrix']
    caps = arr(rec['caps'], d)
    demand = [max(0, target['v'][j]-t['produce'][j]) for j in range(d)]
    for i in range(d):
        nat(caps[i])
        for j in range(d):
            if A[j][i] > 0:
                need(A[j][i]*caps[i] >= demand[j], 'invalid direct clipping bound')
    todo = [(rec['tree'], [0]*d, list(caps))]
    count = 0
    while todo:
        node, lower, upper = todo.pop()
        count += 1
        need(count <= MAX_ITEMS*10, 'direct partition too large')
        arr(node)
        need(len(node)>0 and type(node[0]) is str, 'bad direct partition node')
        if node[0] == 'basis':
            need(len(node)==2, 'basis leaf arity')
            b = basis[idx(node[1], len(basis), 'basis coverage index')]
            need(b['q']==t['source'] and all(b['v'][i]<=t['consume'][i]+lower[i] for i in range(d)),
                 'direct predecessor box not covered')
        elif node[0] == 'impossible':
            need(len(node)==2, 'direct impossible leaf arity')
            j = idx(node[1], d)
            need(sum(A[j][i]*upper[i] for i in range(d))<demand[j], 'false direct infeasibility leaf')
        elif node[0] == 'split':
            need(len(node)==5, 'direct split arity')
            i = idx(node[1], d); cut = nat(node[2])
            need(lower[i]<=cut<upper[i], 'bad direct split')
            lu,rl=upper.copy(),lower.copy();lu[i],rl[i]=cut,cut+1
            todo.append((node[3],lower.copy(),lu));todo.append((node[4],rl,upper.copy()))
        else:
            raise Reject('unknown direct partition tag')


def verify(problem: Any, certificate: Any) -> dict[str, int]:
    validate_problem(problem)
    c = certificate
    obj(c, {'format', 'subject', 'nodes', 'basis', 'target_cover', 'closure'}, 'certificate')
    need(c['format'] == 'forge-ordered-v1', 'unsupported certificate format')
    need(c['subject'] == canon(problem), 'certificate is bound to a different problem')
    ns = arr(c['nodes'])
    for ni, n in enumerate(ns):
        need(type(n) is dict, 'invalid derivation node')
        if n.get('kind') == 'bad':
            obj(n, {'state', 'kind', 'target'}, 'bad derivation')
            j = idx(n['target'], len(problem['bad']), 'bad target')
            need(n['state'] == problem['bad'][j], 'bad derivation has the wrong target')
        elif n.get('kind') == 'pred':
            obj(n, {'state', 'kind', 'transition', 'child'}, 'predecessor derivation')
            child = idx(n['child'], ni, 'earlier child')
            ti = idx(n['transition'], len(problem['transitions']), 'transition')
            validate_state(problem, n['state'])
            need(can_cover(problem, problem['transitions'][ti], n['state'], ns[child]['state']),
                 'invalid one-step lower-inclusion witness')
        else:
            raise Reject('unknown derivation tag')
        validate_state(problem, n['state'])
    basis = [ns[idx(i, len(ns), 'basis node')]['state'] for i in arr(c['basis'])]
    keys = [(x['q'], tuple(x['v'])) for x in basis]
    need(keys == sorted(keys), 'noncanonical basis order')
    for i, x in enumerate(basis):
        for j, y in enumerate(basis):
            if i != j:
                need(not below(problem, x, y), 'basis is not an antichain')
    targets = arr(c['target_cover'], len(problem['bad']))
    for b, k in zip(problem['bad'], targets):
        need(below(problem, basis[idx(k, len(basis), 'target covering basis')], b),
             'bad target is not covered')
    expected = {(bi, ti) for bi, b in enumerate(basis)
                for ti, t in enumerate(problem['transitions']) if t['target'] == b['q']}
    seen = set()
    predecessor_count = 0
    direct_rows = 0
    for e in arr(c['closure']):
        obj(e, {'basis', 'transition', 'predecessor', 'cover'}, 'closure row')
        bi = idx(e['basis'], len(basis), 'closure basis')
        ti = idx(e['transition'], len(problem['transitions']), 'closure transition')
        key = (bi, ti)
        need(key in expected and key not in seen, 'duplicate or irrelevant closure row')
        seen.add(key)
        if type(e['predecessor']) is dict and e['predecessor'].get('kind') == 'resource-cover':
            need(e['cover'] == [], 'direct cover does not carry local-minimum indices')
            verify_direct_cover(problem, problem['transitions'][ti], basis[bi], e['predecessor'], basis)
            direct_rows += 1
            continue
        preds = checked_predecessors(problem, problem['transitions'][ti], basis[bi], e['predecessor'])
        predecessor_count += len(preds)
        covers = arr(e['cover'], len(preds))
        for pred, k in zip(preds, covers):
            b = basis[idx(k, len(basis), 'predecessor covering basis')]
            need(below(problem, b, pred), 'predecessor not included in final region')
    need(seen == expected, 'missing transition/basis closure obligations')
    return {'nodes': len(ns), 'basis': len(basis), 'closure_rows': len(seen),
            'predecessors': predecessor_count, 'direct_closure_rows': direct_rows}


def verify_trace(problem: Any, trace: Any, initial: dict | None = None) -> int:
    validate_problem(problem)
    obj(trace, {'format', 'subject', 'initial', 'steps', 'target'}, 'execution trace')
    need(trace['format'] == 'forge-ordered-trace-v1', 'bad trace format')
    need(trace['subject'] == canon(problem), 'trace belongs to another problem')
    if initial is not None:
        need(trace['initial'] == initial, 'trace initial state changed')
    cur = trace['initial']
    validate_state(problem, cur)
    steps = arr(trace['steps'])
    for e in steps:
        if problem['kind'] == 'resource':
            obj(e, {'transition', 'after'}, 'resource trace step')
        else:
            obj(e, {'transition', 'before', 'middle', 'after'}, 'lossy trace step')
        t = problem['transitions'][idx(e['transition'], len(problem['transitions']))]
        after = e['after']
        validate_state(problem, after)
        need(cur['q'] == t['source'] and after['q'] == t['target'], 'trace control mismatch')
        if problem['kind'] == 'resource':
            result = resource_step(t, cur['v'])
            need(result is not None and result == after['v'], 'invalid concrete resource step')
        else:
            validate_words(problem, e['before'])
            validate_words(problem, e['middle'])
            need(all(subseq(e['before'][i], cur['v'][i]) for i in range(problem['channels'])),
                 'pre-action loss invented messages')
            mid = e['before'].copy()
            ch = t['channel']
            if t['op'] == 'send':
                mid[ch] = mid[ch] + t['symbol']
            elif t['op'] == 'recv':
                need(len(mid[ch]) > 0 and mid[ch][0] == t['symbol'], 'receive did not consume head')
                mid[ch] = mid[ch][1:]
            need(e['middle'] == mid, 'wrong reliable channel action')
            need(all(subseq(after['v'][i], mid[i]) for i in range(problem['channels'])),
                 'post-action loss invented messages')
        cur = after
    target = problem['bad'][idx(trace['target'], len(problem['bad']), 'trace target')]
    need(below(problem, target, cur), 'trace does not end in upward bad set')
    return len(steps)


def classify_checked(problem: dict, certificate: dict, initial: dict) -> str:
    verify(problem, certificate)
    validate_state(problem, initial)
    for k in certificate['basis']:
        if below(problem, certificate['nodes'][k]['state'], initial):
            return 'unsafe'
    return 'safe'


def main() -> None:
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('problem')
    parser.add_argument('certificate')
    parser.add_argument('--trace', action='store_true')
    args = parser.parse_args()
    try:
        p, c = load_json(args.problem), load_json(args.certificate)
        info = {'steps': verify_trace(p, c)} if args.trace else verify(p, c)
    except (Reject, RecursionError) as ex:
        parser.exit(1, f'REJECT: {ex}\n')
    print(json.dumps({'accepted_python_check': True, **info}, sort_keys=True))


if __name__ == '__main__':
    main()
