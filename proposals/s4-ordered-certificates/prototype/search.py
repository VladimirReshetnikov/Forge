"""Untrusted exact backward-basis producer. Python standard library only.

Two input languages: guarded nonnegative-affine resource transitions and
finite-control lossy FIFO channels. No Lean proof is produced by this module.
The separately implemented checker.py must check every successful result.
"""
from __future__ import annotations
import itertools
import json
from collections import deque
from dataclasses import dataclass
from typing import Any


class Exhausted(Exception):
    """Operational cutoff; it is not a negative mathematical answer."""


@dataclass
class Budget:
    max_nodes: int = 20000
    max_expansions: int = 50000
    max_grid: int = 200000
    max_box_nodes: int = 1000000
    expansions: int = 0
    grid_points: int = 0
    box_nodes: int = 0
    pred_calls: int = 0

    def stats(self) -> dict[str, int]:
        return {k: getattr(self, k) for k in
                ('expansions', 'grid_points', 'box_nodes', 'pred_calls')}


def canonical(obj: Any) -> str:
    return json.dumps(obj, sort_keys=True, separators=(',', ':'), ensure_ascii=True,
                      allow_nan=False)


def subword(a: str, b: str) -> bool:
    """Producer's greedy subsequence test."""
    it = iter(b)
    return all(any(x == y for y in it) for x in a)


def leq(problem: dict, x: tuple, y: tuple) -> bool:
    if x[0] != y[0]:
        return False
    if problem['kind'] == 'resource':
        return all(a <= b for a, b in zip(x[1], y[1]))
    return all(subword(a, b) for a, b in zip(x[1], y[1]))


def state(obj: dict) -> tuple:
    return (obj['q'], tuple(obj['v']))


def state_json(x: tuple) -> dict:
    return {'q': x[0], 'v': list(x[1])}


def mv(A: list[list[int]], x: tuple | list) -> list[int]:
    return [sum(a * b for a, b in zip(row, x)) for row in A]


def forward_resource(t: dict, x: tuple | list) -> tuple[int, ...] | None:
    a = t['consume']
    if any(xi < ai for xi, ai in zip(x, a)):
        return None
    z = [xi - ai for xi, ai in zip(x, a)]
    return tuple(y + b for y, b in zip(mv(t['matrix'], z), t['produce']))


def pareto(vectors: list[tuple[int, ...]]) -> list[tuple[int, ...]]:
    out: list[tuple[int, ...]] = []
    for x in vectors:
        if any(all(bi <= xi for bi, xi in zip(b, x)) for b in out):
            continue
        out = [b for b in out if not all(xi <= bi for xi, bi in zip(x, b))]
        out.append(x)
    return sorted(out)


def box_tree(A: list[list[int]], r: list[int], mins: list[tuple[int, ...]],
             L: tuple[int, ...], U: tuple[int, ...], budget: Budget) -> list:
    budget.box_nodes += 1
    if budget.box_nodes > budget.max_box_nodes:
        raise Exhausted('box-certificate node budget exhausted')
    for k, p in enumerate(mins):
        if all(pi <= li for pi, li in zip(p, L)):
            return ['covered', k]
    upper = mv(A, U)
    for j, (uj, rj) in enumerate(zip(upper, r)):
        if uj < rj:
            return ['impossible', j]
    spans = [hi - lo for lo, hi in zip(L, U)]
    i = max(range(len(spans)), key=spans.__getitem__)
    if spans[i] == 0:
        raise AssertionError('feasible singleton omitted by proposed Pareto basis')
    cut = (L[i] + U[i]) // 2
    left_u = list(U)
    left_u[i] = cut
    right_l = list(L)
    right_l[i] = cut + 1
    return ['split', i, cut,
            box_tree(A, r, mins, L, tuple(left_u), budget),
            box_tree(A, r, mins, tuple(right_l), U, budget)]


def resource_pre(t: dict, target: tuple[int, ...], budget: Budget,
                 receipt: bool = True) -> tuple[list[tuple[int, ...]], dict]:
    """Exact minimal predecessors; diagonal shortcut or integer-box coverage."""
    budget.pred_calls += 1
    A, a, b = t['matrix'], t['consume'], t['produce']
    d = len(a)
    r = [max(0, u - v) for u, v in zip(target, b)]
    if all(A[i][j] == 0 for i in range(d) for j in range(d) if i != j):
        z = []
        for i in range(d):
            if A[i][i] == 0:
                if r[i]:
                    return [], {'kind': 'diagonal'}
                z.append(0)
            else:
                z.append((r[i] + A[i][i] - 1) // A[i][i])
        return [tuple(ai + zi for ai, zi in zip(a, z))], {'kind': 'diagonal'}
    caps = [max(((r[j] + A[j][i] - 1) // A[j][i]
                  for j in range(d) if A[j][i] > 0), default=0)
            for i in range(d)]
    count = 1
    for c in caps:
        count *= c + 1
        if count > budget.max_grid:
            raise Exhausted(f'local predecessor grid exceeds {budget.max_grid} points')
    feasible = []
    for z in itertools.product(*(range(c + 1) for c in caps)):
        budget.grid_points += 1
        if all(x >= y for x, y in zip(mv(A, z), r)):
            feasible.append(z)
    mins = pareto(feasible)
    preds = [tuple(ai + zi for ai, zi in zip(a, z)) for z in mins]
    if not receipt:
        return preds, {}
    tree = box_tree(A, r, mins, (0,) * d, tuple(caps), budget)
    return preds, {'kind': 'box', 'caps': caps, 'minima': [list(z) for z in mins],
                   'tree': tree}


def channel_pre(t: dict, target: tuple[str, ...], budget: Budget) -> tuple[list, dict]:
    budget.pred_calls += 1
    words = list(target)
    c, a = t['channel'], t['symbol']
    if t['op'] == 'send':
        if words[c].endswith(a):
            words[c] = words[c][:-1]
    elif t['op'] == 'recv':
        words[c] = a + words[c]
    return [tuple(words)], {'kind': 'lossy-word'}


def predecessors(problem: dict, t: dict, target: tuple, budget: Budget,
                 receipt: bool = True) -> tuple[list[tuple], dict]:
    if problem['kind'] == 'resource':
        preds, cert = resource_pre(t, target, budget, receipt)
    else:
        preds, cert = channel_pre(t, target, budget)
    return [(t['source'], p) for p in preds], cert


def solve(problem: dict, budget: Budget | None = None) -> dict:
    """Return a full exact-region certificate or an explicitly inconclusive result.

    Call checker.validate_problem before this entry point for untrusted inputs.
    This producer is intentionally not an input-security boundary.
    """
    budget = budget or Budget()
    nodes: list[dict] = []
    active: set[int] = set()
    work: deque[int] = deque()

    def key(n: int) -> tuple:
        return state(nodes[n]['state'])

    def admit(s: tuple, reason: dict) -> int | None:
        if any(leq(problem, key(i), s) for i in active):
            return None
        if len(nodes) >= budget.max_nodes:
            raise Exhausted('derivation node budget exhausted')
        remove = [i for i in active if leq(problem, s, key(i))]
        for i in remove:
            active.remove(i)
        idx = len(nodes)
        nodes.append({'state': state_json(s), **reason})
        active.add(idx)
        work.append(idx)
        return idx

    try:
        for j, b in enumerate(problem['bad']):
            admit(state(b), {'kind': 'bad', 'target': j})
        while work:
            n = work.popleft()
            if n not in active:
                continue
            budget.expansions += 1
            if budget.expansions > budget.max_expansions:
                raise Exhausted('backward expansion budget exhausted')
            s = key(n)
            for ti, t in enumerate(problem['transitions']):
                if t['target'] != s[0]:
                    continue
                preds, _ = predecessors(problem, t, s[1], budget, receipt=False)
                for p in preds:
                    admit(p, {'kind': 'pred', 'transition': ti, 'child': n})
        basis = sorted(active, key=key)
        target_cover = []
        for b in problem['bad']:
            target_cover.append(next(i for i, n in enumerate(basis)
                                     if leq(problem, key(n), state(b))))
        closure = []
        for bi, n in enumerate(basis):
            s = key(n)
            for ti, t in enumerate(problem['transitions']):
                if t['target'] != s[0]:
                    continue
                preds, rec = predecessors(problem, t, s[1], budget, receipt=True)
                cover = [next(i for i, k in enumerate(basis)
                              if leq(problem, key(k), p)) for p in preds]
                closure.append({'basis': bi, 'transition': ti,
                                'predecessor': rec, 'cover': cover})
        cert = {'format': 'forge-ordered-v1', 'subject': canonical(problem),
                'nodes': nodes, 'basis': basis, 'target_cover': target_cover,
                'closure': closure}
        return {'status': 'complete', 'certificate': cert,
                'stats': {**budget.stats(), 'nodes': len(nodes), 'basis': len(basis)}}
    except Exhausted as ex:
        return {'status': 'unknown', 'reason': str(ex),
                'stats': {**budget.stats(), 'nodes': len(nodes), 'basis': len(active)}}


def classify(problem: dict, certificate: dict, initial: dict) -> str:
    """Use only after independent verification of the certificate."""
    s = state(initial)
    return ('unsafe' if any(leq(problem, state(certificate['nodes'][n]['state']), s)
                            for n in certificate['basis']) else 'safe')


def witness(problem: dict, certificate: dict, initial: dict) -> dict | None:
    """Extract a concrete, independently replayable finite bad execution."""
    current = state(initial)
    ns = certificate['nodes']
    n = next((n for n in certificate['basis']
              if leq(problem, state(ns[n]['state']), current)), None)
    if n is None:
        return None
    steps = []
    while ns[n]['kind'] == 'pred':
        ti, child = ns[n]['transition'], ns[n]['child']
        t = problem['transitions'][ti]
        dst = state(ns[child]['state'])
        if problem['kind'] == 'resource':
            v = forward_resource(t, current[1])
            if v is None:
                raise AssertionError('invalid certificate supplied to witness extractor')
            after = (t['target'], v)
            steps.append({'transition': ti, 'after': state_json(after)})
        else:
            before = list(dst[1])
            c, a = t['channel'], t['symbol']
            if t['op'] == 'send':
                before = list(current[1])
                mid = before.copy()
                mid[c] += a
            elif t['op'] == 'recv':
                before[c] = a + before[c]
                mid = before.copy()
                mid[c] = mid[c][1:]
            else:
                mid = before.copy()
            after = dst
            steps.append({'transition': ti, 'before': before, 'middle': mid,
                          'after': state_json(after)})
        current = after
        n = child
    return {'format': 'forge-ordered-trace-v1', 'subject': canonical(problem),
            'initial': initial, 'steps': steps, 'target': ns[n]['target']}


def closure_probe(problem: dict, t: dict, target: tuple[int, ...],
                  basis: list[tuple], budget: Budget) -> tuple[tuple | None, dict | None]:
    """Find one uncovered predecessor OR certify complete coverage by global basis.

    No grid enumeration or local Pareto basis is needed. The returned witness
    is a genuine predecessor, not necessarily a minimal one. A complete tree
    has leaves referring directly to the current/final global basis indices.
    """
    budget.pred_calls += 1
    A, a, b = t['matrix'], t['consume'], t['produce']
    d = len(a)
    r = [max(0, u-v) for u,v in zip(target,b)]
    caps = [max(((r[j]+A[j][i]-1)//A[j][i] for j in range(d) if A[j][i]>0),default=0)
            for i in range(d)]
    class Found(Exception):
        def __init__(self, point): self.point=point
    def tree(L,U):
        budget.box_nodes+=1
        if budget.box_nodes>budget.max_box_nodes:
            raise Exhausted('direct closure partition budget exhausted')
        for k,(q,v) in enumerate(basis):
            if q==t['source'] and all(v[i]<=a[i]+L[i] for i in range(d)):
                return ['basis',k]
        upper=mv(A,U)
        for j in range(d):
            if upper[j]<r[j]: return ['impossible',j]
        if all(x>=y for x,y in zip(mv(A,L),r)):
            raise Found(tuple(a[i]+L[i] for i in range(d)))
        spans=[U[i]-L[i] for i in range(d)]
        i=max(range(d),key=spans.__getitem__)
        if spans[i]==0: raise AssertionError('singleton should have been decided')
        cut=(L[i]+U[i])//2
        lU=list(U);lU[i]=cut
        rL=list(L);rL[i]=cut+1
        return ['split',i,cut,tree(L,tuple(lU)),tree(tuple(rL),U)]
    try:
        result=tree((0,)*d,tuple(caps))
        return None,{'kind':'resource-cover','caps':caps,'tree':result}
    except Found as f:
        return (t['source'],f.point),None


def solve_separation(problem: dict, budget: Budget | None = None) -> dict:
    """Antichain-aware closure separation, with the same final-region semantics.

    This second producer uses direct partition receipts for nondiagonal resource
    maps, and the original cheap exact rules for diagonal maps and lossy words.
    """
    budget=budget or Budget()
    nodes=[];active=set();work=deque()
    def key(n):return state(nodes[n]['state'])
    def admit(s,reason):
        if any(leq(problem,key(i),s) for i in active):return None
        if len(nodes)>=budget.max_nodes:raise Exhausted('derivation node budget exhausted')
        active.difference_update([i for i in active if leq(problem,s,key(i))])
        n=len(nodes);nodes.append({'state':state_json(s),**reason});active.add(n);work.append(n)
        return n
    def dense(t):
        return problem['kind']=='resource' and any(t['matrix'][i][j]!=0
            for i in range(problem['dimension']) for j in range(problem['dimension']) if i!=j)
    try:
        for i,b in enumerate(problem['bad']):admit(state(b),{'kind':'bad','target':i})
        while work:
            n=work.popleft()
            if n not in active:continue
            budget.expansions+=1
            if budget.expansions>budget.max_expansions:raise Exhausted('expansion budget exhausted')
            s=key(n)
            for ti,t in enumerate(problem['transitions']):
                if n not in active:break
                if t['target']!=s[0]:continue
                if dense(t):
                    while n in active:
                        p,_=closure_probe(problem,t,s[1],[key(i) for i in sorted(active,key=key)],budget)
                        if p is None:break
                        admit(p,{'kind':'pred','transition':ti,'child':n})
                else:
                    ps,_=predecessors(problem,t,s[1],budget,receipt=False)
                    for p in ps:admit(p,{'kind':'pred','transition':ti,'child':n})
        basis=sorted(active,key=key)
        covers=[next(i for i,n in enumerate(basis) if leq(problem,key(n),state(b)))
                for b in problem['bad']]
        closure=[]
        for bi,n in enumerate(basis):
            s=key(n)
            for ti,t in enumerate(problem['transitions']):
                if t['target']!=s[0]:continue
                if dense(t):
                    p,rec=closure_probe(problem,t,s[1],[key(i) for i in basis],budget)
                    if p is not None:raise AssertionError('uncovered predecessor after saturation')
                    cover=[]
                else:
                    ps,rec=predecessors(problem,t,s[1],budget,receipt=True)
                    cover=[next(i for i,k in enumerate(basis) if leq(problem,key(k),p)) for p in ps]
                closure.append({'basis':bi,'transition':ti,'predecessor':rec,'cover':cover})
        cert={'format':'forge-ordered-v1','subject':canonical(problem),'nodes':nodes,
              'basis':basis,'target_cover':covers,'closure':closure}
        return {'status':'complete','certificate':cert,
                'stats':{**budget.stats(),'nodes':len(nodes),'basis':len(basis)}}
    except (Exhausted,RecursionError) as ex:
        return {'status':'unknown','reason':str(ex) or 'recursive partition depth exhausted',
                'stats':{**budget.stats(),'nodes':len(nodes),'basis':len(active)}}
