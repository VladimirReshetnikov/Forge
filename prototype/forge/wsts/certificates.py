# PROVENANCE: the acceptance paths of s1, s3 and s4, collected so that the
# checking code is separable from the search code by inspection as well as by
# import. This module imports orders.py and nets.py for the model languages and
# the order; it does not import search.py or summaries.py, and must not.
"""Exact certificate CHECKING for the well-structured-transition-system lanes.

Ordinary Python validation. NOT a verified checker, and NOT a Lean proof.

Each function takes the AUTHORITATIVE problem separately from the certificate
and refuses to proceed unless the certificate is bound to exactly that problem,
field for field. A certificate that carried its own problem statement would be
free to answer an easier question than the one asked.

Two of these run a genuinely different computation from their producers:

  `check_frontier` recomputes every run summary in (need, signed delta)
  coordinates, where the producer composed in (need, give) coordinates.

  `check_backward_closed` recomputes each predecessor from the transition
  data rather than reading the producer's, and searches the basis for a
  dominating element rather than trusting the index it was handed --- the
  index is checked against the recomputation, not used in place of it.

One does not, and says so: `check_direct_cover` replays the producer's
partition tree. It cannot do otherwise; the whole point of that receipt is
that the set it covers is too large to enumerate. What it does check is that
the tree is a genuine partition of the declared box and that every leaf
discharges its own obligation, which is a real check of a real object, just
not an independent recomputation of it.
"""
from __future__ import annotations
from typing import Any, Sequence

from .orders import (Vector, canonical, dickson_leq, higman_leq, natural,
                     predecessor, subsequence)


class InvalidCertificate(ValueError):
    """The certificate is wrong. A mathematical verdict."""


class ResourceRefusal(RuntimeError):
    """A budget was exceeded. An operational refusal, and NOT a verdict."""


MAX_ITEMS = 200_000
MAX_BITS = 4_096
MAX_NODES = 100_000


def fail(message: str) -> None:
    raise InvalidCertificate(message)


def need(condition: bool, message: str) -> None:
    if not condition:
        fail(message)


def same_json(a: Any, b: Any) -> bool:
    """Type-aware structural identity. True is NOT the integer 1 here."""
    if type(a) is not type(b):
        return False
    if type(a) is dict:
        return set(a) == set(b) and all(same_json(a[k], b[k]) for k in a)
    if type(a) is list:
        return len(a) == len(b) and all(same_json(x, y) for x, y in zip(a, b))
    return a == b


def fields(x: Any, keys: set[str], context: str) -> None:
    need(type(x) is dict and set(x) == keys, f'{context}: wrong or unsupported fields')


def nat(x: Any, context: str = 'integer') -> int:
    need(type(x) is int and x >= 0, f'{context}: expected a nonnegative integer, not bool')
    if x.bit_length() > MAX_BITS:
        raise ResourceRefusal(f'{context}: integer exceeds the bit budget')
    return x


def arr(x: Any, context: str, length: int | None = None) -> list:
    need(type(x) is list, f'{context}: expected a list')
    if len(x) > MAX_ITEMS:
        raise ResourceRefusal(f'{context}: too many entries')
    if length is not None:
        need(len(x) == length, f'{context}: wrong length')
    return x


def index(x: Any, bound: int, context: str) -> int:
    need(type(x) is int and 0 <= x < bound, f'{context}: index out of range')
    return x


def vec(x: Any, d: int, context: str = 'vector') -> Vector:
    return tuple(nat(a, context) for a in arr(x, context, d))


# --------------------------------------------------------------------------
# Problem validation, shared by every checker below.
# --------------------------------------------------------------------------
def validate_net(p: Any) -> tuple[int, list[dict], list[Vector]]:
    fields(p, {'kind', 'dimension', 'transitions', 'targets'}, 'problem')
    need(p['kind'] == 'pt-net-coverability',
         'unsupported semantics: expected an ordinary place/transition net')
    d = nat(p['dimension'], 'dimension')
    transitions = arr(p['transitions'], 'transitions')
    names: set[str] = set()
    for t in transitions:
        fields(t, {'name', 'consume', 'produce'}, 'transition')
        need(type(t['name']) is str, 'transition name must be a string')
        need(t['name'] not in names, 'duplicate transition name')
        names.add(t['name'])
        vec(t['consume'], d, 'consume')
        vec(t['produce'], d, 'produce')
    targets = [vec(b, d, 'target') for b in arr(p['targets'], 'targets')]
    return d, transitions, targets


# --------------------------------------------------------------------------
# s1: run summaries, recomputed in the other coordinate system.
# --------------------------------------------------------------------------
def check_runs(problem: dict, nodes: Any) -> list[tuple[Vector, tuple[int, ...], int]]:
    """Recompute every node as (need, signed delta, length).

    The producer composed (need, give). Here a sequence's need is
    max(left.need, right.need - left.delta) and its delta is the sum, which is
    a visibly different recurrence for the same quantity. A repetition's need
    grows by the per-iteration shortfall max(0, -delta), so a repeat count of
    10**18 costs one multiplication and the certificate stays small.

    Children are required to have strictly lower indices, so the DAG cannot be
    cyclic and this single forward pass is total.
    """
    d, transitions, _ = validate_net(problem)
    nodes = arr(nodes, 'runs')
    if len(nodes) > MAX_NODES:
        raise ResourceRefusal('run DAG node budget')
    need(bool(nodes), 'empty run DAG')
    out: list[tuple[Vector, tuple[int, ...], int]] = []
    for number, node in enumerate(nodes):
        need(type(node) is dict and type(node.get('op')) is str, 'missing run opcode')
        op = node['op']
        if op == 'empty':
            fields(node, {'op'}, 'empty node')
            required, delta, length = (0,) * d, (0,) * d, 0
        elif op == 'step':
            fields(node, {'op', 'transition'}, 'step node')
            t = transitions[index(node['transition'], len(transitions), 'transition')]
            required = tuple(t['consume'])
            delta = tuple(t['produce'][i] - t['consume'][i] for i in range(d))
            length = 1
        elif op == 'seq':
            fields(node, {'op', 'left', 'right'}, 'sequence node')
            r, e, n = out[index(node['left'], number, 'left reference')]
            s, f, m = out[index(node['right'], number, 'right reference')]
            required = tuple(max(r[i], s[i] - e[i]) for i in range(d))
            delta = tuple(e[i] + f[i] for i in range(d))
            length = n + m
        elif op == 'repeat':
            fields(node, {'op', 'body', 'count'}, 'repeat node')
            r, e, n = out[index(node['body'], number, 'body reference')]
            count = nat(node['count'], 'repeat count')
            if count == 0:
                required, delta, length = (0,) * d, (0,) * d, 0
            else:
                required = tuple(r[i] + (count - 1) * max(0, -e[i]) for i in range(d))
                delta = tuple(count * e[i] for i in range(d))
                length = count * n
        else:
            fail('unknown run opcode')
        need(all(x >= 0 for x in required), 'negative resource requirement')
        need(all(required[i] + delta[i] >= 0 for i in range(d)),
             'run summary leaves a negative marking')
        if any(abs(x).bit_length() > MAX_BITS * 4 for x in (*required, *delta, length)):
            raise ResourceRefusal('intermediate summary exceeds the bit budget')
        out.append((required, delta, length))
    return out


def check_frontier(expected_problem: dict, certificate: Any) -> dict:
    """Verify a minimal coverability frontier: the answer for EVERY marking.

    Four obligations, and dropping any one of them leaves a different claim:

      minimality      the basis is sorted and pairwise incomparable, so it
                      really is the frontier and not merely some superset
      soundness       each basis element has a run covering an original target
      completeness    each original target dominates some basis element
      closure         each basis element's predecessors are all dominated

    The last is the only inductive one. Together with completeness it gives
    that the upward closure of the basis contains every marking from which a
    target is coverable, and soundness gives the converse.
    """
    d, transitions, targets = validate_net(expected_problem)
    fields(certificate, {'schema', 'problem', 'basis', 'runs', 'target_cover',
                         'predecessor_cover'}, 'frontier certificate')
    need(certificate['schema'] == 'forge.wsts.frontier.v1', 'wrong frontier schema')
    validate_net(certificate['problem'])
    need(same_json(certificate['problem'], expected_problem),
         'certificate is not bound to the exact supplied problem')

    entries = arr(certificate['basis'], 'basis')
    markings: list[Vector] = []
    for entry in entries:
        fields(entry, {'marking', 'run', 'target'}, 'basis entry')
        markings.append(vec(entry['marking'], d, 'basis marking'))
    need(canonical(markings, dickson_leq),
         'basis is not a canonical antichain: unsorted, duplicated or dominated')

    runs = check_runs(expected_problem, certificate['runs'])
    for entry, marking in zip(entries, markings):
        required, delta, _ = runs[index(entry['run'], len(runs), 'basis run')]
        target = targets[index(entry['target'], len(targets), 'basis target')]
        need(dickson_leq(required, marking),
             'basis witness is not enabled at its own marking')
        end = tuple(marking[i] + delta[i] for i in range(d))
        need(dickson_leq(target, end),
             'basis witness does not cover the target it claims')

    cover = arr(certificate['target_cover'], 'target cover', len(targets))
    for target, i in zip(targets, cover):
        need(dickson_leq(markings[index(i, len(markings), 'target cover')], target),
             'an original target is not covered by the basis')

    rows = arr(certificate['predecessor_cover'], 'predecessor cover', len(markings))
    for b, row in zip(markings, rows):
        arr(row, 'predecessor row', len(transitions))
        for t, i in zip(transitions, row):
            # Recomputed here from the transition, not read from the producer.
            earlier = predecessor(tuple(t['consume']), tuple(t['produce']), b)
            a = markings[index(i, len(markings), 'predecessor cover')]
            need(dickson_leq(a, earlier), 'basis is not backward closed')

    return {'status': 'PYTHON_CHECKED',
            'meaning': 'exact minimal coverability frontier over all initial markings',
            'basis': [list(b) for b in markings],
            'run_nodes': len(runs),
            'longest_witness': max([0] + [runs[e['run']][2] for e in entries])}


def check_threshold(expected_query: dict, certificate: Any) -> dict:
    """Verify the least n with base + n*slope unsafe, or that none exists.

    Each basis threshold is checked by two evaluations --- feasible at n, and
    not feasible at n-1 --- rather than by recomputing a ceiling division. A
    ceiling division here would be the producer's own algorithm run twice.
    """
    fields(expected_query, {'problem', 'slope', 'offset'}, 'threshold query')
    d, _, _ = validate_net(expected_query['problem'])
    slope = vec(expected_query['slope'], d, 'slope')
    offset = vec(expected_query['offset'], d, 'offset')
    fields(certificate, {'schema', 'query', 'frontier', 'basis_thresholds', 'threshold'},
           'threshold certificate')
    need(certificate['schema'] == 'forge.wsts.threshold.v1', 'wrong threshold schema')
    need(same_json(certificate['query'], expected_query), 'threshold query mismatch')

    checked = check_frontier(expected_query['problem'], certificate['frontier'])
    basis = checked['basis']
    supplied = arr(certificate['basis_thresholds'], 'basis thresholds', len(basis))
    recomputed: list[int | None] = []
    for b, claim in zip(basis, supplied):
        unreachable = any(slope[i] == 0 and offset[i] < b[i] for i in range(d))
        if unreachable:
            need(claim is None, 'an unreachable basis element has a finite threshold')
            recomputed.append(None)
            continue
        n = nat(claim, 'basis threshold')
        need(all(offset[i] + n * slope[i] >= b[i] for i in range(d)),
             'basis threshold is not feasible')
        need(not (n > 0 and all(offset[i] + (n - 1) * slope[i] >= b[i] for i in range(d))),
             'basis threshold is not least')
        recomputed.append(n)
    finite = [n for n in recomputed if n is not None]
    expected = min(finite) if finite else None
    if certificate['threshold'] is not None:
        nat(certificate['threshold'], 'global threshold')
    need(certificate['threshold'] == expected, 'global threshold mismatch')
    return {'status': 'PYTHON_CHECKED', 'meaning': 'least unsafe natural parameter',
            'threshold': expected, 'all_safe': expected is None}


# --------------------------------------------------------------------------
# s3: a safety basis for a counter system, and an unsafety counterexample.
# --------------------------------------------------------------------------
def validate_vass(p: Any) -> tuple[int, int, list[dict]]:
    fields(p, {'kind', 'controls', 'dimension', 'transitions', 'bad', 'initials'},
           'counter system')
    need(p['kind'] == 'vass-coverability', 'unsupported counter-system semantics')
    controls = nat(p['controls'], 'controls')
    need(controls >= 1, 'at least one control state is required')
    d = nat(p['dimension'], 'dimension')
    for t in arr(p['transitions'], 'transitions'):
        fields(t, {'src', 'dst', 'consume', 'produce'}, 'transition')
        index(t['src'], controls, 'source control')
        index(t['dst'], controls, 'target control')
        vec(t['consume'], d, 'consume')
        vec(t['produce'], d, 'produce')
    for b in arr(p['bad'], 'bad states'):
        fields(b, {'control', 'vector'}, 'bad state')
        index(b['control'], controls, 'bad control')
        vec(b['vector'], d, 'bad vector')
    for f in arr(p['initials'], 'initial families'):
        fields(f, {'control', 'base', 'rays'}, 'initial family')
        index(f['control'], controls, 'initial control')
        vec(f['base'], d, 'base')
        for ray in arr(f['rays'], 'rays'):
            vec(ray, d, 'ray')
    return controls, d, p['transitions']


def check_backward_closed(expected_problem: dict, certificate: Any) -> dict:
    """Verify a safety certificate: a backward-closed basis missing every start.

    The basis is per control state. Three obligations:

      it contains every bad state;
      it is closed under predecessors, recomputed here from the transitions;
      no initial configuration --- for ANY choice of ray parameters --- lies
      in its upward closure.

    The third is the one that needs an argument rather than an evaluation. A
    basis element b is unreachable from the family base + sum n_j ray_j
    exactly when some coordinate i has b[i] > base[i] and every ray zero at i:
    no choice of parameters can raise that coordinate. Checking one large n
    would not establish it, because the family is infinite.
    """
    controls, d, transitions = validate_vass(expected_problem)
    fields(certificate, {'schema', 'problem', 'basis'}, 'safety certificate')
    need(certificate['schema'] == 'forge.wsts.safe.v1', 'wrong safety schema')
    need(same_json(certificate['problem'], expected_problem),
         'certificate is not bound to the exact supplied problem')

    groups = arr(certificate['basis'], 'basis', controls)
    basis = [[vec(v, d, 'basis vector') for v in arr(g, 'basis group')] for g in groups]
    for q, group in enumerate(basis):
        need(canonical(group, dickson_leq), f'basis for control {q} is not canonical')

    def dominated(control: int, value: Vector) -> bool:
        return any(dickson_leq(b, value) for b in basis[control])

    for b in expected_problem['bad']:
        need(dominated(b['control'], tuple(b['vector'])),
             'a bad state is outside the claimed backward-closed set')

    for t in transitions:
        for b in basis[t['dst']]:
            earlier = predecessor(tuple(t['consume']), tuple(t['produce']), b)
            need(dominated(t['src'], earlier),
                 'basis is not closed under predecessors')

    for f in expected_problem['initials']:
        base = tuple(f['base'])
        rays = [tuple(r) for r in f['rays']]
        for b in basis[f['control']]:
            blocked = any(b[i] > base[i] and all(ray[i] == 0 for ray in rays)
                          for i in range(d))
            need(blocked, 'an initial family can reach the claimed-unsafe region')

    return {'status': 'PYTHON_CHECKED',
            'meaning': 'backward-closed basis separating the initial set from the bad set',
            'basis_size': sum(len(g) for g in basis)}


def check_counterexample(expected_problem: dict, certificate: Any) -> dict:
    """Replay a claimed unsafe run in the ORIGINAL transition relation.

    No antichain, no order, no search: rebuild the exact initial configuration
    from the named parameters, fire the listed transitions one at a time, and
    require the result to cover a declared bad state. A refutation that cannot
    survive this is not a refutation.
    """
    controls, d, transitions = validate_vass(expected_problem)
    fields(certificate, {'schema', 'problem', 'initial', 'parameters', 'transitions'},
           'counterexample certificate')
    need(certificate['schema'] == 'forge.wsts.unsafe.v1', 'wrong counterexample schema')
    need(same_json(certificate['problem'], expected_problem),
         'certificate is not bound to the exact supplied problem')
    families = expected_problem['initials']
    family = families[index(certificate['initial'], len(families), 'initial family')]
    rays = [tuple(r) for r in family['rays']]
    parameters = [nat(n, 'ray parameter') for n in
                  arr(certificate['parameters'], 'parameters', len(rays))]
    state = tuple(family['base'][i] + sum(n * ray[i] for n, ray in zip(parameters, rays))
                  for i in range(d))
    control = family['control']
    steps = arr(certificate['transitions'], 'transition sequence')
    for step in steps:
        t = transitions[index(step, len(transitions), 'transition')]
        need(t['src'] == control, 'transition is not enabled at this control state')
        need(dickson_leq(tuple(t['consume']), state),
             'transition is not enabled at this marking')
        state = tuple(state[i] - t['consume'][i] + t['produce'][i] for i in range(d))
        control = t['dst']
    for b in expected_problem['bad']:
        if b['control'] == control and dickson_leq(tuple(b['vector']), state):
            return {'status': 'PYTHON_CHECKED', 'meaning': 'executable unsafe run',
                    'length': len(steps), 'final': list(state)}
    fail('the replayed run does not reach any declared bad state')
    raise AssertionError('unreachable')


# --------------------------------------------------------------------------
# s4: the direct-cover receipt, which avoids materialising the minima.
# --------------------------------------------------------------------------
def check_direct_cover(matrix: Sequence[Sequence[int]], consume: Sequence[int],
                       produce: Sequence[int], target: Sequence[int],
                       basis: Sequence[Sequence[int]], receipt: Any) -> dict:
    """Verify that EVERY predecessor is dominated, without listing any of them.

    The obligation is: for all z >= 0 with A z >= demand, some basis element
    is below consume + z. The receipt is a binary partition of the box
    [0, caps] whose leaves each discharge it one of two ways --- a sub-box
    whose corner is already covered by a named basis element, or a sub-box
    whose maximum still fails a row of A z >= demand and therefore contains no
    predecessor at all.

    s4 reports a case with 26,075,972,546 minimal predecessors and a receipt of
    a few hundred nodes. Enumerating them to check it is not an option, so this
    checker replays the producer's tree rather than recomputing the set. What
    it verifies independently is that the tree is a genuine partition --- every
    split lies inside its parent's box and the two children tile it exactly ---
    and that each leaf's own claim holds. A tree that skipped a region would
    have to do so by an arithmetic error the partition check catches.

    `caps` is checked, not trusted: a surplus above it cannot be minimal
    because a single row already has enough from that coordinate alone.
    """
    d = len(target)
    fields(receipt, {'kind', 'caps', 'tree'}, 'direct cover receipt')
    need(receipt['kind'] == 'direct-cover', 'wrong receipt kind')
    caps = [nat(c, 'cap') for c in arr(receipt['caps'], 'caps', d)]
    demand = [max(0, target[j] - produce[j]) for j in range(d)]
    for i in range(d):
        for j in range(d):
            if matrix[j][i] > 0:
                need(matrix[j][i] * caps[i] >= demand[j], 'clipping bound is too small')

    covered_volume = 0
    total_volume = 1
    for c in caps:
        total_volume *= c + 1
    pending = [(receipt['tree'], [0] * d, list(caps))]
    visited = 0
    while pending:
        node, low, high = pending.pop()
        visited += 1
        if visited > MAX_ITEMS:
            raise ResourceRefusal('partition tree exceeds the node budget')
        arr(node, 'partition node')
        need(bool(node) and type(node[0]) is str, 'malformed partition node')
        volume = 1
        for i in range(d):
            volume *= high[i] - low[i] + 1
        if node[0] == 'basis':
            need(len(node) == 2, 'basis leaf arity')
            b = basis[index(node[1], len(basis), 'basis reference')]
            need(all(b[i] <= consume[i] + low[i] for i in range(d)),
                 'sub-box is not covered by the named basis element')
            covered_volume += volume
        elif node[0] == 'impossible':
            need(len(node) == 2, 'impossible leaf arity')
            j = index(node[1], d, 'infeasible row')
            need(sum(matrix[j][i] * high[i] for i in range(d)) < demand[j],
                 'sub-box declared impossible but its maximum satisfies the row')
            covered_volume += volume
        elif node[0] == 'split':
            need(len(node) == 5, 'split arity')
            i = index(node[1], d, 'split coordinate')
            k = nat(node[2], 'split point')
            need(low[i] <= k < high[i], 'split point lies outside its own box')
            left_high, right_low = list(high), list(low)
            left_high[i], right_low[i] = k, k + 1
            pending.append((node[3], list(low), left_high))
            pending.append((node[4], right_low, list(high)))
        else:
            fail('unknown partition node tag')
    need(covered_volume == total_volume,
         'the partition does not tile the declared box exactly')
    return {'status': 'PYTHON_CHECKED',
            'meaning': 'every predecessor in the clipping box is dominated',
            'nodes': visited, 'box_volume': total_volume}


# --------------------------------------------------------------------------
# s4: lossy channels, where the order IS the loss.
# --------------------------------------------------------------------------
def check_lossy_closed(controls: int, alphabet: Sequence[str],
                       transitions: Sequence[dict], bad: Sequence[dict],
                       basis: Sequence[Sequence[Sequence[str]]]) -> dict:
    """Verify a backward-closed basis of channel configurations.

    Nothing here mentions message loss. It does not have to: a set upward-closed
    under the subsequence order already contains every lossy variant of every
    member, so an ordinary predecessor closure over that order is a closure
    under lossy steps. The same loop, a different order.
    """
    channels = len(basis[0][0]) if basis and basis[0] else 0
    groups = [[tuple(w) for w in arr(g, 'basis group')] for g in basis]
    need(len(groups) == controls, 'basis must cover every control state')
    for q, group in enumerate(groups):
        for words in group:
            need(len(words) == channels, 'channel count mismatch')
            for w in words:
                need(type(w) is str and all(a in alphabet for a in w),
                     'word contains a symbol outside the alphabet')
        need(canonical(group, higman_leq), f'basis for control {q} is not canonical')

    def dominated(control: int, words: tuple[str, ...]) -> bool:
        return any(higman_leq(b, words) for b in groups[control])

    for b in bad:
        need(dominated(b['control'], tuple(b['words'])),
             'a bad configuration is outside the claimed backward-closed set')

    for t in transitions:
        for words in groups[t['dst']]:
            out = list(words)
            channel, symbol = t['channel'], t['symbol']
            if t['op'] == 'send':
                current = words[channel]
                if current and current[-1] == symbol:
                    out[channel] = current[:-1]
            elif t['op'] == 'recv':
                out[channel] = symbol + words[channel]
            need(dominated(t['src'], tuple(out)),
                 'basis is not closed under channel predecessors')

    return {'status': 'PYTHON_CHECKED',
            'meaning': 'backward-closed basis under the subsequence order',
            'basis_size': sum(len(g) for g in groups)}
