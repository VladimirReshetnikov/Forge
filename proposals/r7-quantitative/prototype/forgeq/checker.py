"""Search-free, exact certificate replay for the explicitly defined fragments.

Imports no producer or optimization module. This is tested research code, NOT
formally verified and NOT a Lean-kernel checker. Its limits are defensive
bounds, not a claim of comprehensive hostile-input hardening.
"""
from __future__ import annotations
from fractions import Fraction
import json
import re
from typing import Any

MAX_STATES = 48
MAX_BITS = 4096
MAX_DEGREE = 12
MAX_BYTES = 32_000_000
RATIONAL = re.compile(r'-?(?:0|[1-9][0-9]*)(?:/[1-9][0-9]*)?\Z')


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def fields(x: Any, keys: set[str]) -> None:
    require(type(x) is dict and set(x) == keys, 'unexpected or missing fields')


def number(x: Any) -> Fraction:
    require(type(x) in (int, str), 'only integer or canonical rational string allowed')
    if type(x) is str:
        require(len(x) <= 2500 and bool(RATIONAL.fullmatch(x)), 'invalid rational syntax')
    z = Fraction(x)
    require(z.numerator.bit_length() <= MAX_BITS and z.denominator.bit_length() <= MAX_BITS,
            'rational bit budget')
    if type(x) is str:
        require(str(z) == x, 'noncanonical rational')
    return z


def vector(x: Any, n: int | None = None) -> list[Fraction]:
    require(type(x) is list and len(x) <= MAX_STATES, 'invalid vector')
    if n is not None:
        require(len(x) == n, 'vector dimension')
    return [number(z) for z in x]


def matrix(x: Any, n: int, m: int) -> list[list[Fraction]]:
    require(type(x) is list and len(x) == n, 'matrix row dimension')
    return [vector(row, m) for row in x]


def indices(x: Any, n: int) -> set[int]:
    require(type(x) is list and len(x) <= n, 'invalid index set')
    require(all(type(i) is int and 0 <= i < n for i in x), 'index out of bounds')
    require(len(set(x)) == len(x), 'duplicate index')
    return set(x)


def pair(x: Any, n: int, m: int) -> tuple[int, int]:
    require(type(x) is list and len(x) == 2, 'invalid pair')
    require(type(x[0]) is int and 0 <= x[0] < n and
            type(x[1]) is int and 0 <= x[1] < m, 'pair index bounds')
    return x[0], x[1]


def relation(x: Any, n: int, m: int) -> set[tuple[int, int]]:
    require(type(x) is list and len(x) <= n*m, 'invalid relation')
    ans = [pair(p, n, m) for p in x]
    require(len(set(ans)) == len(ans), 'duplicate pair')
    return set(ans)


def law(x: Any, n: int | None = None) -> list[Fraction]:
    v = vector(x, n)
    require(bool(v) and all(z >= 0 for z in v) and sum(v) == 1, 'not a probability law')
    return v


def chain(x: Any) -> list[list[Fraction]]:
    require(type(x) is list and 0 < len(x) <= MAX_STATES, 'invalid state count')
    return [law(row, len(x)) for row in x]


def mdp(p: dict):
    fields(p, {'actions', 'target'})
    require(type(p['actions']) is list and 0 < len(p['actions']) <= MAX_STATES,
            'invalid MDP state count')
    n = len(p['actions'])
    target = indices(p['target'], n)
    actions = []
    for s, choices in enumerate(p['actions']):
        require(type(choices) is list and 0 < len(choices) <= 16, 'invalid action set')
        rows = [law(row, n) for row in choices]
        if s in target:
            require(all(row[s] == 1 for row in rows), 'target must be absorbing')
        actions.append(rows)
    return actions, target


def reach(p: dict, c: dict) -> str:
    acts, target = mdp(p)
    n = len(acts)
    fields(c, {'kind', 'value', 'policy', 'dead', 'rank'})
    require(c['kind'] == 'reach_max', 'certificate kind')
    v, r = vector(c['value'], n), vector(c['rank'], n)
    require(type(c['policy']) is list and len(c['policy']) == n, 'policy length')
    require(all(type(a) is int and 0 <= a < len(acts[s]) for s, a in enumerate(c['policy'])),
            'invalid action selector')
    dead = indices(c['dead'], n)
    require(not dead & target, 'target declared dead')
    active = set(range(n)) - target - dead
    require(all(0 <= x <= 1 for x in v), 'probability range')
    require(all(x >= 0 for x in r), 'negative rank')
    require(all(v[s] == 1 for s in target), 'target value')
    require(all(v[s] == 0 for s in dead), 'dead value')
    require(all(r[s] == 0 for s in target | dead), 'rank boundary')
    for s in range(n):
        chosen = acts[s][c['policy'][s]]
        if s in dead:
            require(all(chosen[t] == 0 for t in range(n) if t not in dead), 'dead set not closed')
        if s not in target:
            require(v[s] == sum(chosen[t]*v[t] for t in range(n)), 'selected harmonic equation')
            require(all(sum(row[t]*v[t] for t in range(n)) <= v[s] for row in acts[s]),
                    'not an all-action supersolution')
        if s in active:
            require(r[s] >= 1 + sum(chosen[t]*r[t] for t in active), 'missing exit progress')
    return 'exact_maximum_reachability_all_states'


def runtime(p: dict, c: dict) -> str:
    acts, target = mdp(p)
    n = len(acts)
    fields(c, {'kind', 'potential'})
    require(c['kind'] == 'runtime_upper', 'certificate kind')
    v = vector(c['potential'], n)
    require(all(z >= 0 for z in v), 'negative potential')
    require(all(v[s] == 0 for s in target), 'potential boundary')
    for s in range(n):
        if s not in target:
            for row in acts[s]:
                require(1 + sum(row[t]*v[t] for t in range(n)) <= v[s],
                        'not a uniform unit-cost supersolution')
    return 'expected_hitting_time_upper_every_scheduler'


def transport_data(p: dict):
    fields(p, {'left', 'right', 'allowed', 'cost'})
    mu, nu = law(p['left']), law(p['right'])
    n, m = len(mu), len(nu)
    rel, cost = relation(p['allowed'], n, m), matrix(p['cost'], n, m)
    require(all(z >= 0 for row in cost for z in row), 'negative transport cost')
    return mu, nu, rel, cost


def coupling(mu, nu, rel, raw):
    n, m = len(mu), len(nu)
    pi = matrix(raw, n, m)
    require(all(pi[i][j] >= 0 and ((i, j) in rel or pi[i][j] == 0)
                for i in range(n) for j in range(m)), 'joint sign or support')
    require(all(sum(pi[i]) == mu[i] for i in range(n)), 'left marginal')
    require(all(sum(pi[i][j] for i in range(n)) == nu[j] for j in range(m)), 'right marginal')
    return pi


def hall(mu, nu, rel, c):
    fields(c, {'kind', 'left_set', 'neighbors'})
    require(c['kind'] == 'hall', 'certificate kind')
    subset = indices(c['left_set'], len(mu))
    neighbors = indices(c['neighbors'], len(nu))
    require(neighbors == {j for i, j in rel if i in subset}, 'incomplete neighborhood')
    require(sum(mu[i] for i in subset) > sum(nu[j] for j in neighbors), 'no strict Hall deficit')


def transport(p: dict, c: dict) -> str:
    mu, nu, rel, cost = transport_data(p)
    require(type(c) is dict and 'kind' in c, 'certificate kind')
    if c['kind'] == 'hall':
        hall(mu, nu, rel, c)
        return 'no_coupling_in_named_support_relation'
    fields(c, {'kind', 'joint', 'left_potential', 'right_potential'})
    require(c['kind'] == 'transport', 'certificate kind')
    pi = coupling(mu, nu, rel, c['joint'])
    u, v = vector(c['left_potential'], len(mu)), vector(c['right_potential'], len(nu))
    require(all(u[i] + v[j] <= cost[i][j] for i, j in rel), 'dual infeasible')
    primal = sum(pi[i][j]*cost[i][j] for i in range(len(mu)) for j in range(len(nu)))
    dual = sum(mu[i]*u[i] for i in range(len(mu))) + sum(nu[j]*v[j] for j in range(len(nu)))
    require(primal == dual, 'primal-dual gap')
    return 'optimal_transport_for_named_cost_and_support'


def bisimulation(p: dict, c: dict) -> str:
    fields(p, {'left', 'right', 'obs_left', 'obs_right', 'start'})
    left, right = chain(p['left']), chain(p['right'])
    n, m = len(left), len(right)
    for labels, size in [(p['obs_left'], n), (p['obs_right'], m)]:
        require(type(labels) is list and len(labels) == size, 'observation length')
        require(all((type(x) is int and x.bit_length() <= 128) or
                    (type(x) is str and len(x) <= 128) for x in labels), 'invalid observation')
    initial = {(i, j) for i in range(n) for j in range(m)
               if p['obs_left'][i] == p['obs_right'][j]}
    start = pair(p['start'], n, m)
    require(type(c) is dict and 'kind' in c, 'certificate kind')
    if c['kind'] == 'bisimulation':
        fields(c, {'kind', 'relation', 'couplings'})
        rel = relation(c['relation'], n, m)
        require(start in rel and rel <= initial, 'start or observations')
        require(type(c['couplings']) is list and len(c['couplings']) == len(rel), 'coupling count')
        seen = set()
        for entry in c['couplings']:
            fields(entry, {'pair', 'joint'})
            ij = pair(entry['pair'], n, m)
            require(ij in rel and ij not in seen, 'duplicate or unrelated coupling')
            seen.add(ij)
            coupling(left[ij[0]], right[ij[1]], rel, entry['joint'])
        return 'strong_probabilistic_bisimulation_at_start'
    fields(c, {'kind', 'removals'})
    require(c['kind'] == 'no_bisimulation', 'certificate kind')
    require(type(c['removals']) is list and len(c['removals']) <= n*m, 'removal count')
    rel = set(initial)
    for entry in c['removals']:
        fields(entry, {'pair', 'cut'})
        ij = pair(entry['pair'], n, m)
        require(ij in rel, 'invalid deletion')
        hall(left[ij[0]], right[ij[1]], rel, entry['cut'])
        rel.remove(ij)
    require(start not in rel, 'no obstruction for requested start')
    return 'no_strong_bisimulation_NOT_trace_inequivalence'


def contraction(p: dict, c: dict) -> str:
    fields(p, {'left', 'right', 'distance', 'rate', 'error'})
    left, right = chain(p['left']), chain(p['right'])
    n = len(left)
    require(len(right) == n, 'different metric carrier sizes')
    d, rate, error = matrix(p['distance'], n, n), number(p['rate']), number(p['error'])
    require(0 <= rate < 1 and error >= 0, 'rate or error range')
    for i in range(n):
        for j in range(n):
            require(d[i][j] >= 0 and (d[i][j] == 0) == (i == j) and d[i][j] == d[j][i],
                    'not a metric')
            for k in range(n):
                require(d[i][k] <= d[i][j] + d[j][k], 'triangle inequality')
    rel = {(i, j) for i in range(n) for j in range(n)}
    require(type(c) is dict and 'kind' in c, 'certificate kind')
    if c['kind'] == 'rate_obstruction':
        fields(c, {'kind', 'pair', 'transport'})
        i, j = pair(c['pair'], n, n)
        tp = {'left': p['left'][i], 'right': p['right'][j],
              'cost': p['distance'], 'allowed': [list(x) for x in sorted(rel)]}
        require(c['transport'].get('kind') == 'transport', 'not a dual optimum')
        transport(tp, c['transport'])
        pi = matrix(c['transport']['joint'], n, n)
        optimum = sum(pi[a][b]*d[a][b] for a in range(n) for b in range(n))
        require(optimum > rate*d[i][j] + error, 'not a rate obstruction')
        return 'no_one_step_coupling_at_named_metric_rate_NOT_nonmixing'
    fields(c, {'kind', 'joints'})
    require(c['kind'] == 'contraction', 'certificate kind')
    require(type(c['joints']) is list and len(c['joints']) == n*n, 'joint count')
    for i in range(n):
        for j in range(n):
            pi = coupling(left[i], right[j], rel, c['joints'][i*n+j])
            require(sum(pi[a][b]*d[a][b] for a in range(n) for b in range(n))
                    <= rate*d[i][j] + error, 'affine distance bound')
    return 'all_horizon_affine_expected_distance_bound'


def shift_poly(poly: list[Fraction], shift: int) -> list[Fraction]:
    """Horner composition, not the producer's binomial-moment construction."""
    out = [Fraction(0)]
    for a in reversed(poly):
        new = [Fraction(0)] * (len(out) + 1)
        for i, z in enumerate(out):
            new[i] += shift*z
            new[i+1] += z
        new[0] += a
        out = new
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def polynomial_cost(p: dict, c: dict) -> str:
    fields(p, {'jumps', 'probabilities', 'cost'})
    require(type(p['jumps']) is list and 0 < len(p['jumps']) <= 16, 'jump count')
    jumps = p['jumps']
    require(all(type(j) is int and -1 <= j <= 16 for j in jumps), 'skip-free jump condition')
    require(len(set(jumps)) == len(jumps), 'duplicate jumps')
    probs, cost = law(p['probabilities'], len(jumps)), vector(p['cost'])
    require(0 < len(cost) <= MAX_DEGREE, 'cost degree')
    fields(c, {'kind', 'potential', 'epsilon'})
    require(c['kind'] == 'polynomial_cost', 'certificate kind')
    v, eps = vector(c['potential']), number(c['epsilon'])
    require(0 < len(v) <= MAX_DEGREE + 1 and v[0] == 0, 'potential degree or boundary')
    require(all(x >= 0 for x in v) and eps >= 0, 'potential sign or epsilon')
    boundcost = shift_poly(cost, 1)
    boundcost[0] -= eps
    require(all(x >= 0 for x in boundcost), 'cost lower-bound coefficients')
    length = max(len(v), len(cost))
    drift = [v[i] if i < len(v) else Fraction(0) for i in range(length)]
    for j, probability in zip(jumps, probs):
        moved = shift_poly(v, j)
        for i, x in enumerate(moved):
            drift[i] -= probability*x
    for i, x in enumerate(cost):
        drift[i] -= x
    require(all(x >= 0 for x in shift_poly(drift, 1)), 'drift not nonnegative on n >= 1')
    return ('expected_cost_and_runtime_upper' if eps > 0 else
            'expected_cost_upper_NOT_a_termination_claim')


WORKERS = {'reach': reach, 'runtime': runtime, 'transport': transport,
           'bisimulation': bisimulation, 'contraction': contraction,
           'polynomial_cost': polynomial_cost}


def audit(worker: str, problem: Any, certificate: Any) -> dict:
    try:
        require(worker in WORKERS, 'unknown worker')
        claim = WORKERS[worker](problem, certificate)
        return {'accepted': True, 'claim': claim}
    except (ValueError, TypeError, KeyError, IndexError, ZeroDivisionError,
            AttributeError, OverflowError) as exc:
        return {'accepted': False, 'reason': str(exc)}


def check(worker: str, problem: Any, certificate: Any) -> bool:
    return audit(worker, problem, certificate)['accepted']


def loads(text: str) -> Any:
    require(type(text) is str and len(text.encode('utf-8')) <= MAX_BYTES, 'JSON byte budget')
    def obj(pairs):
        result = {}
        for key, val in pairs:
            require(key not in result, 'duplicate JSON field')
            result[key] = val
        return result
    def bad_float(_):
        raise ValueError('floating point and nonfinite constants forbidden')
    return json.loads(text, object_pairs_hook=obj, parse_float=bad_float, parse_constant=bad_float)
