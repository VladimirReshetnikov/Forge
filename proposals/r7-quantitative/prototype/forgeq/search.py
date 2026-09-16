"""Untrusted, exact-rational producers for Forge-Q research certificates.

Only the Python standard library is used. The checker is deliberately not
imported. Search limits mean UNKNOWN, never that a Lean proposition is false.
Public functions expect well-formed problem dictionaries (checker validates
all externally supplied problems again). Fractions serialize as strings.
"""
from __future__ import annotations
from fractions import Fraction as F
from itertools import product
from math import comb
from typing import Any


def dump(x: Any) -> Any:
    if isinstance(x, F):
        return str(x)
    if isinstance(x, (list, tuple)):
        return [dump(a) for a in x]
    if isinstance(x, dict):
        return {k: dump(v) for k, v in x.items()}
    return x


def solve(a: list[list[F]], b: list[F]) -> list[F] | None:
    """Exact square-system Gauss-Jordan elimination; singular -> None."""
    n = len(b)
    if not n:
        return []
    m = [list(map(F, row)) + [F(y)] for row, y in zip(a, b)]
    if len(m) != n or any(len(row) != n + 1 for row in m):
        raise ValueError('square system required')
    for j in range(n):
        pivot = next((i for i in range(j, n) if m[i][j]), None)
        if pivot is None:
            return None
        m[j], m[pivot] = m[pivot], m[j]
        q = m[j][j]
        m[j] = [z / q for z in m[j]]
        for i in range(n):
            if i != j:
                q = m[i][j]
                m[i] = [x - q * y for x, y in zip(m[i], m[j])]
    return [row[-1] for row in m]


def chain_values(p: list[list[F]], target: set[int]):
    """Graph classification + two linear solves. Returns v, dead, exit rank."""
    n = len(p)
    live = set(target)
    while True:
        grown = live | {i for i in range(n) if any(p[i][j] > 0 for j in live)}
        if grown == live:
            break
        live = grown
    dead = set(range(n)) - live
    active = sorted(live - target)
    a = [[F(i == j) - p[i][j] for j in active] for i in active]
    val = solve(a, [sum(p[i][j] for j in target) for i in active])
    rank = solve(a, [F(1) for _ in active])
    if val is None or rank is None:
        raise ArithmeticError('transient graph generated singular system')
    v, r = [F(i in target) for i in range(n)], [F(0) for _ in range(n)]
    for k, i in enumerate(active):
        v[i], r[i] = val[k], rank[k]
    return v, dead, r


def reachability(problem: dict, max_policies: int = 100000) -> dict:
    """An exact maximum-reachability certificate, including a proper witness.

    Enumerates deterministic stationary policies. This is a small reference
    producer, not a scalable MDP solver. The rank concerns exit to target OR
    the selected policy's closed zero-probability region.
    """
    acts = [[[F(x) for x in row] for row in choices] for choices in problem['actions']]
    target = set(problem['target'])
    for k, policy in enumerate(product(*(range(len(x)) for x in acts))):
        if k >= max_policies:
            return {'kind': 'unknown', 'reason': 'policy budget'}
        p = [choices[a] for choices, a in zip(acts, policy)]
        v, dead, rank = chain_values(p, target)
        if all(sum(x*y for x, y in zip(row, v)) <= v[s]
               for s, choices in enumerate(acts) if s not in target for row in choices):
            return dump({'kind': 'reach_max', 'value': v, 'policy': list(policy),
                         'dead': sorted(dead), 'rank': rank})
    return {'kind': 'unknown', 'reason': 'no candidate accepted by producer'}


def runtime(problem: dict, max_policies: int = 100000) -> dict:
    """Uniform expected hitting-time upper bound for EVERY scheduler."""
    acts = [[[F(x) for x in row] for row in choices] for choices in problem['actions']]
    target, n = set(problem['target']), len(acts)
    active = [i for i in range(n) if i not in target]
    for k, policy in enumerate(product(*(range(len(x)) for x in acts))):
        if k >= max_policies:
            return {'kind': 'unknown', 'reason': 'policy budget'}
        p = [choices[a] for choices, a in zip(acts, policy)]
        a = [[F(i == j) - p[i][j] for j in active] for i in active]
        ans = solve(a, [F(1) for _ in active])
        if ans is None:
            continue
        v = [F(0)] * n
        for i, x in zip(active, ans):
            v[i] = x
        if all(x >= 0 for x in v) and all(
            1 + sum(x*y for x, y in zip(row, v)) <= v[s]
            for s, choices in enumerate(acts) if s not in target for row in choices):
            return dump({'kind': 'runtime_upper', 'potential': v})
    return {'kind': 'unknown', 'reason': 'no uniform runtime certificate'}


def transport(problem: dict, max_augmentations: int = 100000) -> dict:
    """Min-cost rational transport with a dual certificate, or a Hall cut.

    Successive shortest augmenting paths use Bellman-Ford on the residual
    graph. Artificial internal capacities are 2 > total mass, so the dual
    certificate has no artificial upper-bound multipliers. A final shortest
    potential computation starts at a zero-cost super-source.
    """
    mu, nu = list(map(F, problem['left'])), list(map(F, problem['right']))
    n, m = len(mu), len(nu)
    allowed = {tuple(e) for e in problem['allowed']}
    cost = [[F(x) for x in row] for row in problem['cost']]
    N, src, sink = n + m + 2, n + m, n + m + 1
    cap = [[F(0) for _ in range(N)] for _ in range(N)]
    weight = [[F(0) for _ in range(N)] for _ in range(N)]
    def edge(u, v, capacity, c):
        cap[u][v], weight[u][v], weight[v][u] = capacity, c, -c
    for i in range(n):
        edge(src, i, mu[i], F(0))
    for i, j in allowed:
        edge(i, n + j, F(2), cost[i][j])
    for j in range(m):
        edge(n + j, sink, nu[j], F(0))
    total, steps = F(0), 0
    while total < 1:
        if steps >= max_augmentations:
            return {'kind': 'unknown', 'reason': 'augmentation budget'}
        steps += 1
        dist, pred = [None] * N, [-1] * N
        dist[src] = F(0)
        for _ in range(N - 1):
            changed = False
            for u in range(N):
                if dist[u] is None:
                    continue
                for v in range(N):
                    d = dist[u] + weight[u][v]
                    if cap[u][v] > 0 and (dist[v] is None or d < dist[v]):
                        dist[v], pred[v], changed = d, u, True
            if not changed:
                break
        if dist[sink] is None:
            seen, queue = {src}, [src]
            for u in queue:
                for v in range(N):
                    if cap[u][v] > 0 and v not in seen:
                        seen.add(v)
                        queue.append(v)
            left = sorted(i for i in range(n) if i in seen)
            neighbors = sorted({j for i, j in allowed if i in left})
            return {'kind': 'hall', 'left_set': left, 'neighbors': neighbors}
        path, v = [], sink
        while v != src:
            u = pred[v]
            if u < 0 or len(path) >= N:
                raise ArithmeticError('invalid residual predecessor path')
            path.append((u, v))
            v = u
        amount = min(cap[u][v] for u, v in path)
        for u, v in path:
            cap[u][v] -= amount
            cap[v][u] += amount
        total += amount
    pi = [[F(2) - cap[i][n+j] if (i, j) in allowed else F(0)
           for j in range(m)] for i in range(n)]
    d = [F(0)] * N
    for it in range(N):
        changed = False
        for u in range(N):
            for v in range(N):
                if cap[u][v] > 0 and d[v] > d[u] + weight[u][v]:
                    d[v], changed = d[u] + weight[u][v], True
        if not changed:
            break
        if it == N - 1:
            raise ArithmeticError('negative residual cycle after optimization')
    return dump({'kind': 'transport', 'joint': pi,
                 'left_potential': [-d[i] for i in range(n)],
                 'right_potential': [d[n+j] for j in range(m)]})


def transport_problem(mu, nu, relation=None, cost=None) -> dict:
    n, m = len(mu), len(nu)
    return dump({'left': mu, 'right': nu,
        'allowed': sorted(relation if relation is not None else product(range(n), range(m))),
        'cost': cost if cost is not None else [[F(0)] * m for _ in range(n)]})


def bisimulation(problem: dict, max_calls: int = 100000) -> dict:
    """Greatest relational fixed point; failures include local Hall cuts.

    A negative result means no STRONG PROBABILISTIC BISIMULATION. It is not
    a refutation of trace-distribution equivalence.
    """
    p, q = problem['left'], problem['right']
    n, m = len(p), len(q)
    rel = {(i, j) for i in range(n) for j in range(m)
           if problem['obs_left'][i] == problem['obs_right'][j]}
    start, removed, calls = tuple(problem['start']), [], 0
    if start not in rel:
        return {'kind': 'no_bisimulation', 'removals': []}
    while True:
        changed, witnesses = False, []
        for pair in sorted(rel):
            calls += 1
            if calls > max_calls:
                return {'kind': 'unknown', 'reason': 'transport-call budget'}
            i, j = pair
            result = transport(transport_problem(p[i], q[j], rel))
            if result['kind'] == 'unknown':
                return result
            if result['kind'] == 'hall':
                removed.append({'pair': list(pair), 'cut': result})
                rel.remove(pair)
                changed = True
                if start not in rel:
                    return {'kind': 'no_bisimulation', 'removals': removed}
            else:
                witnesses.append({'pair': list(pair), 'joint': result['joint']})
        if not changed:
            return {'kind': 'bisimulation', 'relation': [list(e) for e in sorted(rel)],
                    'couplings': witnesses}


def contraction(problem: dict) -> dict:
    """All-pairs affine distance bound for two kernels on one finite metric."""
    p, q, d = problem['left'], problem['right'], problem['distance']
    kappa, eps, joints = F(problem['rate']), F(problem['error']), []
    for i in range(len(p)):
        for j in range(len(p)):
            t = transport(transport_problem(p[i], q[j], cost=d))
            if t['kind'] != 'transport':
                return {'kind': 'unknown', 'reason': 'transport did not complete'}
            value = sum(F(t['joint'][a][b]) * F(d[a][b])
                        for a in range(len(p)) for b in range(len(p)))
            if value > kappa * F(d[i][j]) + eps:
                return {'kind': 'rate_obstruction', 'pair': [i, j], 'transport': t}
            joints.append(t['joint'])
    return {'kind': 'contraction', 'joints': joints}


def polynomial_cost(problem: dict, max_degree: int = 10) -> dict:
    """Poisson-equation synthesis for a stopped skip-free random walk on N.

    The degree-d potential is solved from V - E[V(n+J)] = cost. Acceptance
    additionally needs coefficient positivity; failure is not nontermination.
    """
    jumps, probs = problem['jumps'], list(map(F, problem['probabilities']))
    cost = list(map(F, problem['cost']))
    while len(cost) > 1 and cost[-1] == 0:
        cost.pop()
    degree = len(cost)
    if degree > max_degree:
        return {'kind': 'unknown', 'reason': 'degree budget'}
    if sum(F(j) * p for j, p in zip(jumps, probs)) >= 0:
        return {'kind': 'unknown', 'reason': 'negative drift fragment required'}
    a = [[-F(comb(k, i)) * sum(p * F(j) ** (k-i) for j, p in zip(jumps, probs))
          if i < k else F(0)
          for k in range(1, degree + 1)] for i in range(degree)]
    coeff = solve(a, cost)
    if coeff is None or any(x < 0 for x in coeff) or any(x < 0 for x in cost):
        return {'kind': 'unknown', 'reason': 'coefficient positivity vocabulary'}
    return dump({'kind': 'polynomial_cost', 'potential': [F(0)] + coeff,
                 'epsilon': sum(cost)})
