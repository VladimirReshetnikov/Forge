"""Backward coverability for finite-control vector addition systems.

Search only. Certificates are checked by checker.py, which does not import this
module. All counters and initial-family coefficients are nonnegative integers.
A transition consumes tokens before producing tokens. Resource exhaustion is
UNKNOWN, not a proof. Python >= 3.10; standard library only.
"""
from __future__ import annotations
from collections import deque
from dataclasses import dataclass
from typing import Any

Vector = tuple[int, ...]

def le(a: Vector, b: Vector) -> bool:
    return all(x <= y for x, y in zip(a, b))

def predecessor(consume: Vector, produce: Vector, target: Vector) -> Vector:
    return tuple(a + max(0, b - z) for a, z, b in zip(consume, produce, target))

def initial_witness(family: dict, threshold: Vector) -> list[int] | None:
    """Find n >= 0 with base + sum(n_j * ray_j) >= threshold, if one exists."""
    base, rays = family['base'], family['rays']
    common = 0
    for i, b in enumerate(threshold):
        need = b - base[i]
        if need <= 0:
            continue
        slope = sum(ray[i] for ray in rays)
        if slope == 0:
            return None
        common = max(common, (need + slope - 1) // slope)
    return [common] * len(rays)

def initial_value(family: dict, params: list[int]) -> Vector:
    return tuple(b + sum(n * ray[i] for n, ray in zip(params, family['rays']))
                 for i, b in enumerate(family['base']))

@dataclass(frozen=True)
class Node:
    control: int
    vector: Vector
    edge: int | None
    successor: int | None


def solve(problem: dict, *, max_admissions: int = 20000,
          max_predecessors: int = 200000) -> dict:
    """Input must first pass checker.validate_vass at a public boundary.

    'safe' carries a backward-closed superset of the bad set; 'unsafe' carries
    an ordinary executable transition sequence. Active antichains may delete
    dominated vectors, but immutable witness nodes are never deleted.
    """
    controls = problem['controls']
    edges = problem['transitions']
    incoming = [[] for _ in range(controls)]
    for i, edge in enumerate(edges):
        incoming[edge['dst']].append(i)
    active: list[dict[Vector, int]] = [dict() for _ in range(controls)]
    history: list[Node] = []
    pending: deque[int] = deque()
    attempts = 0
    largest = 0

    def stats() -> dict:
        return {'admissions': len(history), 'predecessors': attempts,
                'final_basis': sum(map(len, active)), 'peak_basis': largest}

    def add(q: int, vec: Vector, edge: int | None, nxt: int | None) -> int | None:
        nonlocal largest
        if any(le(old, vec) for old in active[q]):
            return None
        for old in list(active[q]):
            if le(vec, old):
                del active[q][old]
        idx = len(history)
        history.append(Node(q, vec, edge, nxt))
        active[q][vec] = idx
        pending.append(idx)
        largest = max(largest, sum(map(len, active)))
        return idx

    def counterexample(idx: int) -> dict | None:
        node = history[idx]
        for fi, family in enumerate(problem['initials']):
            if family['control'] != node.control:
                continue
            params = initial_witness(family, node.vector)
            if params is None:
                continue
            trace = []
            cursor = idx
            while history[cursor].edge is not None:
                trace.append(history[cursor].edge)
                successor = history[cursor].successor
                assert successor is not None
                cursor = successor
            return {'schema': 1, 'kind': 'unsafe', 'initial': fi,
                    'parameters': params, 'transitions': trace, 'stats': stats()}
        return None

    for bad in problem['bad']:
        idx = add(bad['control'], tuple(bad['vector']), None, None)
        if idx is not None:
            answer = counterexample(idx)
            if answer:
                return answer
    while pending:
        if len(history) > max_admissions or attempts >= max_predecessors:
            return {'schema': 1, 'kind': 'unknown', 'reason': 'budget', 'stats': stats()}
        idx = pending.popleft()
        node = history[idx]
        if active[node.control].get(node.vector) != idx:
            continue
        for eid in incoming[node.control]:
            attempts += 1
            if attempts > max_predecessors:
                return {'schema': 1, 'kind': 'unknown', 'reason': 'budget', 'stats': stats()}
            edge = edges[eid]
            vec = predecessor(tuple(edge['consume']), tuple(edge['produce']), node.vector)
            new_id = add(edge['src'], vec, eid, idx)
            if new_id is not None:
                answer = counterexample(new_id)
                if answer:
                    return answer
                if len(history) > max_admissions:
                    return {'schema': 1, 'kind': 'unknown', 'reason': 'budget', 'stats': stats()}
    return {'schema': 1, 'kind': 'safe',
            'basis': [[list(v) for v in sorted(group)] for group in active], 'stats': stats()}
