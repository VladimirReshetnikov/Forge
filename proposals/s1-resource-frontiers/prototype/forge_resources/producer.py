"""Untrusted certificate producers. Bounded failures always return UNKNOWN."""
from __future__ import annotations
from collections import deque
from dataclasses import dataclass
from itertools import product
from math import prod
from time import perf_counter_ns
from typing import Any
from .model import Net, Vector, RunDAG, leq, vector, natural


@dataclass(frozen=True)
class Entry:
    marking: Vector
    run: int
    target: int


def frontier(problem: dict[str, Any], *, max_candidates: int = 100_000,
             max_insertions: int = 20_000, accelerate: bool = False) -> dict[str, Any]:
    """Compute the exact minimal initial-marking basis of eventual coverability.

    Deleting a dominated basis entry NEVER deletes its immutable provenance.
    Completion is certified by local closure and one positive run per survivor.
    """
    natural(max_candidates); natural(max_insertions)
    if type(accelerate) is not bool: raise ValueError("accelerate must be Boolean")
    net = Net.from_dict(problem)
    dag = RunDAG(net)
    history: list[Entry] = []
    active: set[int] = set()
    queue: deque[int] = deque()
    stats = {"candidates": 0, "insertions": 0, "deletions": 0,
             "maximum_basis": 0, "stale_work_items": 0}
    start = perf_counter_ns()

    def insert(b: Vector, run: int, target: int) -> bool:
        if any(leq(history[i].marking, b) for i in active):
            return False
        obsolete = [i for i in active if leq(b, history[i].marking)]
        active.difference_update(obsolete)
        stats["deletions"] += len(obsolete)
        i = len(history)
        history.append(Entry(b, run, target))
        active.add(i); queue.append(i)
        stats["insertions"] += 1
        stats["maximum_basis"] = max(stats["maximum_basis"], len(active))
        return True

    def unknown(reason: str) -> dict[str, Any]:
        return {"status": "UNKNOWN", "reason": reason, "certificate": None,
                "stats": stats | {"search_ns": perf_counter_ns() - start}}

    for j, b in enumerate(net.targets):
        if stats["insertions"] >= max_insertions:
            return unknown("insertion budget exhausted during initialization")
        insert(b, 0, j)
    while queue:
        i = queue.popleft()
        if i not in active:
            stats["stale_work_items"] += 1
            continue
        entry = history[i]
        for t, transition in enumerate(net.transitions):
            if stats["candidates"] >= max_candidates:
                return unknown("candidate budget exhausted")
            stats["candidates"] += 1
            count = 1
            if accelerate and all(p >= c for c, p in zip(transition.consume, transition.produce)):
                # Exact saturation by powers of one productive transition.
                # H makes all increasing coordinates reach their backward plateau.
                count = max([1] + [(max(0, bi-ci) + pi-ci-1)//(pi-ci)
                    for bi,ci,pi in zip(entry.marking, transition.consume, transition.produce) if pi>ci])
                b = tuple(ci if pi>ci else max(ci,bi)
                    for bi,ci,pi in zip(entry.marking, transition.consume, transition.produce))
            else:
                b = transition.predecessor(entry.marking)
            if any(leq(history[j].marking, b) for j in active):
                continue
            if stats["insertions"] >= max_insertions:
                return unknown("insertion budget exhausted")
            stem = dag.step(t)
            if count != 1: stem = dag.repeat(stem, count)
            run = dag.seq(stem, entry.run)
            insert(b, run, entry.target)
    survivors = sorted((history[i] for i in active), key=lambda e: e.marking)
    nodes, roots = dag.compact([e.run for e in survivors])

    def covering_index(b: Vector) -> int:
        return next(i for i, e in enumerate(survivors) if leq(e.marking, b))

    cert = {"schema": "forge.resources.frontier.v1", "problem": net.to_dict(),
            "basis": [{"marking": list(e.marking), "run": r, "target": e.target}
                      for e, r in zip(survivors, roots)],
            "runs": nodes,
            "target_cover": [covering_index(b) for b in net.targets],
            "predecessor_cover": [[covering_index(t.predecessor(e.marking))
                                   for t in net.transitions] for e in survivors]}
    stats |= {"final_basis": len(survivors), "run_nodes": len(nodes),
              "search_ns": perf_counter_ns() - start}
    return {"status": "CERTIFICATE", "certificate": cert, "stats": stats}


def affine(matrix: list[list[int]], offset: list[int], theta: tuple[int, ...]) -> Vector:
    return tuple(c + sum(a * n for a, n in zip(row, theta))
                 for row, c in zip(matrix, offset))


def validate_family(net: Net, matrix: Any, offset: Any) -> tuple[list[list[int]], list[int], int]:
    if type(matrix) is not list or len(matrix) != net.dimension:
        raise ValueError("bad affine matrix")
    # With no places, the number of parameters must be supplied separately;
    # the public parameter producer intentionally refuses that ambiguous encoding.
    if net.dimension == 0:
        raise ValueError("parameter families require at least one place")
    if type(matrix[0]) is not list:
        raise ValueError("matrix rows must be lists")
    k = len(matrix[0])
    rows = [list(vector(row, k)) for row in matrix]
    return rows, list(vector(offset, net.dimension)), k


def threshold(problem: dict[str, Any], fc: dict[str, Any], slope: list[int],
              offset: list[int]) -> dict[str, Any]:
    net = Net.from_dict(problem)
    a = vector(slope, net.dimension); c = vector(offset, net.dimension)
    bounds: list[int | None] = []
    for entry in fc["basis"]:
        b = entry["marking"]
        if any(ai == 0 and ci < bi for ai, ci, bi in zip(a, c, b)):
            bounds.append(None)
        else:
            bounds.append(max([0] + [(max(0, bi - ci) + ai - 1) // ai
                                    for ai, ci, bi in zip(a, c, b) if ai > 0]))
    finite = [n for n in bounds if n is not None]
    query = {"problem": problem, "slope": list(a), "offset": list(c)}
    return {"schema": "forge.resources.threshold.v1", "query": query,
            "frontier": fc, "basis_thresholds": bounds,
            "threshold": min(finite) if finite else None}


def parameters(problem: dict[str, Any], fc: dict[str, Any], matrix: list[list[int]],
               offset: list[int], *, max_box: int = 100_000) -> dict[str, Any]:
    """Exact Pareto frontier via a proved finite cap, not a guessed search box."""
    net = Net.from_dict(problem)
    matrix, offset, k = validate_family(net, matrix, offset)
    basis = [tuple(e["marking"]) for e in fc["basis"]]
    eligible = [b for b in basis if not any(
        all(a == 0 for a in row) and c < bi
        for row, c, bi in zip(matrix, offset, b))]
    caps = [max([0] + [(max(0, b[i] - offset[i]) + matrix[i][j] - 1) // matrix[i][j]
                      for b in eligible for i in range(net.dimension) if matrix[i][j] > 0])
            for j in range(k)]
    cells = prod(c + 1 for c in caps)
    if cells > max_box:
        return {"status": "UNKNOWN", "reason": "certified cap exceeds enumeration budget",
                "box_cells": cells, "certificate": None}
    unsafe: list[Vector] = []
    for theta in product(*(range(c + 1) for c in caps)):
        m = affine(matrix, offset, theta)
        if any(leq(b, m) for b in eligible) and not any(leq(f, theta) for f in unsafe):
            unsafe = [f for f in unsafe if not leq(theta, f)]
            unsafe.append(theta)
    minima = sorted(unsafe)
    covers = []
    for theta in product(*(range(c + 1) for c in caps)):
        covers.append(next((i for i, f in enumerate(minima) if leq(f, theta)), -1))
    witnesses = [next(i for i, b in enumerate(basis) if leq(b, affine(matrix, offset, f)))
                 for f in minima]
    query = {"problem": problem, "matrix": matrix, "offset": offset}
    cert = {"schema": "forge.resources.parameters.v1", "query": query,
            "frontier": fc, "caps": caps, "minima": [list(f) for f in minima],
            "witness_basis": witnesses, "covers": covers}
    return {"status": "CERTIFICATE", "certificate": cert, "box_cells": cells}


def find_lasso(problem: dict[str, Any], initial: list[int], *, claim: str = "unbounded",
               place: int = 0, max_depth: int = 12, max_nodes: int = 10_000) -> dict[str, Any]:
    """Bounded path search. A negative search result is never a termination proof."""
    net = Net.from_dict(problem)
    m0 = vector(initial, net.dimension)
    if claim not in ("unbounded", "nontermination"):
        raise ValueError("unsupported lasso claim")
    if claim == "unbounded" and not (type(place) is int and 0 <= place < net.dimension):
        raise ValueError("bad growth place")
    query = {"problem": problem, "initial": list(m0), "claim": claim,
             "place": place if claim == "unbounded" else None}
    queue = deque([(m0, (), (m0,))])
    expanded = 0
    while queue and expanded < max_nodes:
        state, path, ancestors = queue.popleft()
        if len(path) >= max_depth:
            continue
        expanded += 1
        for t, transition in enumerate(net.transitions):
            dest = transition.fire(state)
            if dest is None:
                continue
            extended = path + (t,)
            for j, old in enumerate(ancestors):
                if leq(old, dest) and (claim == "nontermination" or dest[place] > old[place]):
                    dag = RunDAG(net)
                    roots = [dag.word(extended[:j]), dag.word(extended[j:])]
                    nodes, roots = dag.compact(roots)
                    cert = {"schema": "forge.resources.lasso.v1", "query": query,
                            "runs": nodes, "prefix": roots[0], "loop": roots[1]}
                    return {"status": "CERTIFICATE", "certificate": cert,
                            "expanded_paths": expanded}
            if dest not in ancestors:
                queue.append((dest, extended, ancestors + (dest,)))
    return {"status": "UNKNOWN", "certificate": None, "expanded_paths": expanded,
            "reason": "no qualifying lasso found within the bounded path search"}


def compare_programs(query: dict[str, Any]) -> dict[str, Any]:
    """Decide guarded endpoint equivalence, ignoring primitive step counts.

    The input contains BOTH original programs. Equality is not claimed merely
    because two worker-supplied summaries happen to match.
    """
    from .model import ResourceSummary
    if set(query) != {'problem', 'left', 'right'}:
        raise ValueError('unexpected equivalence query fields')
    net = Net.from_dict(query['problem'])

    def summarize(program):
        if set(program) != {'nodes', 'root'}:
            raise ValueError('bad compressed program')
        summaries = []
        for i, node in enumerate(program['nodes']):
            op = node['op']
            def prior(j):
                if type(j) is not int or not 0 <= j < i:
                    raise ValueError('non-prior program reference')
                return summaries[j]
            if op == 'empty': s = ResourceSummary.empty(net.dimension)
            elif op == 'step': s = ResourceSummary.step(net.transitions[node['transition']])
            elif op == 'seq': s = prior(node['left']).then(prior(node['right']))
            elif op == 'repeat': s = prior(node['body']).repeat(node['count'])
            else: raise ValueError('unknown program operation')
            summaries.append(s)
        r = program['root']
        if type(r) is not int or not 0 <= r < len(summaries): raise ValueError('bad program root')
        return summaries[r]

    left = summarize(query['left']); right = summarize(query['right'])
    if (left.need, left.give) == (right.need, right.give):
        verdict = 'equivalent'; witness = None
    else:
        verdict = 'different'
        if not leq(right.need, left.need): witness = list(left.need)
        elif not leq(left.need, right.need): witness = list(right.need)
        else: witness = list(left.need)
    return {'schema': 'forge.resources.equivalence.v1', 'query': query,
            'verdict': verdict, 'separating_initial': witness}
