# PROVENANCE: s1's frontier search, s3's control-indexed backward search, s4's
# region search. All three are the same loop over a different predecessor rule.
# The loop is written once here. Nothing in certificates.py imports this module.
"""Backward search: saturate the predecessor-closure of an upward-closed set.

The set of configurations that can cover a target is upward-closed, and its
minimal elements form an antichain. Repeatedly adding predecessors and pruning
dominated elements therefore terminates, by Dickson's lemma for counters and
Higman's lemma for channels. The result is a FINITE basis for an infinite set,
which is the point: it is a certificate, and certificates.py checks it without
running any search at all.

Three outcomes, and the distinction between the last two matters:

  'unsafe'   a specific initial configuration and a run reaching the target
  'safe'     a finite backward-closed basis, whose upward closure misses
             every initial configuration
  'unknown'  a budget was exhausted

'unknown' is an operational refusal. It is not a weak form of 'safe', and no
caller should read it as one.
"""
from __future__ import annotations
from collections import deque
from dataclasses import dataclass
from typing import Any, Callable, Sequence

from .nets import (ChannelTransition, Edge, InitialFamily, MatrixTransition,
                   Net, Vass)
from .orders import (Antichain, Budget, Vector, dickson_leq, higman_leq,
                     predecessor)
from .summaries import ResourceSummary, RunDAG


@dataclass(frozen=True)
class Node:
    """An admitted configuration and the single step that justified it.

    Immutable, and never deleted. The active antichain drops dominated
    elements to stay small, but a dropped element may still be the tail of
    some other element's witness chain, so the history is append-only.
    """
    control: int
    value: Any
    edge: int | None
    successor: int | None


def _backward(controls: int, incoming: list[list[int]],
              seeds: Sequence[tuple[int, Any]],
              step_back: Callable[[int, tuple[int, Any]], list[tuple[int, Any]]],
              leq: Callable[[Any, Any], bool],
              escape: Callable[[int, int, list[Node]], dict | None],
              budget: Budget) -> dict:
    """The shared loop. `escape` reports a counterexample, or None."""
    active = [Antichain(leq) for _ in range(controls)]
    # The node id that currently OWNS each live antichain element. An element
    # dropped by pruning simply loses its entry; its history node survives,
    # because some other element's witness chain may still pass through it.
    owner: list[dict[Any, int]] = [dict() for _ in range(controls)]
    history: list[Node] = []
    pending: deque[int] = deque()
    attempts = 0
    peak = 0

    def stats() -> dict:
        return {'admissions': len(history), 'predecessors': attempts,
                'final_basis': sum(len(a) for a in active), 'peak_basis': peak}

    def admit(control: int, value: Any, edge: int | None, nxt: int | None) -> int | None:
        nonlocal peak
        if not active[control].add(value):
            return None
        live = set(active[control].elements)
        owner[control] = {v: i for v, i in owner[control].items() if v in live}
        node = len(history)
        history.append(Node(control, value, edge, nxt))
        owner[control][value] = node
        pending.append(node)
        peak = max(peak, sum(len(a) for a in active))
        return node

    for control, value in seeds:
        node = admit(control, value, None, None)
        if node is not None:
            found = escape(node, control, history)
            if found is not None:
                return dict(found, stats=stats())

    while pending:
        if len(history) > budget.admissions or attempts >= budget.predecessors:
            return {'kind': 'unknown', 'reason': 'budget', 'stats': stats()}
        node_id = pending.popleft()
        node = history[node_id]
        if owner[node.control].get(node.value) != node_id:
            continue          # superseded by a strictly smaller element
        for edge_index in incoming[node.control]:
            attempts += 1
            if attempts > budget.predecessors:
                return {'kind': 'unknown', 'reason': 'budget', 'stats': stats()}
            for control, value in step_back(edge_index, (node.control, node.value)):
                fresh = admit(control, value, edge_index, node_id)
                if fresh is None:
                    continue
                found = escape(fresh, control, history)
                if found is not None:
                    return dict(found, stats=stats())
                if len(history) > budget.admissions:
                    return {'kind': 'unknown', 'reason': 'budget', 'stats': stats()}

    return {'kind': 'safe',
            'basis': [sorted(a.elements) for a in active],
            'stats': stats()}


def _trace(history: list[Node], node_id: int) -> list[int]:
    out: list[int] = []
    cursor = node_id
    while history[cursor].edge is not None:
        out.append(history[cursor].edge)          # type: ignore[arg-type]
        nxt = history[cursor].successor
        assert nxt is not None
        cursor = nxt
    return out


# --------------------------------------------------------------------------
# s3: counter systems with parameterised initial families.
# --------------------------------------------------------------------------
def solve_vass(system: Vass, bad: Sequence[tuple[int, Vector]],
               initials: Sequence[InitialFamily],
               budget: Budget = Budget()) -> dict:
    def escape(node_id: int, control: int, history: list[Node]) -> dict | None:
        value = history[node_id].value
        for i, family in enumerate(initials):
            if family.control != control:
                continue
            parameters = family.witness(value)
            if parameters is None:
                continue
            if not dickson_leq(value, family.value(parameters)):
                continue      # the witness search overshot; not a proof of anything
            return {'kind': 'unsafe', 'initial': i, 'parameters': parameters,
                    'transitions': _trace(history, node_id)}
        return None

    return _backward(system.controls, system.incoming(), list(bad),
                     system.predecessors, dickson_leq, escape, budget)


# --------------------------------------------------------------------------
# s4: matrix updates and lossy channels, over the same loop.
# --------------------------------------------------------------------------
def solve_matrix(controls: int, transitions: Sequence[MatrixTransition],
                 bad: Sequence[tuple[int, Vector]],
                 initials: Sequence[tuple[int, Vector]],
                 budget: Budget = Budget()) -> dict:
    incoming: list[list[int]] = [[] for _ in range(controls)]
    for i, t in enumerate(transitions):
        incoming[t.target].append(i)

    def step_back(i: int, target: tuple[int, Vector]) -> list[tuple[int, Vector]]:
        return transitions[i].predecessors(target)

    def escape(node_id: int, control: int, history: list[Node]) -> dict | None:
        value = history[node_id].value
        for i, (q, start) in enumerate(initials):
            if q == control and dickson_leq(value, start):
                return {'kind': 'unsafe', 'initial': i,
                        'transitions': _trace(history, node_id)}
        return None

    return _backward(controls, incoming, list(bad), step_back, dickson_leq,
                     escape, budget)


def solve_lossy(controls: int, transitions: Sequence[ChannelTransition],
                bad: Sequence[tuple[int, tuple[str, ...]]],
                initials: Sequence[tuple[int, tuple[str, ...]]],
                budget: Budget = Budget()) -> dict:
    incoming: list[list[int]] = [[] for _ in range(controls)]
    for i, t in enumerate(transitions):
        incoming[t.target].append(i)

    def step_back(i, target):
        return transitions[i].predecessors(target)

    def escape(node_id: int, control: int, history: list[Node]) -> dict | None:
        value = history[node_id].value
        for i, (q, start) in enumerate(initials):
            if q == control and higman_leq(value, start):
                return {'kind': 'unsafe', 'initial': i,
                        'transitions': _trace(history, node_id)}
        return None

    return _backward(controls, incoming, list(bad), step_back, higman_leq,
                     escape, budget)


# --------------------------------------------------------------------------
# s1: the frontier over ALL initial markings.
# --------------------------------------------------------------------------
def frontier(net: Net, budget: Budget = Budget()) -> dict:
    """The minimal markings from which some target is coverable.

    A different question from the three above, and the only one in the fourth
    round that is not "is this one configuration safe". Its answer is a basis
    that settles EVERY initial marking at once: a marking is unsafe exactly
    when it dominates a basis element, so one certificate decides infinitely
    many instances and a later query costs a comparison rather than a search.

    Each basis element ships a witness run, compressed through the DAG, and a
    reference to the original target that run covers.
    """
    d = net.dimension
    dag = RunDAG(net)
    active = Antichain(dickson_leq)
    # marking -> (run node, index of the original target it covers)
    witness: dict[Vector, tuple[int, int]] = {}
    pending: deque[Vector] = deque()

    live: set[Vector] = set()

    def admit(marking: Vector, run: int, target_index: int) -> bool:
        if not active.add(marking):
            return False
        live.clear()
        live.update(active.elements)
        witness[marking] = (run, target_index)
        pending.append(marking)
        return True

    for i, target in enumerate(net.targets):
        admit(target, 0, i)

    steps = 0
    while pending:
        marking = pending.popleft()
        if marking not in live:
            continue          # pruned by a strictly smaller marking since admission
        run, target_index = witness[marking]
        for t_index, t in enumerate(net.transitions):
            steps += 1
            if steps > budget.predecessors or len(active) > budget.basis:
                return {'kind': 'unknown', 'reason': 'budget',
                        'stats': {'predecessors': steps, 'basis': len(active)}}
            earlier = t.predecessor(marking)
            admit(earlier, dag.seq(dag.step(t_index), run), target_index)

    basis = sorted(active.elements)
    roots = [witness[b][0] for b in basis]
    nodes, renamed = dag.compact(roots)
    cover = []
    for target in net.targets:
        below = [i for i, b in enumerate(basis) if dickson_leq(b, target)]
        if not below:
            raise AssertionError('a target is not covered by its own frontier')
        cover.append(below[0])
    predecessor_cover = []
    for b in basis:
        row = []
        for t in net.transitions:
            needed = t.predecessor(b)
            hit = [i for i, other in enumerate(basis) if dickson_leq(other, needed)]
            if not hit:
                raise AssertionError('frontier is not backward closed')
            row.append(hit[0])
        predecessor_cover.append(row)
    return {'kind': 'frontier',
            'certificate': {
                'schema': 'forge.wsts.frontier.v1',
                'problem': net.to_dict(),
                'basis': [{'marking': list(b), 'run': renamed[i],
                           'target': witness[b][1]} for i, b in enumerate(basis)],
                'runs': nodes,
                'target_cover': cover,
                'predecessor_cover': predecessor_cover},
            'stats': {'predecessors': steps, 'basis': len(basis),
                      'run_nodes': len(nodes)}}
