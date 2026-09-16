# PROVENANCE: s1. Nothing else in the collection compresses a witness run, and
# without this a frontier basis element whose witness is a long loop would have
# to ship that loop symbol by symbol.
"""Summaries of transition words, and a hash-consed DAG of the words themselves.

A word's effect on a marking is captured by two vectors: the least marking at
which it is enabled, and what it leaves behind. Composition of summaries is
associative, and repetition has a closed form, so a word like t^1000000 has a
summary of the same size as t and a DAG node of constant size. That is what
lets a certificate quote an astronomically long witness run.

THE DELIBERATE ASYMMETRY. The producer composes in (need, give) coordinates:
what the word takes and what it returns. The checker in certificates.py
recomputes in (need, SIGNED DELTA) coordinates: what the word takes and how
the marking net changes. The two are related by give = need + delta, so they
must agree --- and because the composition rules are written differently in the
two coordinate systems, a transcription error in one of them shows up as a
disagreement rather than being reproduced identically on both sides. s1 made
this choice explicitly; it is the strongest producer/checker separation in the
fourth round, and it is kept.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Any, Iterable

from .nets import Net, Transition
from .orders import Vector, dickson_leq, natural


@dataclass(frozen=True)
class ResourceSummary:
    """A word needs exactly `need`, returns `give`, and leaves surplus alone.

    Monotone in the marking: if it runs from x it runs from anything above x,
    and the results are ordered the same way. That is the only property the
    backward search uses, and it is why a summary may replace its word.
    """
    need: Vector
    give: Vector
    length: int

    @classmethod
    def empty(cls, d: int) -> ResourceSummary:
        return cls((0,) * d, (0,) * d, 0)

    @classmethod
    def step(cls, t: Transition) -> ResourceSummary:
        return cls(t.consume, t.produce, 1)

    def then(self, other: ResourceSummary) -> ResourceSummary:
        """Run self, then other. What the pair needs is what self needs, plus
        whatever of other's need self's output does not already supply."""
        if len(self.need) != len(other.need):
            raise ValueError('dimension mismatch')
        d = len(self.need)
        need = tuple(self.need[i] + max(0, other.need[i] - self.give[i]) for i in range(d))
        give = tuple(other.give[i] + max(0, self.give[i] - other.need[i]) for i in range(d))
        return ResourceSummary(need, give, self.length + other.length)

    def repeat(self, n: int) -> ResourceSummary:
        """n-fold repetition in closed form.

        Each iteration after the first must fund the shortfall max(0, need-give)
        it did not recover, so the total need grows linearly, not exponentially,
        and the n here may be astronomically large at no cost.
        """
        natural(n, 'repeat count')
        if n == 0:
            return self.empty(len(self.need))
        d = len(self.need)
        return ResourceSummary(
            tuple(self.need[i] + (n - 1) * max(0, self.need[i] - self.give[i])
                  for i in range(d)),
            tuple(self.give[i] + (n - 1) * max(0, self.give[i] - self.need[i])
                  for i in range(d)),
            self.length * n)

    def execute(self, state: Vector) -> Vector | None:
        if not dickson_leq(self.need, state):
            return None
        return tuple(state[i] - self.need[i] + self.give[i] for i in range(len(state)))


class RunDAG:
    """Hash-consed words over a net's transitions. Identifiers are never reused.

    `compact` renumbers for output, but only once search is finished. Recycling
    an identifier during the search would let a certificate reference a node
    that meant something else when it was written.
    """

    def __init__(self, net: Net) -> None:
        self.net = net
        self.nodes: list[dict[str, Any]] = [{'op': 'empty'}]
        self.cache: dict[tuple[Any, ...], int] = {('empty',): 0}

    def _intern(self, key: tuple[Any, ...], node: dict[str, Any]) -> int:
        if key not in self.cache:
            self.cache[key] = len(self.nodes)
            self.nodes.append(node)
        return self.cache[key]

    def step(self, t: int) -> int:
        if type(t) is not int or not 0 <= t < len(self.net.transitions):
            raise ValueError('bad transition index')
        return self._intern(('step', t), {'op': 'step', 'transition': t})

    def seq(self, left: int, right: int) -> int:
        if left == 0:
            return right
        if right == 0:
            return left
        return self._intern(('seq', left, right),
                            {'op': 'seq', 'left': left, 'right': right})

    def repeat(self, body: int, count: int) -> int:
        natural(count, 'repeat count')
        if count == 0 or body == 0:
            return 0
        return self._intern(('repeat', body, count),
                            {'op': 'repeat', 'body': body, 'count': count})

    def word(self, letters: Iterable[int]) -> int:
        out = 0
        for t in letters:
            out = self.seq(out, self.step(t))
        return out

    def summarize(self, node: int) -> ResourceSummary:
        d = self.net.dimension
        memo: dict[int, ResourceSummary] = {}

        def walk(i: int) -> ResourceSummary:
            if i in memo:
                return memo[i]
            n = self.nodes[i]
            if n['op'] == 'empty':
                out = ResourceSummary.empty(d)
            elif n['op'] == 'step':
                out = ResourceSummary.step(self.net.transitions[n['transition']])
            elif n['op'] == 'seq':
                out = walk(n['left']).then(walk(n['right']))
            elif n['op'] == 'repeat':
                out = walk(n['body']).repeat(n['count'])
            else:
                raise ValueError('unknown run opcode')
            memo[i] = out
            return out

        return walk(node)

    def compact(self, roots: list[int]) -> tuple[list[dict[str, Any]], list[int]]:
        """Drop unreachable provenance and renumber. Children keep lower indices."""
        keep = {0}
        todo = list(roots)
        while todo:
            i = todo.pop()
            if i in keep:
                continue
            keep.add(i)
            node = self.nodes[i]
            if node['op'] == 'seq':
                todo.extend([node['left'], node['right']])
            elif node['op'] == 'repeat':
                todo.append(node['body'])
        renaming = {old: new for new, old in enumerate(sorted(keep))}
        nodes = []
        for old in sorted(keep):
            node = dict(self.nodes[old])
            for k in ('left', 'right', 'body'):
                if k in node:
                    node[k] = renaming[node[k]]
            nodes.append(node)
        return nodes, [renaming[r] for r in roots]
