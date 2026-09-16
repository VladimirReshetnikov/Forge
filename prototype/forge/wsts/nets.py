# PROVENANCE: s1's place/transition nets, s3's finite-control counter systems,
# s4's matrix-update systems and lossy FIFO channels. Four model languages, one
# interface: each supplies a predecessor rule and an order, and search.py does
# not know which of them it is driving.
"""The model families the merged backward search runs over.

Each family exposes the same three things:

  states        an order on configurations (from orders.py)
  step          forward firing, used only to replay a claimed counterexample
  predecessors  the minimal configurations from which one transition reaches
                a given upward-closed target

`predecessors` returns a LIST because s4's matrix updates have no single least
predecessor: a transition x |-> produce + A (x - consume) can require several
incomparable minima, and returning one of them would make the search unsound
rather than merely incomplete. The vector-addition families return a singleton,
which is the special case A = I that s1 and s3 both restrict themselves to.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import product
from typing import Any, Iterable, Sequence

from .orders import Vector, dickson_leq, higman_leq, natural, predecessor, vector


# --------------------------------------------------------------------------
# s1: ordinary place/transition nets.
# --------------------------------------------------------------------------
@dataclass(frozen=True)
class Transition:
    name: str
    consume: Vector
    produce: Vector

    def fire(self, state: Vector) -> Vector | None:
        if not dickson_leq(self.consume, state):
            return None
        return tuple(state[i] - self.consume[i] + self.produce[i]
                     for i in range(len(state)))

    def predecessor(self, target: Vector) -> Vector:
        return predecessor(self.consume, self.produce, target)


@dataclass(frozen=True)
class Net:
    """A place/transition net together with the targets to be covered.

    No guards, no resets, no inhibitor arcs. That restriction is what keeps
    coverability decidable, and `from_dict` refuses the extra fields by name
    rather than ignoring them: silently dropping an inhibitor arc would turn
    an undecidable question into a confidently wrong answer.
    """
    dimension: int
    transitions: tuple[Transition, ...]
    targets: tuple[Vector, ...]

    @classmethod
    def from_dict(cls, obj: dict[str, Any]) -> Net:
        if type(obj) is not dict or set(obj) != {'kind', 'dimension', 'transitions', 'targets'}:
            raise ValueError('unsupported net fields')
        if obj['kind'] != 'pt-net-coverability':
            raise ValueError('only ordinary place/transition nets are supported')
        d = natural(obj['dimension'], 'dimension')
        if type(obj['transitions']) is not list or type(obj['targets']) is not list:
            raise ValueError('transitions and targets must be lists')
        ts = []
        for t in obj['transitions']:
            if type(t) is not dict or set(t) != {'name', 'consume', 'produce'}:
                raise ValueError('unsupported transition: guards, resets and '
                                 'inhibitor arcs are refused, not ignored')
            if type(t['name']) is not str:
                raise ValueError('transition name must be a string')
            ts.append(Transition(t['name'], vector(t['consume'], d, 'consume'),
                                 vector(t['produce'], d, 'produce')))
        if len({t.name for t in ts}) != len(ts):
            raise ValueError('transition names must be distinct')
        return cls(d, tuple(ts), tuple(vector(b, d, 'target') for b in obj['targets']))

    def to_dict(self) -> dict[str, Any]:
        return {'kind': 'pt-net-coverability', 'dimension': self.dimension,
                'transitions': [{'name': t.name, 'consume': list(t.consume),
                                 'produce': list(t.produce)} for t in self.transitions],
                'targets': [list(b) for b in self.targets]}


# --------------------------------------------------------------------------
# s3: finite-control counter systems, and the multi-ray initial families.
# --------------------------------------------------------------------------
@dataclass(frozen=True)
class Edge:
    source: int
    target: int
    consume: Vector
    produce: Vector


@dataclass(frozen=True)
class Vass:
    """A vector addition system with a finite control graph.

    s1's nets are the one-control case. They are kept separate rather than
    encoded as `controls == 1`, because s1's question is different: it asks for
    the frontier over ALL initial markings, and s3 asks about a family of them.
    Merging the models would not have merged the questions.
    """
    controls: int
    dimension: int
    edges: tuple[Edge, ...]

    def incoming(self) -> list[list[int]]:
        table: list[list[int]] = [[] for _ in range(self.controls)]
        for i, edge in enumerate(self.edges):
            table[edge.target].append(i)
        return table

    def predecessors(self, edge_index: int, target: tuple[int, Vector]
                     ) -> list[tuple[int, Vector]]:
        control, vec = target
        edge = self.edges[edge_index]
        if edge.target != control:
            return []
        return [(edge.source, predecessor(edge.consume, edge.produce, vec))]


@dataclass(frozen=True)
class InitialFamily:
    """base + sum_j n_j * ray_j, over all n in N^k: an infinite initial set.

    A counterexample must name the n it used, so the checker can rebuild the
    exact starting configuration and replay the run in it. `witness` searches
    for one; it is producer-side, and being incomplete would cost completeness,
    not soundness.
    """
    control: int
    base: Vector
    rays: tuple[Vector, ...]

    def value(self, parameters: Sequence[int]) -> Vector:
        if len(parameters) != len(self.rays):
            raise ValueError('wrong number of ray parameters')
        return tuple(self.base[i] + sum(n * ray[i] for n, ray in zip(parameters, self.rays))
                     for i in range(len(self.base)))

    def witness(self, threshold: Vector) -> list[int] | None:
        """A uniform multiplier reaching `threshold`, or None if no ray helps.

        Uniform because a coordinate with no positive ray can never be raised,
        and a coordinate that can be raised is raised by every ray together.
        A returned list is a claim the caller must check by calling `value`;
        returning None is a failure to find one, NOT a proof that none exists.
        """
        common = 0
        for i, bound in enumerate(threshold):
            shortfall = bound - self.base[i]
            if shortfall <= 0:
                continue
            slope = sum(ray[i] for ray in self.rays)
            if slope == 0:
                return None
            common = max(common, -(-shortfall // slope))
        return [common] * len(self.rays)


# --------------------------------------------------------------------------
# s4: matrix-update transitions, where the least predecessor is not unique.
# --------------------------------------------------------------------------
@dataclass(frozen=True)
class MatrixTransition:
    """x |-> produce + A (x - consume), enabled when x >= consume.

    A is a nonnegative integer matrix, so the update is monotone, which is what
    the backward search needs. Resets are A with a zero row, transfers are A
    with a column moved, and duplication is a column with two ones --- none of
    which is expressible as a vector addition, and all of which break the
    "unique least predecessor" property that s1 and s3 rely on.
    """
    source: int
    target: int
    consume: Vector
    matrix: tuple[Vector, ...]
    produce: Vector

    def fire(self, state: Vector) -> Vector | None:
        d = len(state)
        if not dickson_leq(self.consume, state):
            return None
        surplus = [state[i] - self.consume[i] for i in range(d)]
        return tuple(self.produce[j] + sum(self.matrix[j][i] * surplus[i] for i in range(d))
                     for j in range(d))

    def demand(self, target: Vector) -> list[int]:
        """What the surplus must supply, once `produce` is accounted for."""
        return [max(0, target[j] - self.produce[j]) for j in range(len(target))]

    def caps(self, target: Vector) -> list[int] | None:
        """A box outside which no surplus is minimal, or None if unreachable.

        For each coordinate i, a surplus above max_j ceil(demand_j / A[j][i])
        is more than any single row can need from i alone, so a minimal
        solution never exceeds it. A coordinate j with positive demand and an
        all-zero row admits no solution at all.
        """
        d = len(target)
        demand = self.demand(target)
        for j in range(d):
            if demand[j] > 0 and not any(self.matrix[j][i] > 0 for i in range(d)):
                return None
        bound = [0] * d
        for i in range(d):
            for j in range(d):
                if self.matrix[j][i] > 0:
                    bound[i] = max(bound[i], -(-demand[j] // self.matrix[j][i]))
        return bound

    def minimal_surpluses(self, target: Vector) -> list[Vector] | None:
        """The minimal z >= 0 with A z >= demand, by exhaustive box search.

        Exponential in the dimension and honest about it: s4 shipped a
        branch-and-bound partition receipt precisely so a CHECKER would not
        have to do this. The search may do it; the checker in certificates.py
        replays the partition instead.
        """
        d = len(target)
        bound = self.caps(target)
        if bound is None:
            return None
        demand = self.demand(target)
        cells = 1
        for b in bound:
            cells *= b + 1
            if cells > 1_000_000:
                raise ValueError('surplus box exceeds the enumeration budget')
        feasible = []
        for z in product(*[range(b + 1) for b in bound]):
            if all(sum(self.matrix[j][i] * z[i] for i in range(d)) >= demand[j]
                   for j in range(d)):
                feasible.append(z)
        minimal = [z for z in feasible
                   if not any(other != z and dickson_leq(other, z) for other in feasible)]
        return sorted(minimal)

    def predecessors(self, target: tuple[int, Vector]) -> list[tuple[int, Vector]]:
        control, vec = target
        if self.target != control:
            return []
        minima = self.minimal_surpluses(vec)
        if minima is None:
            return []
        d = len(vec)
        return [(self.source, tuple(self.consume[i] + z[i] for i in range(d)))
                for z in minima]


@dataclass(frozen=True)
class ChannelTransition:
    """A lossy FIFO operation. Configurations are tuples of words.

    Lossiness is not a separate rule: it is the Higman order itself. A
    configuration stands for every configuration obtained by dropping symbols,
    so the upward-closed sets are exactly the loss-closed ones and the ordinary
    backward search already handles message loss.
    """
    source: int
    target: int
    op: str          # 'send' | 'recv' | 'tau'
    channel: int
    symbol: str

    def predecessors(self, target: tuple[int, tuple[str, ...]]
                     ) -> list[tuple[int, tuple[str, ...]]]:
        control, words = target
        if self.target != control:
            return []
        out = list(words)
        current = words[self.channel]
        if self.op == 'send':
            # Only the LAST position can hold the symbol just appended.
            if current and current[-1] == self.symbol:
                out[self.channel] = current[:-1]
        elif self.op == 'recv':
            out[self.channel] = self.symbol + current
        return [(self.source, tuple(out))]
