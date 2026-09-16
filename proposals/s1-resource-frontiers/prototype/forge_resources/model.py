"""Producer-side semantics. The independent checker does not import this file."""
from __future__ import annotations
from dataclasses import dataclass
from typing import Any, Iterable

Vector = tuple[int, ...]


def natural(x: Any) -> int:
    if type(x) is not int or x < 0:
        raise ValueError("expected a natural number (Boolean values are not integers here)")
    return x


def vector(xs: Any, d: int) -> Vector:
    if not isinstance(xs, (list, tuple)) or len(xs) != d:
        raise ValueError("vector dimension mismatch")
    return tuple(natural(x) for x in xs)


def leq(a: Vector, b: Vector) -> bool:
    if len(a) != len(b):
        raise ValueError("dimension mismatch")
    return all(x <= y for x, y in zip(a, b))


@dataclass(frozen=True)
class Transition:
    name: str
    consume: Vector
    produce: Vector

    def fire(self, state: Vector) -> Vector | None:
        if not leq(self.consume, state):
            return None
        return tuple(x - c + p for x, c, p in zip(state, self.consume, self.produce))

    def predecessor(self, goal: Vector) -> Vector:
        return tuple(c + max(0, b - p)
                     for c, p, b in zip(self.consume, self.produce, goal))


@dataclass(frozen=True)
class Net:
    dimension: int
    transitions: tuple[Transition, ...]
    targets: tuple[Vector, ...]

    @classmethod
    def from_dict(cls, obj: dict[str, Any]) -> Net:
        if type(obj) is not dict or set(obj) != {"kind", "dimension", "transitions", "targets"}:
            raise ValueError("unsupported net fields")
        if obj["kind"] != "pt-net-coverability":
            raise ValueError("only ordinary place/transition nets are supported")
        d = natural(obj["dimension"])
        if type(obj["transitions"]) is not list or type(obj["targets"]) is not list:
            raise ValueError("transitions and targets must be lists")
        ts = []
        for t in obj["transitions"]:
            if type(t) is not dict or set(t) != {"name", "consume", "produce"}:
                raise ValueError("unsupported transition: guards, resets, and inhibitor arcs are refused")
            if type(t["name"]) is not str:
                raise ValueError("transition name must be a string")
            ts.append(Transition(t["name"], vector(t["consume"], d), vector(t["produce"], d)))
        if len({t.name for t in ts}) != len(ts):
            raise ValueError("transition names must be distinct")
        return cls(d, tuple(ts), tuple(vector(b, d) for b in obj["targets"]))

    def to_dict(self) -> dict[str, Any]:
        return {"kind": "pt-net-coverability", "dimension": self.dimension,
                "transitions": [{"name": t.name, "consume": list(t.consume),
                                 "produce": list(t.produce)} for t in self.transitions],
                "targets": [list(b) for b in self.targets]}


@dataclass(frozen=True)
class ResourceSummary:
    """A word consumes exactly `need` and returns `give`, leaving surplus untouched."""
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
        if len(self.need) != len(other.need):
            raise ValueError("dimension mismatch")
        need = tuple(c + max(0, a - p)
                     for c, p, a in zip(self.need, self.give, other.need))
        give = tuple(b + max(0, p - a)
                     for p, a, b in zip(self.give, other.need, other.give))
        return ResourceSummary(need, give, self.length + other.length)

    def repeat(self, n: int) -> ResourceSummary:
        natural(n)
        if n == 0:
            return self.empty(len(self.need))
        return ResourceSummary(
            tuple(c + (n - 1) * max(0, c - p) for c, p in zip(self.need, self.give)),
            tuple(p + (n - 1) * max(0, p - c) for c, p in zip(self.need, self.give)),
            self.length * n)

    def execute(self, state: Vector) -> Vector | None:
        if not leq(self.need, state):
            return None
        return tuple(x - c + p for x, c, p in zip(state, self.need, self.give))


class RunDAG:
    def __init__(self, net: Net) -> None:
        self.net = net
        self.nodes: list[dict[str, Any]] = [{"op": "empty"}]
        self.cache: dict[tuple[Any, ...], int] = {("empty",): 0}

    def _intern(self, key: tuple[Any, ...], node: dict[str, Any]) -> int:
        if key not in self.cache:
            self.cache[key] = len(self.nodes)
            self.nodes.append(node)
        return self.cache[key]

    def step(self, t: int) -> int:
        if type(t) is not int or not 0 <= t < len(self.net.transitions):
            raise ValueError("bad transition index")
        return self._intern(("step", t), {"op": "step", "transition": t})

    def seq(self, left: int, right: int) -> int:
        if left == 0:
            return right
        if right == 0:
            return left
        return self._intern(("seq", left, right), {"op": "seq", "left": left, "right": right})

    def repeat(self, body: int, count: int) -> int:
        natural(count)
        return self._intern(("repeat", body, count),
                            {"op": "repeat", "body": body, "count": count})

    def word(self, letters: Iterable[int]) -> int:
        out = 0
        for t in letters:
            out = self.seq(out, self.step(t))
        return out

    def compact(self, roots: list[int]) -> tuple[list[dict[str, Any]], list[int]]:
        """Discard dead provenance without recycling any identifier during search."""
        keep = {0}
        todo = list(roots)
        while todo:
            i = todo.pop()
            if i in keep:
                continue
            keep.add(i)
            node = self.nodes[i]
            if node["op"] == "seq":
                todo.extend([node["left"], node["right"]])
            elif node["op"] == "repeat":
                todo.append(node["body"])
        renaming = {old: new for new, old in enumerate(sorted(keep))}
        nodes = []
        for old in sorted(keep):
            node = dict(self.nodes[old])
            for k in ("left", "right", "body"):
                if k in node:
                    node[k] = renaming[node[k]]
            nodes.append(node)
        return nodes, [renaming[r] for r in roots]
