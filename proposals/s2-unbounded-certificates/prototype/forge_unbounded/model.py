"""Immutable inputs and serialization. No search or certificate acceptance here."""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
import json
from typing import Any


def nat(x: Any) -> int:
    if type(x) is not int or x < 0:
        raise ValueError("expected a nonnegative integer (not a bool)")
    return x


def rat(x: Any) -> Q:
    if not isinstance(x, list) or len(x) != 2:
        raise ValueError("a rational must be [numerator, positive denominator]")
    a, b = x
    if type(a) is not int or type(b) is not int or b <= 0:
        raise ValueError("invalid rational")
    return Q(a, b)


def encq(x: Q) -> list[int]:
    return [x.numerator, x.denominator]


def vector(x: Any, d: int | None = None) -> tuple[int, ...]:
    if not isinstance(x, list):
        raise ValueError("expected a vector")
    y = tuple(nat(t) for t in x)
    if d is not None and len(y) != d:
        raise ValueError("dimension mismatch")
    return y


@dataclass(frozen=True)
class Petri:
    initial: tuple[int, ...]
    transitions: tuple[tuple[tuple[int, ...], tuple[int, ...]], ...]
    targets: tuple[tuple[int, ...], ...]

    @property
    def d(self) -> int:
        return len(self.initial)

    def data(self) -> dict:
        return {"kind": "petri", "initial": list(self.initial),
                "transitions": [{"pre": list(a), "post": list(b)}
                                for a, b in self.transitions],
                "targets": [list(x) for x in self.targets]}


@dataclass(frozen=True)
class Term:
    coefficient: Q
    powers: tuple[int, ...]


@dataclass(frozen=True)
class PPS:
    polynomials: tuple[tuple[Term, ...], ...]

    @property
    def d(self) -> int:
        return len(self.polynomials)

    def data(self) -> dict:
        return {"kind": "pps", "polynomials": [
            [{"coefficient": encq(t.coefficient), "powers": list(t.powers)}
             for t in row] for row in self.polynomials]}


Problem = Petri | PPS


def parse_problem(data: Any) -> Problem:
    if not isinstance(data, dict):
        raise ValueError("problem must be an object")
    if data.get("kind") == "petri":
        if set(data) != {"kind", "initial", "transitions", "targets"}:
            raise ValueError("unexpected Petri fields")
        initial = vector(data["initial"])
        d = len(initial)
        ts = []
        for t in data["transitions"]:
            if not isinstance(t, dict) or set(t) != {"pre", "post"}:
                raise ValueError("unexpected transition fields")
            ts.append((vector(t["pre"], d), vector(t["post"], d)))
        targets = tuple(vector(t, d) for t in data["targets"])
        return Petri(initial, tuple(ts), targets)
    if data.get("kind") == "pps":
        if set(data) != {"kind", "polynomials"}:
            raise ValueError("unexpected PPS fields")
        rows = data["polynomials"]
        if not isinstance(rows, list) or not rows:
            raise ValueError("a PPS needs at least one coordinate")
        d = len(rows)
        result = []
        for row in rows:
            terms: dict[tuple[int, ...], Q] = {}
            for t in row:
                if not isinstance(t, dict) or set(t) != {"coefficient", "powers"}:
                    raise ValueError("unexpected monomial fields")
                c, e = rat(t["coefficient"]), vector(t["powers"], d)
                if c < 0:
                    raise ValueError("PPS coefficients must be nonnegative")
                terms[e] = terms.get(e, Q(0)) + c
            if sum(terms.values(), Q(0)) > 1:
                raise ValueError("P(1) must be at most 1 in every coordinate")
            result.append(tuple(Term(c, e) for e, c in sorted(terms.items()) if c))
        return PPS(tuple(result))
    raise ValueError("unsupported problem kind")


def subject(p: Problem) -> str:
    """A full canonical encoding, not a lossy pretty-print or a hash."""
    return json.dumps(p.data(), sort_keys=True, separators=(",", ":"))


def validate_object(p: Problem) -> Problem:
    """Do not let direct dataclass construction bypass input validation."""
    return parse_problem(p.data())
