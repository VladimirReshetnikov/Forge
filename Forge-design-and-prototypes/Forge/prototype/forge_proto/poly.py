"""Small exact sparse Q[x_0,...,x_(n-1)] substrate.

The certificate checkers use only this module and the Python standard library.
This is a prototype mathematical checker, NOT a Lean kernel implementation.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
from math import comb
from typing import Iterable, Sequence


@dataclass(frozen=True)
class Poly:
    n: int
    terms: tuple[tuple[tuple[int, ...], Q], ...]

    def __post_init__(self) -> None:
        if type(self.n) is not int or self.n < 1:
            raise ValueError("a positive variable count is required")
        last = None
        for exponent, coefficient in self.terms:
            if len(exponent) != self.n or any(type(e) is not int or e < 0 for e in exponent):
                raise ValueError("invalid exponent")
            if not isinstance(coefficient, Q) or not coefficient:
                raise ValueError("coefficients must be nonzero exact Fractions")
            if last is not None and exponent <= last:
                raise ValueError("terms must be sorted and unique")
            last = exponent

    @classmethod
    def make(cls, n: int, terms: Iterable[tuple[Sequence[int], Q | int]]) -> Poly:
        d: dict[tuple[int, ...], Q] = {}
        for exponent, coefficient in terms:
            e = tuple(exponent)
            if isinstance(coefficient, float):
                raise TypeError("floating-point coefficients are not accepted")
            d[e] = d.get(e, Q(0)) + Q(coefficient)
        return cls(n, tuple(sorted((e, c) for e, c in d.items() if c)))

    @classmethod
    def constant(cls, n: int, value: Q | int) -> Poly:
        return cls.make(n, [((0,) * n, value)])

    @classmethod
    def variable(cls, n: int, index: int) -> Poly:
        if not 0 <= index < n:
            raise ValueError("variable index out of range")
        e = [0] * n
        e[index] = 1
        return cls.make(n, [(e, 1)])

    def coerce(self, other: Poly | int | Q) -> Poly:
        if not isinstance(other, Poly):
            return Poly.constant(self.n, other)
        if self.n != other.n:
            raise ValueError("polynomial arity mismatch")
        return other

    def __add__(self, other: Poly | int | Q) -> Poly:
        p = self.coerce(other)
        return Poly.make(self.n, (*self.terms, *p.terms))

    __radd__ = __add__

    def __neg__(self) -> Poly:
        return Poly.make(self.n, ((e, -c) for e, c in self.terms))

    def __sub__(self, other: Poly | int | Q) -> Poly:
        return self + (-self.coerce(other))

    def __rsub__(self, other: Poly | int | Q) -> Poly:
        return self.coerce(other) - self

    def __mul__(self, other: Poly | int | Q) -> Poly:
        p = self.coerce(other)
        return Poly.make(self.n, ((tuple(a + b for a, b in zip(e, f)), c * d)
                                 for e, c in self.terms for f, d in p.terms))

    __rmul__ = __mul__

    def __pow__(self, exponent: int) -> Poly:
        if type(exponent) is not int or exponent < 0:
            raise ValueError("nonnegative integer power required")
        p, result = self, Poly.constant(self.n, 1)
        while exponent:
            if exponent & 1:
                result = result * p
            p = p * p
            exponent //= 2
        return result

    def evaluate(self, values: Sequence[Q | int]) -> Q:
        if len(values) != self.n:
            raise ValueError("evaluation arity mismatch")
        vals = tuple(Q(v) for v in values)
        return sum((c * _prod(v ** k for v, k in zip(vals, e))
                    for e, c in self.terms), Q(0))

    def substitute(self, values: Sequence[Poly]) -> Poly:
        if len(values) != self.n or not values or any(p.n != values[0].n for p in values):
            raise ValueError("substitution arity mismatch")
        out = Poly.constant(values[0].n, 0)
        for e, c in self.terms:
            term = Poly.constant(out.n, c)
            for p, k in zip(values, e):
                term *= p ** k
            out += term
        return out

    def degrees(self) -> tuple[int, ...]:
        return tuple(max((e[i] for e, _ in self.terms), default=0) for i in range(self.n))

    def total_degree(self) -> int:
        return max((sum(e) for e, _ in self.terms), default=0)

    def coefficient(self, exponent: Sequence[int]) -> Q:
        return dict(self.terms).get(tuple(exponent), Q(0))

    def to_json(self) -> dict:
        return {"variables": self.n, "terms": [[list(e), str(c)] for e, c in self.terms]}

    @classmethod
    def from_json(cls, value: dict) -> Poly:
        # Construction through the canonical constructor rejects duplicate,
        # zero, or unsorted entries rather than silently fixing certificates.
        return cls(value["variables"], tuple((tuple(e), Q(c)) for e, c in value["terms"]))

    def __str__(self) -> str:
        if not self.terms:
            return "0"
        out = []
        for e, c in reversed(self.terms):
            factors = [f"x{i}" + (f"^{k}" if k != 1 else "") for i, k in enumerate(e) if k]
            out.append(str(c) + ("*" + "*".join(factors) if factors else ""))
        return " + ".join(out).replace("+ -", "- ")


def _prod(values: Iterable[Q]) -> Q:
    result = Q(1)
    for v in values:
        result *= v
    return result


def monomials(n: int, degree: int) -> list[Poly]:
    return [Poly.make(n, [(e, 1)]) for e in product(range(degree + 1), repeat=n)
            if sum(e) <= degree]


def bernstein_coefficients(p: Poly, box: Sequence[tuple[Q, Q]]) -> tuple[Q, ...]:
    """Exact tensor-product Bernstein coefficients on a rational box."""
    if len(box) != p.n or any(Q(a) >= Q(b) for a, b in box):
        raise ValueError("nonempty full-dimensional rational box required")
    variables = [Poly.variable(p.n, i) for i in range(p.n)]
    normalized = p.substitute([Q(a) + (Q(b) - Q(a)) * t
                               for (a, b), t in zip(box, variables)])
    degrees = p.degrees()
    coefficients = []
    for alpha in product(*(range(d + 1) for d in degrees)):
        value = Q(0)
        for beta, c in normalized.terms:
            if all(b <= a for a, b in zip(alpha, beta)):
                value += c * _prod(Q(comb(a, b), comb(d, b))
                                   for a, b, d in zip(alpha, beta, degrees))
        coefficients.append(value)
    return tuple(coefficients)
