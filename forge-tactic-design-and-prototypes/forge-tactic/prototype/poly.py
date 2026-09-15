"""Sparse multivariate polynomials over Q. No symbolic evaluation or float input.

The search engines are untrusted. This module supplies exact operations to the
standalone experimental checkers; it is not a formally verified Lean checker.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
from math import comb
from typing import Iterable, Mapping

Exp = tuple[int, ...]

def rational(x: int | Q) -> Q:
    if type(x) is int or isinstance(x, Q):
        return Q(x)
    raise TypeError("polynomial coefficients must be int or Fraction, not floats")

@dataclass(frozen=True)
class Poly:
    n: int
    terms: tuple[tuple[Exp, Q], ...]

    def __post_init__(self) -> None:
        if type(self.n) is not int or self.n < 1:
            raise ValueError("positive variable count required")
        prev = None
        for e, c in self.terms:
            if len(e) != self.n or any(type(k) is not int or k < 0 for k in e):
                raise ValueError("invalid exponent")
            if not isinstance(c, Q) or not c or (prev is not None and e <= prev):
                raise ValueError("terms must be nonzero, rational, uniquely sorted")
            prev = e

    @staticmethod
    def make(n: int, data: Mapping[Exp, int | Q]) -> Poly:
        out = []
        for e, raw in data.items():
            c = rational(raw)  # Validate even coefficients that happen to be zero.
            if len(e) != n or any(type(k) is not int or k < 0 for k in e):
                raise ValueError("invalid exponent")
            if c:
                out.append((e, c))
        return Poly(n, tuple(sorted(out)))

    @staticmethod
    def const(n: int, c: int | Q) -> Poly:
        return Poly.make(n, {(0,) * n: rational(c)})

    @staticmethod
    def var(n: int, i: int) -> Poly:
        if not 0 <= i < n:
            raise ValueError("variable index outside arity")
        e = tuple(int(j == i) for j in range(n))
        return Poly.make(n, {e: Q(1)})

    @staticmethod
    def monomial(n: int, e: Exp, c: int | Q = 1) -> Poly:
        return Poly.make(n, {e: rational(c)})

    def coerce(self, other: Poly | int | Q) -> Poly:
        p = other if isinstance(other, Poly) else Poly.const(self.n, rational(other))
        if p.n != self.n:
            raise ValueError("incompatible polynomial arities")
        return p

    def __add__(self, other: Poly | int | Q) -> Poly:
        p = self.coerce(other)
        out = dict(self.terms)
        for e, c in p.terms:
            out[e] = out.get(e, Q(0)) + c
        return Poly.make(self.n, out)

    __radd__ = __add__

    def __neg__(self) -> Poly:
        return Poly(self.n, tuple((e, -c) for e, c in self.terms))

    def __sub__(self, other: Poly | int | Q) -> Poly:
        return self + -self.coerce(other)

    def __rsub__(self, other: Poly | int | Q) -> Poly:
        return self.coerce(other) + -self

    def __mul__(self, other: Poly | int | Q) -> Poly:
        p = self.coerce(other)
        out: dict[Exp, Q] = {}
        for a, c in self.terms:
            for b, d in p.terms:
                e = tuple(x + y for x, y in zip(a, b))
                out[e] = out.get(e, Q(0)) + c*d
        return Poly.make(self.n, out)

    __rmul__ = __mul__

    def __pow__(self, k: int) -> Poly:
        if type(k) is not int or k < 0:
            raise ValueError("nonnegative integer exponent required")
        result = Poly.const(self.n, 1)
        p = self
        while k:
            if k & 1:
                result = result*p
            p = p*p
            k //= 2
        return result

    def evaluate(self, point: Iterable[int | Q]) -> Q:
        a = tuple(rational(x) for x in point)
        if len(a) != self.n:
            raise ValueError("point dimension mismatch")
        return sum((c * _prod(x**k for x, k in zip(a, e))
                    for e, c in self.terms), Q(0))

    @property
    def degree(self) -> int:
        return max((sum(e) for e, _ in self.terms), default=0)

    @property
    def degrees(self) -> Exp:
        return tuple(max((e[j] for e, _ in self.terms), default=0)
                     for j in range(self.n))

    def substitute(self, images: tuple[Poly, ...]) -> Poly:
        if len(images) != self.n or not images:
            raise ValueError("substitution arity mismatch")
        m = images[0].n
        if any(p.n != m for p in images):
            raise ValueError("substitution codomain mismatch")
        result = Poly.const(m, 0)
        for e, c in self.terms:
            term = Poly.const(m, c)
            for p, k in zip(images, e):
                term *= p**k
            result += term
        return result

    def to_json(self) -> dict:
        return {"n": self.n,
                "terms": [[list(e), str(c)] for e, c in self.terms]}

    def __str__(self) -> str:
        return " + ".join(f"({c})*" + "*".join(
            f"x{j}^{k}" for j, k in enumerate(e) if k)
            for e, c in self.terms) if self.terms else "0"


def _prod(xs: Iterable) -> Q:
    a = Q(1)
    for x in xs:
        a *= x
    return a


def monomials(n: int, max_degree: int) -> tuple[Poly, ...]:
    if type(n) is not int or n < 1 or type(max_degree) is not int or max_degree < 0:
        raise ValueError("invalid monomial bounds")
    # Enumerate only weak compositions, not a (degree+1)^n enclosing grid.
    def compositions(total: int, parts: int):
        if parts == 1:
            yield (total,)
        else:
            for first in range(total+1):
                for tail in compositions(total-first, parts-1):
                    yield (first,)+tail
    return tuple(Poly.monomial(n,e) for d in range(max_degree+1)
                 for e in compositions(d,n))


def unit_transform(p: Poly, box: tuple[tuple[Q, Q], ...]) -> Poly:
    if len(box) != p.n or any(not isinstance(l, Q) or not isinstance(u, Q)
                              or l >= u for l, u in box):
        raise ValueError("box must have rational endpoints with lower < upper")
    return p.substitute(tuple(l+(u-l)*Poly.var(p.n, j)
                             for j, (l, u) in enumerate(box)))


def bernstein_coefficients(p: Poly, box: tuple[tuple[Q, Q], ...]) -> tuple[Q, ...]:
    """Power-to-tensor-Bernstein conversion after affine box transformation."""
    t = unit_transform(p, box)
    ds = p.degrees
    result = []
    for i in product(*(range(d+1) for d in ds)):
        result.append(sum((c*_prod(Q(comb(ij, a), comb(dj, a))
                                      for ij, dj, a in zip(i, ds, e))
                           for e, c in t.terms if all(a <= b for a, b in zip(e, i))), Q(0)))
    return tuple(result)
