"""Small exact sparse Q[x] implementation. No floating point in checking.

The representation is deliberately independent of the search library (SciPy).
Monomials are exponent tuples; zero coefficients are removed canonically.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
from math import comb
from typing import Iterable

@dataclass(frozen=True)
class Poly:
    n: int
    terms: tuple[tuple[tuple[int, ...], Q], ...]

    @staticmethod
    def make(n: int, items: Iterable[tuple[tuple[int, ...], object]]) -> 'Poly':
        if n < 1:
            raise ValueError('At least one variable is required')
        d: dict[tuple[int, ...], Q] = {}
        for m, c in items:
            if len(m) != n or any(type(e) is not int or e < 0 for e in m):
                raise ValueError('Malformed monomial')
            if isinstance(c, float):
                raise TypeError('Float input prohibited: use Fraction or integers')
            d[m] = d.get(m, Q(0)) + Q(c)
        return Poly(n, tuple(sorted((m, c) for m, c in d.items() if c)))

    @staticmethod
    def const(n: int, c: object) -> 'Poly':
        return Poly.make(n, [((0,) * n, c)])

    @staticmethod
    def var(n: int, i: int) -> 'Poly':
        if not 0 <= i < n:
            raise ValueError('Bad variable index')
        return Poly.make(n, [(tuple(int(j == i) for j in range(n)), 1)])

    def coerce(self, other: object) -> 'Poly':
        if isinstance(other, Poly):
            if other.n != self.n:
                raise ValueError('Polynomial dimensions differ')
            return other
        return Poly.const(self.n, other)

    def __add__(self, other: object) -> 'Poly':
        q = self.coerce(other)
        return Poly.make(self.n, self.terms + q.terms)

    __radd__ = __add__

    def __neg__(self) -> 'Poly':
        return Poly.make(self.n, [(m, -c) for m, c in self.terms])

    def __sub__(self, other: object) -> 'Poly':
        return self + -self.coerce(other)

    def __rsub__(self, other: object) -> 'Poly':
        return self.coerce(other) + -self

    def __mul__(self, other: object) -> 'Poly':
        q = self.coerce(other)
        return Poly.make(self.n, [
            (tuple(a+b for a, b in zip(m, k)), c*d)
            for m, c in self.terms for k, d in q.terms])

    __rmul__ = __mul__

    def __pow__(self, k: int) -> 'Poly':
        if type(k) is not int or k < 0:
            raise ValueError('Exponent must be nonnegative integer')
        r, b = Poly.const(self.n, 1), self
        while k:
            if k & 1:
                r = r*b
            b = b*b
            k >>= 1
        return r

    def degree(self) -> int:
        return max((sum(m) for m, _ in self.terms), default=0)

    def multidegree(self) -> tuple[int, ...]:
        return tuple(max((m[i] for m, _ in self.terms), default=0) for i in range(self.n))

    def evaluate(self, xs: tuple[Q, ...]) -> Q:
        if len(xs) != self.n:
            raise ValueError('Bad point dimension')
        out = Q(0)
        for m, c in self.terms:
            for x, e in zip(xs, m):
                c *= Q(x)**e
            out += c
        return out

    def affine_box(self, box: tuple[tuple[Q, Q], ...]) -> 'Poly':
        if len(box) != self.n or any(l >= u for l, u in box):
            raise ValueError('Boxes must have positive rational widths')
        coords = [Poly.const(self.n, l) + (u-l)*Poly.var(self.n, i)
                  for i, (l, u) in enumerate(box)]
        out = Poly.const(self.n, 0)
        for m, c in self.terms:
            t = Poly.const(self.n, c)
            for x, e in zip(coords, m):
                t = t*x**e
            out += t
        return out

    def to_json(self) -> dict:
        return {'n': self.n, 'terms': [[list(m), str(c)] for m, c in self.terms]}

    def lean(self, names: tuple[str, ...]) -> str:
        if len(names) != self.n:
            raise ValueError('Bad variable names')
        if not self.terms:
            return '(0 : ℝ)'
        parts = []
        for m, c in self.terms:
            coef = f'({c.numerator} : ℝ)' if c.denominator == 1 else f'({c.numerator} / {c.denominator} : ℝ)'
            factors = [coef] + [f'({v} ^ {e})' for v, e in zip(names, m) if e]
            parts.append(' * '.join(factors))
        return '(' + ' + '.join(parts) + ')'


def monomials(n: int, total_degree: int) -> list[Poly]:
    return [Poly.make(n, [(m, 1)]) for m in product(range(total_degree+1), repeat=n)
            if sum(m) <= total_degree]


def bernstein_coefficients(p: Poly, box: tuple[tuple[Q, Q], ...]) -> tuple[tuple[int, ...], tuple[Q, ...]]:
    """Search-side power-to-Bernstein conversion; independently replayed by expansion."""
    a = p.affine_box(box)
    ds = a.multidegree()
    vals = []
    for beta in product(*(range(d+1) for d in ds)):
        s = Q(0)
        for alpha, c in a.terms:
            if all(i <= j for i, j in zip(alpha, beta)):
                for i, j, d in zip(alpha, beta, ds):
                    c *= Q(comb(j, i), comb(d, i))
                s += c
        vals.append(s)
    return ds, tuple(vals)


def expand_bernstein(n: int, ds: tuple[int, ...], coeffs: tuple[Q, ...]) -> Poly:
    """Checker-side conversion in the opposite direction, not the search formula."""
    indices = list(product(*(range(d+1) for d in ds)))
    if len(ds) != n or len(indices) != len(coeffs):
        raise ValueError('Malformed Bernstein coefficient vector')
    out = Poly.const(n, 0)
    for beta, c in zip(indices, coeffs):
        t = Poly.const(n, c)
        for i, (b, d) in enumerate(zip(beta, ds)):
            x = Poly.var(n, i)
            t = t*comb(d, b)*x**b*(1-x)**(d-b)
        out += t
    return out
