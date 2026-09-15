"""Small exact polynomial kernel. No floating-point arithmetic or third-party imports.

Search modules are deliberately separate. This file checks identities over Q;
it is not a formally verified kernel and is not a replacement for Lean replay.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
from math import comb
from typing import Iterable, Sequence

Exp = tuple[int, ...]

@dataclass(frozen=True)
class Poly:
    n: int
    terms: tuple[tuple[Exp, Q], ...]

    def __post_init__(self) -> None:
        if type(self.n) is not int or self.n < 1:
            raise ValueError('positive variable count required')
        previous = None
        for exponent, coefficient in self.terms:
            if len(exponent) != self.n or any(type(e) is not int or e < 0 for e in exponent):
                raise ValueError('invalid exponent')
            if not isinstance(coefficient, Q) or not coefficient:
                raise ValueError('canonical, nonzero rational coefficients required')
            if previous is not None and exponent <= previous:
                raise ValueError('terms must be sorted and unique')
            previous = exponent

    @staticmethod
    def make(n: int, terms: Iterable[tuple[Exp, Q | int]]) -> Poly:
        d: dict[Exp, Q] = {}
        for e, c in terms:
            d[e] = d.get(e, Q(0)) + Q(c)
        return Poly(n, tuple(sorted((e, c) for e, c in d.items() if c)))

    @staticmethod
    def const(n: int, c: Q | int) -> Poly:
        return Poly.make(n, [((0,) * n, c)])

    @staticmethod
    def var(n: int, i: int) -> Poly:
        if not 0 <= i < n:
            raise ValueError('variable out of range')
        return Poly.make(n, [(tuple(int(j == i) for j in range(n)), 1)])

    @property
    def degree(self) -> int:
        return max((sum(e) for e, _ in self.terms), default=0)

    def _coerce(self, other: Poly | Q | int) -> Poly:
        if isinstance(other, Poly):
            if self.n != other.n:
                raise ValueError('different polynomial rings')
            return other
        return Poly.const(self.n, other)

    def __add__(self, other: Poly | Q | int) -> Poly:
        p = self._coerce(other)
        return Poly.make(self.n, self.terms + p.terms)

    __radd__ = __add__

    def __neg__(self) -> Poly:
        return Poly.make(self.n, ((e, -c) for e, c in self.terms))

    def __sub__(self, other: Poly | Q | int) -> Poly:
        return self + (-self._coerce(other))

    def __rsub__(self, other: Poly | Q | int) -> Poly:
        return self._coerce(other) - self

    def __mul__(self, other: Poly | Q | int) -> Poly:
        p = self._coerce(other)
        return Poly.make(self.n, ((tuple(a+b for a,b in zip(e,f)), c*d)
            for e,c in self.terms for f,d in p.terms))

    __rmul__ = __mul__

    def __pow__(self, k: int) -> Poly:
        if type(k) is not int or k < 0:
            raise ValueError('nonnegative integer exponent required')
        ans, base = Poly.const(self.n, 1), self
        while k:
            if k & 1:
                ans = ans * base
            base = base * base
            k //= 2
        return ans

    def evaluate(self, values: Sequence[Q | int]) -> Q:
        if len(values) != self.n:
            raise ValueError('wrong point dimension')
        total = Q(0)
        for ex, c in self.terms:
            for a, k in zip(values, ex):
                c *= Q(a) ** k
            total += c
        return total

    def substitute(self, values: Sequence[Poly]) -> Poly:
        if len(values) != self.n or not values:
            raise ValueError('wrong substitution dimension')
        m = values[0].n
        if any(p.n != m for p in values):
            raise ValueError('inconsistent substitution codomain')
        total = Poly.const(m, 0)
        for ex, c in self.terms:
            term = Poly.const(m, c)
            for p, k in zip(values, ex):
                term = term * p**k
            total += term
        return total

    def lean(self, names: Sequence[str]) -> str:
        """Render already structured polynomials, never parse/evaluate source text."""
        if len(names) != self.n:
            raise ValueError('wrong name dimension')
        if not self.terms:
            return '0'
        chunks = []
        for ex, c in reversed(self.terms):
            coef = str(c.numerator) if c.denominator == 1 else f'({c.numerator} / {c.denominator})'
            factors = [f'({coef})']
            factors += [f'({v})' if k == 1 else f'({v}) ^ {k}'
                        for v, k in zip(names, ex) if k]
            chunks.append(' * '.join(factors))
        return ' + '.join(chunks)

    def json(self) -> dict:
        return {'n': self.n, 'terms': [[list(e), str(c)] for e,c in self.terms]}


def monomial_exponents(n: int, degree: int) -> list[Exp]:
    if n < 1 or degree < 0:
        raise ValueError('invalid monomial bounds')
    return sorted((e for e in product(range(degree+1), repeat=n)
                   if sum(e) <= degree), key=lambda e: (sum(e), e))


def solve_linear(a: Sequence[Sequence[Q | int]], b: Sequence[Q | int],
                 columns: int) -> list[Q] | None:
    """Exact RREF; set free parameters to zero. None means inconsistent."""
    if len(a) != len(b) or columns < 0 or any(len(r) != columns for r in a):
        raise ValueError('matrix shape mismatch')
    rows = [[Q(v) for v in r] + [Q(rhs)] for r,rhs in zip(a,b)]
    rank = 0
    pivots = []
    for col in range(columns):
        pivot = next((r for r in range(rank,len(rows)) if rows[r][col]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        q = rows[rank][col]
        rows[rank] = [x/q for x in rows[rank]]
        for r in range(len(rows)):
            if r != rank and rows[r][col]:
                q = rows[r][col]
                rows[r] = [x-q*y for x,y in zip(rows[r],rows[rank])]
        pivots.append(col)
        rank += 1
    if any(not any(r[:-1]) and r[-1] for r in rows):
        return None
    ans = [Q(0)] * columns
    for r,c in enumerate(pivots):
        ans[c] = rows[r][-1]
    return ans


def polynomial_linear_combination(target: Poly, basis: Sequence[Poly]) -> list[Q] | None:
    if any(p.n != target.n for p in basis):
        raise ValueError('inconsistent dimensions')
    support = sorted(set(e for p in [target, *basis] for e,_ in p.terms))
    td, bd = dict(target.terms), [dict(p.terms) for p in basis]
    return solve_linear([[d.get(e,0) for d in bd] for e in support],
                        [td.get(e,0) for e in support],len(basis))
