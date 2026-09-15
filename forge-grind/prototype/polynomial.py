"""Small exact sparse rational polynomial arithmetic, independent of SymPy.

The certificate checkers use only this module and fractions.Fraction. Search may
use floating-point or symbolic libraries; an answer is accepted only after an
exact identity check. Variables are positional; a monomial is an exponent tuple.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
from typing import Iterable

@dataclass(frozen=True)
class Poly:
    n: int
    terms: tuple[tuple[tuple[int, ...], Q], ...]

    @staticmethod
    def make(n: int, terms: dict) -> 'Poly':
        if n < 0:
            raise ValueError('negative variable count')
        out = {}
        for m, c in terms.items():
            m, c = tuple(m), Q(c)
            if len(m) != n or any(type(e) is not int or e < 0 for e in m):
                raise ValueError('invalid monomial')
            if c:
                out[m] = out.get(m, Q(0)) + c
        return Poly(n, tuple(sorted((m, c) for m, c in out.items() if c)))

    @staticmethod
    def const(n: int, c=0) -> 'Poly':
        return Poly.make(n, {(0,) * n: Q(c)})

    @staticmethod
    def var(n: int, i: int) -> 'Poly':
        if not 0 <= i < n:
            raise ValueError('variable index')
        m = [0] * n; m[i] = 1
        return Poly.make(n, {tuple(m): Q(1)})

    @staticmethod
    def mono(n: int, m: tuple) -> 'Poly':
        return Poly.make(n, {m: Q(1)})

    def coerce(self, x) -> 'Poly':
        p = x if isinstance(x, Poly) else Poly.const(self.n, x)
        if p.n != self.n:
            raise ValueError('different polynomial rings')
        return p

    def __add__(self, other) -> 'Poly':
        other = self.coerce(other); d = dict(self.terms)
        for m, c in other.terms:
            d[m] = d.get(m, Q(0)) + c
        return Poly.make(self.n, d)
    __radd__ = __add__

    def __neg__(self) -> 'Poly':
        return Poly.make(self.n, {m: -c for m, c in self.terms})

    def __sub__(self, other) -> 'Poly':
        return self + -self.coerce(other)

    def __rsub__(self, other) -> 'Poly':
        return self.coerce(other) + -self

    def __mul__(self, other) -> 'Poly':
        other = self.coerce(other); d = {}
        for a, u in self.terms:
            for b, v in other.terms:
                m = tuple(x+y for x, y in zip(a, b))
                d[m] = d.get(m, Q(0)) + u*v
        return Poly.make(self.n, d)
    __rmul__ = __mul__

    def __pow__(self, k: int) -> 'Poly':
        if type(k) is not int or k < 0:
            raise ValueError('nonnegative integer exponent required')
        a, b = Poly.const(self.n, 1), self
        while k:
            if k & 1: a = a*b
            k >>= 1
            if k: b = b*b
        return a

    @property
    def degree(self) -> int:
        return max((sum(m) for m, _ in self.terms), default=0)

    def substitute(self, xs: Iterable['Poly']) -> 'Poly':
        xs = tuple(xs)
        if len(xs) != self.n:
            raise ValueError('arity mismatch')
        new_n = xs[0].n if xs else 0
        r = Poly.const(new_n)
        for m, c in self.terms:
            t = Poly.const(new_n, c)
            for x, e in zip(xs, m): t = t * x**e
            r = r+t
        return r

    def evaluate(self, xs: Iterable) -> Q:
        xs = tuple(map(Q, xs))
        if len(xs) != self.n: raise ValueError('arity mismatch')
        return sum((c * prod_q(x**e for x, e in zip(xs, m))
                    for m, c in self.terms), Q(0))

    def json(self) -> dict:
        return {'variables': self.n, 'terms': [
            {'powers': list(m), 'numerator': c.numerator,
             'denominator': c.denominator} for m, c in self.terms]}

    @staticmethod
    def from_json(d: dict) -> 'Poly':
        terms = {}
        for t in d['terms']:
            m = tuple(t['powers'])
            if m in terms: raise ValueError('duplicate monomial')
            terms[m] = Q(t['numerator'], t['denominator'])
        return Poly.make(d['variables'], terms)

    def text(self, names=None) -> str:
        names = names or [f'x{i}' for i in range(self.n)]
        chunks = []
        for m, c in reversed(self.terms):
            s = '*'.join(names[i] + (f'^{e}' if e != 1 else '')
                         for i, e in enumerate(m) if e)
            chunks.append(f'({c})' + ('*'+s if s else ''))
        return ' + '.join(chunks) or '0'


def prod_q(xs):
    r = Q(1)
    for x in xs: r *= x
    return r


def monomials(n: int, degree: int) -> list[tuple[int, ...]]:
    if degree < 0: return []
    return sorted((m for m in product(range(degree+1), repeat=n)
                   if sum(m) <= degree), key=lambda m: (sum(m), m))


def exact_linear_solve(columns: list[Poly], target: Poly) -> list[Q] | None:
    """Rational RREF. Free variables are set to zero. No numeric tolerance."""
    keys = sorted(set(dict(target.terms)).union(
        *(set(dict(p.terms)) for p in columns)))
    m = len(columns)
    coeffs = [dict(p.terms) for p in columns]; rhs = dict(target.terms)
    rows = [[d.get(k, Q(0)) for d in coeffs] + [rhs.get(k, Q(0))]
            for k in keys]
    pivot_row = 0; pivots = []
    for j in range(m):
        s = next((i for i in range(pivot_row, len(rows)) if rows[i][j]), None)
        if s is None: continue
        rows[pivot_row], rows[s] = rows[s], rows[pivot_row]
        t = rows[pivot_row][j]
        rows[pivot_row] = [x/t for x in rows[pivot_row]]
        for i in range(len(rows)):
            if i != pivot_row and rows[i][j]:
                t = rows[i][j]
                rows[i] = [x-t*y for x, y in zip(rows[i], rows[pivot_row])]
        pivots.append(j); pivot_row += 1
        if pivot_row == len(rows): break
    if any(not any(r[:m]) and r[m] for r in rows): return None
    x = [Q(0)] * m
    for i, j in enumerate(pivots): x[j] = rows[i][m]
    return x
