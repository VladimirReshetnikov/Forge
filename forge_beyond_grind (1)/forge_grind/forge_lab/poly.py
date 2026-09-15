"""Sparse rational polynomials and small exact certificate checkers.

This module has no dependency on a numerical optimizer or on SymPy.
Its successful checks are mathematical certificates for the stated polynomial
fragment, not Lean-kernel-checked theorems. Domain assumptions remain explicit.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
from math import comb
from typing import Iterable

Mon = tuple[int, ...]

@dataclass(frozen=True)
class Poly:
    n: int
    terms: tuple[tuple[Mon, Q], ...]

    @staticmethod
    def make(n: int, terms: dict[Mon, Q | int]) -> 'Poly':
        if n < 1:
            raise ValueError('At least one variable is required')
        if any(len(m) != n or any(type(i) is not int or i < 0 for i in m) for m in terms):
            raise ValueError('Malformed monomial')
        return Poly(n, tuple(sorted((m, Q(c)) for m, c in terms.items() if c)))

    @staticmethod
    def const(n: int, c: Q | int) -> 'Poly':
        return Poly.make(n, {(0,) * n: Q(c)})

    @staticmethod
    def var(n: int, i: int) -> 'Poly':
        if not 0 <= i < n:
            raise ValueError('Variable index out of range')
        m = [0] * n
        m[i] = 1
        return Poly.make(n, {tuple(m): Q(1)})

    def _coerce(self, p: 'Poly | Q | int') -> 'Poly':
        p = p if isinstance(p, Poly) else Poly.const(self.n, p)
        if p.n != self.n:
            raise ValueError('Different polynomial rings')
        return p

    def __add__(self, p: 'Poly | Q | int') -> 'Poly':
        p = self._coerce(p)
        d = dict(self.terms)
        for m, c in p.terms:
            d[m] = d.get(m, Q(0)) + c
        return Poly.make(self.n, d)

    __radd__ = __add__

    def __neg__(self) -> 'Poly':
        return Poly.make(self.n, {m: -c for m, c in self.terms})

    def __sub__(self, p: 'Poly | Q | int') -> 'Poly':
        return self + -self._coerce(p)

    def __rsub__(self, p: 'Poly | Q | int') -> 'Poly':
        return self._coerce(p) + -self

    def __mul__(self, p: 'Poly | Q | int') -> 'Poly':
        p = self._coerce(p)
        d: dict[Mon, Q] = {}
        for m, c in self.terms:
            for k, e in p.terms:
                mk = tuple(a + b for a, b in zip(m, k))
                d[mk] = d.get(mk, Q(0)) + c * e
        return Poly.make(self.n, d)

    __rmul__ = __mul__

    def __pow__(self, k: int) -> 'Poly':
        if type(k) is not int or k < 0:
            raise ValueError('Only nonnegative integer powers are supported')
        p = Poly.const(self.n, 1)
        a = self
        while k:
            if k & 1:
                p = p * a
            a = a * a
            k >>= 1
        return p

    @property
    def degree(self) -> int:
        return max((sum(m) for m, _ in self.terms), default=0)

    def eval(self, xs: Iterable[Q | int]) -> Q:
        xs = tuple(map(Q, xs))
        if len(xs) != self.n:
            raise ValueError('Wrong number of coordinates')
        return sum((c * _prod(x ** k for x, k in zip(xs, m)) for m, c in self.terms), Q(0))

    def substitute(self, xs: Iterable['Poly']) -> 'Poly':
        xs = tuple(xs)
        if len(xs) != self.n or any(x.n != self.n for x in xs):
            raise ValueError('Malformed substitution')
        return sum((c * _prod_poly((x ** k for x, k in zip(xs, m)), self.n)
                    for m, c in self.terms), Poly.const(self.n, 0))

    def json(self) -> dict:
        return {'variables': self.n, 'terms': [[list(m), str(c)] for m, c in self.terms]}

    def __str__(self) -> str:
        names = ['x', 'y', 'z'] + [f'x{i}' for i in range(3, self.n)]
        pieces = []
        for m, c in sorted(self.terms, reverse=True):
            factors = [names[i] + (f'^{k}' if k != 1 else '') for i, k in enumerate(m) if k]
            pieces.append(str(c) + ('*' + '*'.join(factors) if factors else ''))
        return ' + '.join(pieces).replace('+ -', '- ') or '0'


def _prod(xs: Iterable[Q]) -> Q:
    p = Q(1)
    for x in xs:
        p *= x
    return p


def _prod_poly(xs: Iterable[Poly], n: int) -> Poly:
    p = Poly.const(n, 1)
    for x in xs:
        p *= x
    return p


@dataclass(frozen=True)
class ConeTerm:
    weight: Q
    square: Poly
    guards: tuple[int, ...] = ()

@dataclass(frozen=True)
class ConeCertificate:
    terms: tuple[ConeTerm, ...]

    def json(self) -> dict:
        return {'kind': 'nonnegative_cone', 'terms': [
            {'weight': str(t.weight), 'square': t.square.json(), 'guards': list(t.guards)}
            for t in self.terms]}


def check_cone(target: Poly, guards: tuple[Poly, ...], cert: ConeCertificate) -> bool:
    """Check target = sum w*q^2*prod guards, w >= 0, over ordered fields.

    A positive result proves target >= 0 CONDITIONALLY on every guard >= 0.
    The caller must prove these guards in the original proof context.
    """
    try:
        if any(g.n != target.n for g in guards):
            return False
        out = Poly.const(target.n, 0)
        for t in cert.terms:
            if t.weight < 0 or t.square.n != target.n:
                return False
            if any(type(j) is not int or j < 0 or j >= len(guards) for j in t.guards):
                return False
            p = t.weight * t.square ** 2
            for j in t.guards:
                p *= guards[j]
            out += p
        return out == target
    except (TypeError, ValueError, IndexError):
        return False

Box = tuple[tuple[Q, Q], ...]


def bernstein_coefficients(p: Poly, box: Box) -> tuple[Q, ...]:
    """Tensor-product Bernstein coefficients after exact affine box scaling."""
    if len(box) != p.n or any(a >= b for a, b in box):
        raise ValueError('Each interval must have positive width')
    p = p.substitute(Poly.const(p.n, a) + (b - a) * Poly.var(p.n, i)
                     for i, (a, b) in enumerate(box))
    deg = tuple(max((m[i] for m, _ in p.terms), default=0) for i in range(p.n))
    result = []
    for k in product(*(range(d + 1) for d in deg)):
        b = Q(0)
        for j, a in p.terms:
            if all(jj <= kk for jj, kk in zip(j, k)):
                b += a * _prod(Q(comb(kk, jj), comb(nn, jj))
                                for kk, jj, nn in zip(k, j, deg))
        result.append(b)
    return tuple(result)

@dataclass(frozen=True)
class BoxCertificate:
    # Leaves contain only an exact bound, recomputed by the checker.
    lower: Q | None = None
    axis: int | None = None
    split: Q | None = None
    left: 'BoxCertificate | None' = None
    right: 'BoxCertificate | None' = None

    def json(self) -> dict:
        if self.axis is None:
            return {'kind': 'leaf', 'lower': str(self.lower)}
        return {'kind': 'split', 'axis': self.axis, 'point': str(self.split),
                'left': self.left.json(), 'right': self.right.json()}


def split_box(box: Box, axis: int, s: Q) -> tuple[Box, Box]:
    if type(axis) is not int or not 0 <= axis < len(box):
        raise ValueError('Invalid axis')
    a, b = box[axis]
    if not a < s < b:
        raise ValueError('Split must be interior')
    left, right = list(box), list(box)
    left[axis], right[axis] = (a, s), (s, b)
    return tuple(left), tuple(right)


def check_box(p: Poly, box: Box, cert: BoxCertificate, strict: bool = False,
              fuel: int = 10000) -> bool:
    """Check a covering bisection tree for p >= 0 (or p > 0)."""
    try:
        if fuel <= 0 or len(box) != p.n or any(a >= b for a, b in box):
            return False
        if cert.axis is None:
            if cert.lower is None or cert.left is not None or cert.right is not None or cert.split is not None:
                return False
            bound = min(bernstein_coefficients(p, box))
            return cert.lower == bound and (bound > 0 if strict else bound >= 0)
        if cert.lower is not None or cert.split is None or cert.left is None or cert.right is None:
            return False
        left, right = split_box(box, cert.axis, cert.split)
        return check_box(p, left, cert.left, strict, fuel - 1) and check_box(p, right, cert.right, strict, fuel - 1)
    except (ValueError, TypeError, RecursionError):
        return False
