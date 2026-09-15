"""Exact sparse multivariate polynomials over Q.

PROVENANCE
  BASE  p1-structural-search/prototype/forge/poly.py
        (frozen dataclass, canonical form enforced in __post_init__)
  FOLD  p8-obligation-broker/prototype/poly.py -- rational() float-rejection gate
        (applied to EVERY coefficient, including ones that happen to be zero),
        the `degrees` property, and weak-composition monomial enumeration
        (p1 built a wasteful (d+1)^n grid).
  FOLD  p3-planner-certificate-layer/prototype/polynomial.py -- expand_bernstein
        and affine_box.
  FOLD  p7-successor-architecture/prototype/polynomial.py -- duplicate-monomial
        rejection in from_json.
  MOVED OUT  p1's solve_linear / polynomial_linear_combination now live in
        forge/linalg.py, the single home for exact linear algebra.

Arity field is `n`; constructors are const/var/make (p5's nvars/constant/variable
and p2's Poly.variable spellings were dropped). No floating point anywhere.
This module is tested, not formally verified; it is not a Lean kernel.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
from math import comb
from typing import Iterable, Mapping, Sequence

Exp = tuple[int, ...]
Box = tuple[tuple[Q, Q], ...]


def rational(x: int | Q) -> Q:
    """Reject floats *before* they can silently enter an acceptance path."""
    if type(x) is int or isinstance(x, Q):
        return Q(x)
    raise TypeError('polynomial coefficients must be int or Fraction, not floats')


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
            if not isinstance(coefficient, Q) or isinstance(coefficient, bool) or not coefficient:
                raise ValueError('canonical, nonzero rational coefficients required')
            if previous is not None and exponent <= previous:
                raise ValueError('terms must be sorted and unique')
            previous = exponent

    # ---- construction -----------------------------------------------------
    @staticmethod
    def make(n: int, terms: Mapping[Exp, Q | int] | Iterable[tuple[Exp, Q | int]]) -> Poly:
        if type(n) is not int or n < 1:
            raise ValueError('positive variable count required')
        items = terms.items() if isinstance(terms, Mapping) else terms
        d: dict[Exp, Q] = {}
        for e, c in items:
            e = tuple(e)
            if len(e) != n or any(type(k) is not int or k < 0 for k in e):
                raise ValueError('invalid exponent')
            # Validate even coefficients that happen to be zero (p8 gate).
            d[e] = d.get(e, Q(0)) + rational(c)
        return Poly(n, tuple(sorted((e, c) for e, c in d.items() if c)))

    @staticmethod
    def const(n: int, c: Q | int = 0) -> Poly:
        return Poly.make(n, [((0,) * n, rational(c))])

    @staticmethod
    def var(n: int, i: int) -> Poly:
        if type(i) is not int or not 0 <= i < n:
            raise ValueError('variable index outside arity')
        return Poly.make(n, [(tuple(int(j == i) for j in range(n)), 1)])

    @staticmethod
    def monomial(n: int, e: Exp, c: Q | int = 1) -> Poly:
        return Poly.make(n, [(tuple(e), rational(c))])

    # ---- shape ------------------------------------------------------------
    @property
    def degree(self) -> int:
        return max((sum(e) for e, _ in self.terms), default=0)

    @property
    def degrees(self) -> Exp:
        """Per-variable maximum exponent (p8)."""
        return tuple(max((e[j] for e, _ in self.terms), default=0) for j in range(self.n))

    # ---- arithmetic -------------------------------------------------------
    def coerce(self, other: Poly | Q | int) -> Poly:
        if isinstance(other, Poly):
            if self.n != other.n:
                raise ValueError('different polynomial rings')
            return other
        return Poly.const(self.n, rational(other))

    _coerce = coerce

    def __add__(self, other: Poly | Q | int) -> Poly:
        p = self.coerce(other)
        return Poly.make(self.n, self.terms + p.terms)

    __radd__ = __add__

    def __neg__(self) -> Poly:
        return Poly(self.n, tuple((e, -c) for e, c in self.terms))

    def __sub__(self, other: Poly | Q | int) -> Poly:
        return self + (-self.coerce(other))

    def __rsub__(self, other: Poly | Q | int) -> Poly:
        return self.coerce(other) + (-self)

    def __mul__(self, other: Poly | Q | int) -> Poly:
        p = self.coerce(other)
        out: dict[Exp, Q] = {}
        for a, c in self.terms:
            for b, d in p.terms:
                e = tuple(x + y for x, y in zip(a, b))
                out[e] = out.get(e, Q(0)) + c * d
        return Poly.make(self.n, out)

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
        vals = tuple(rational(v) for v in values)
        if len(vals) != self.n:
            raise ValueError('wrong point dimension')
        total = Q(0)
        for ex, c in self.terms:
            for a, k in zip(vals, ex):
                c *= a ** k
            total += c
        return total

    def substitute(self, values: Iterable[Poly]) -> Poly:
        images = tuple(values)
        if len(images) != self.n or not images:
            raise ValueError('wrong substitution dimension')
        m = images[0].n
        if any(p.n != m for p in images):
            raise ValueError('inconsistent substitution codomain')
        total = Poly.const(m, 0)
        for ex, c in self.terms:
            term = Poly.const(m, c)
            for p, k in zip(images, ex):
                term = term * p ** k
            total += term
        return total

    def affine_box(self, box: Box) -> Poly:
        """Exact affine map of the unit cube onto `box` (p3)."""
        if len(box) != self.n or any(
                not isinstance(l, Q) or not isinstance(u, Q) or l >= u for l, u in box):
            raise ValueError('box must have rational endpoints with lower < upper')
        return self.substitute(tuple(
            l + (u - l) * Poly.var(self.n, j) for j, (l, u) in enumerate(box)))

    # ---- rendering / serialisation ---------------------------------------
    def lean(self, names: Sequence[str]) -> str:
        """Render already structured polynomials; never parse/evaluate source."""
        if len(names) != self.n:
            raise ValueError('wrong name dimension')
        if not self.terms:
            return '0'
        chunks = []
        for ex, c in reversed(self.terms):
            coef = str(c.numerator) if c.denominator == 1 else f'({c.numerator} / {c.denominator})'
            factors = [f'({coef})']
            factors += [f'({v})' if k == 1 else f'({v}) ^ {k}' for v, k in zip(names, ex) if k]
            chunks.append(' * '.join(factors))
        return ' + '.join(chunks)

    def json(self) -> dict:
        return {'n': self.n, 'terms': [[list(e), str(c)] for e, c in self.terms]}

    to_json = json

    @staticmethod
    def from_json(d: Mapping) -> Poly:
        if not isinstance(d, Mapping) or set(d) != {'n', 'terms'}:
            raise ValueError('invalid polynomial object')
        seen: dict[Exp, Q] = {}
        for e, c in d['terms']:
            e = tuple(e)
            if e in seen:  # p7: a duplicate monomial is never canonical input
                raise ValueError('duplicate monomial')
            seen[e] = Q(c) if isinstance(c, str) else rational(c)
        return Poly.make(d['n'], seen)

    def text(self, names: Sequence[str] | None = None) -> str:
        names = tuple(names) if names else tuple(f'x{i}' for i in range(self.n))
        chunks = []
        for e, c in reversed(self.terms):
            s = '*'.join(names[i] + (f'^{k}' if k != 1 else '')
                         for i, k in enumerate(e) if k)
            chunks.append(f'({c})' + ('*' + s if s else ''))
        return ' + '.join(chunks) or '0'

    __str__ = text


def prod_q(xs: Iterable[Q]) -> Q:
    a = Q(1)
    for x in xs:
        a *= x
    return a


def monomial_exponents(n: int, max_degree: int) -> list[Exp]:
    """Weak compositions only -- not a (max_degree+1)^n enclosing grid (p8)."""
    if type(n) is not int or n < 1 or type(max_degree) is not int or max_degree < 0:
        raise ValueError('invalid monomial bounds')

    def compositions(total: int, parts: int):
        if parts == 1:
            yield (total,)
        else:
            for first in range(total + 1):
                for tail in compositions(total - first, parts - 1):
                    yield (first,) + tail

    return [e for d in range(max_degree + 1) for e in compositions(d, n)]


def monomials(n: int, max_degree: int) -> tuple[Poly, ...]:
    return tuple(Poly.monomial(n, e) for e in monomial_exponents(n, max_degree))


def unit_transform(p: Poly, box: Box) -> Poly:
    return p.affine_box(box)


def bernstein_coefficients(p: Poly, box: Box,
                          max_coefficients: int = 100_000) -> tuple[Exp, tuple[Q, ...]]:
    """Power-to-tensor-Bernstein conversion after exact affine box transformation.

    Degrees come from the TRANSFORMED polynomial, never from the original one.
    Returns (degrees, coefficients) in row-major `product(range(d+1))` order.
    """
    t = p.affine_box(box)
    ds = t.degrees
    size = 1
    for d in ds:
        size *= d + 1
        if size > max_coefficients:  # p3: cap the tensor before building it
            raise ValueError('Bernstein tensor size limit')
    result = []
    for i in product(*(range(d + 1) for d in ds)):
        result.append(sum((c * prod_q(Q(comb(ij, a), comb(dj, a))
                                      for ij, dj, a in zip(i, ds, e))
                           for e, c in t.terms if all(a <= b for a, b in zip(e, i))), Q(0)))
    return ds, tuple(result)


def expand_bernstein(n: int, ds: Exp, coeffs: Sequence[Q]) -> Poly:
    """Checker-side conversion in the opposite direction (p3).

    Deliberately NOT the producer's formula: it rebuilds the polynomial from the
    claimed Bernstein representation over the unit cube.
    """
    if len(ds) != n or any(type(d) is not int or d < 0 for d in ds):
        raise ValueError('Malformed Bernstein degree vector')
    size = 1
    for d in ds:
        size *= d + 1
        if size > 100_000:
            raise ValueError('Bernstein tensor size limit')
    if size != len(coeffs):
        raise ValueError('Malformed Bernstein coefficient vector')
    out = Poly.const(n, 0)
    for beta, c in zip(product(*(range(d + 1) for d in ds)), coeffs):
        t = Poly.const(n, c)
        for i, (b, d) in enumerate(zip(beta, ds)):
            x = Poly.var(n, i)
            t = t * comb(d, b) * x ** b * (1 - x) ** (d - b)
        out += t
    return out
