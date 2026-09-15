"""Tiny exact sparse polynomial arithmetic used by the independent checkers.

No SymPy, NumPy, SciPy, floating point, or search code is used here.
Variables are positional; exponents are nonnegative integers. Coefficients are
fractions.Fraction. This module is executable validation, NOT a formal proof.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from typing import Iterable

@dataclass(frozen=True)
class Poly:
    nvars: int
    terms: tuple[tuple[tuple[int, ...], Q], ...]

    def __post_init__(self) -> None:
        if not isinstance(self.nvars, int) or self.nvars < 1:
            raise ValueError("nvars must be positive")
        prev = None
        for mon, c in self.terms:
            if len(mon) != self.nvars or any(type(e) is not int or e < 0 for e in mon):
                raise ValueError("invalid exponent vector")
            if not isinstance(c, Q) or c == 0 or (prev is not None and mon <= prev):
                raise ValueError("terms must be sorted, unique, nonzero rational coefficients")
            prev = mon

    @classmethod
    def make(cls, n: int, terms: Iterable[tuple[tuple[int, ...], Q | int]]) -> 'Poly':
        d: dict[tuple[int, ...], Q] = {}
        for mon, c in terms:
            d[mon] = d.get(mon, Q(0)) + Q(c)
        return cls(n, tuple(sorted((m, c) for m, c in d.items() if c)))

    @classmethod
    def constant(cls, n: int, c: Q | int) -> 'Poly':
        return cls.make(n, [((0,) * n, Q(c))])

    @classmethod
    def variable(cls, n: int, i: int) -> 'Poly':
        if not 0 <= i < n:
            raise ValueError("bad variable index")
        return cls.make(n, [(tuple(int(j == i) for j in range(n)), 1)])

    def _other(self, other: 'Poly | Q | int') -> 'Poly':
        p = other if isinstance(other, Poly) else Poly.constant(self.nvars, Q(other))
        if p.nvars != self.nvars:
            raise ValueError("different polynomial rings")
        return p

    def __add__(self, other: 'Poly | Q | int') -> 'Poly':
        p = self._other(other)
        return Poly.make(self.nvars, self.terms + p.terms)
    __radd__ = __add__

    def __neg__(self) -> 'Poly':
        return Poly(self.nvars, tuple((m, -c) for m, c in self.terms))

    def __sub__(self, other: 'Poly | Q | int') -> 'Poly':
        return self + -self._other(other)

    def __rsub__(self, other: 'Poly | Q | int') -> 'Poly':
        return self._other(other) + -self

    def __mul__(self, other: 'Poly | Q | int') -> 'Poly':
        p = self._other(other)
        return Poly.make(self.nvars, [(tuple(a+b for a,b in zip(m,k)), c*d)
                        for m,c in self.terms for k,d in p.terms])
    __rmul__ = __mul__

    def __pow__(self, e: int) -> 'Poly':
        if type(e) is not int or e < 0:
            raise ValueError("only nonnegative integer powers")
        out, base = Poly.constant(self.nvars, 1), self
        while e:
            if e & 1:
                out = out * base
            base = base * base
            e //= 2
        return out

    @property
    def degree(self) -> int:
        return max((sum(m) for m,_ in self.terms), default=-1)

    def eval(self, values: Iterable[Q | int]) -> Q:
        vals = tuple(map(Q, values))
        if len(vals) != self.nvars:
            raise ValueError("valuation dimension")
        out = Q(0)
        for mon,c in self.terms:
            for x,e in zip(vals,mon):
                c *= x**e
            out += c
        return out

    def substitute(self, images: Iterable['Poly']) -> 'Poly':
        ps = tuple(images)
        if len(ps) != self.nvars or not ps or any(p.nvars != ps[0].nvars for p in ps):
            raise ValueError("substitution dimension")
        out = Poly.constant(ps[0].nvars, 0)
        for mon,c in self.terms:
            term = Poly.constant(ps[0].nvars, c)
            for p,e in zip(ps,mon):
                term *= p**e
            out += term
        return out

    def to_json(self) -> dict:
        return {"nvars": self.nvars,
                "terms": [[list(m), str(c)] for m,c in self.terms]}

    @classmethod
    def from_json(cls, data: dict) -> 'Poly':
        # Construct directly: malformed/colliding/noncanonical entries are rejected.
        return cls(data['nvars'], tuple((tuple(m), Q(c)) for m,c in data['terms']))

    def text(self, names: tuple[str, ...] | None = None) -> str:
        names = names or tuple(f'x{i}' for i in range(self.nvars))
        if len(names) != self.nvars:
            raise ValueError("variable-name dimension")
        ts = []
        for m,c in self.terms:
            factors = [names[i] if e == 1 else f'{names[i]}^{e}'
                       for i,e in enumerate(m) if e]
            ts.append(str(c) + ("*" + "*".join(factors) if factors else ""))
        return " + ".join(ts) or "0"


def monomials(n: int, degree: int) -> list[tuple[int, ...]]:
    """All exponent vectors of total degree <= degree, stable graded order."""
    def fixed(k: int, d: int):
        if k == 1:
            yield (d,)
        else:
            for e in range(d+1):
                for rest in fixed(k-1,d-e):
                    yield (e,) + rest
    if n < 1 or degree < 0:
        return []
    return [m for d in range(degree+1) for m in fixed(n,d)]
