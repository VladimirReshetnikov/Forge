"""Search-side dense exponential polynomials over Q. No floating arithmetic."""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from typing import Iterable, Mapping


def q(x: int | F) -> F:
    if type(x) not in (int, F):
        raise TypeError("coefficients must be integers or Fractions")
    return F(x)


def rat(x: F) -> list[int]:
    return [x.numerator, x.denominator]


def trim(xs: Iterable[int | F]) -> tuple[F, ...]:
    a = list(map(q, xs))
    while a and a[-1] == 0:
        a.pop()
    return tuple(a)


@dataclass(frozen=True)
class ExpPoly:
    """A canonical sum P_rate(x)*exp(rate*x); coefficients are ascending."""
    terms: tuple[tuple[F, tuple[F, ...]], ...]

    @classmethod
    def make(cls, terms: Mapping[int | F, Iterable[int | F]]) -> 'ExpPoly':
        return cls(tuple(sorted((q(r), p) for r, cs in terms.items()
                                if (p := trim(cs)))))

    @classmethod
    def zero(cls) -> 'ExpPoly':
        return cls(())

    def __add__(self, other: 'ExpPoly') -> 'ExpPoly':
        d = dict(self.terms)
        for r, cs in other.terms:
            old = d.get(r, ())
            n = max(len(old), len(cs))
            d[r] = tuple((old[i] if i < len(old) else F(0)) +
                         (cs[i] if i < len(cs) else F(0)) for i in range(n))
        return ExpPoly.make(d)

    def scale(self, c: int | F) -> 'ExpPoly':
        c = q(c)
        return ExpPoly.make({r: [c*a for a in p] for r, p in self.terms})

    def __sub__(self, other: 'ExpPoly') -> 'ExpPoly':
        return self + other.scale(-1)

    def __mul__(self, other: 'ExpPoly') -> 'ExpPoly':
        out = ExpPoly.zero()
        for r, a in self.terms:
            for s, b in other.terms:
                cs = [F(0)]*(len(a)+len(b)-1)
                for i, u in enumerate(a):
                    for j, v in enumerate(b):
                        cs[i+j] += u*v
                out = out + ExpPoly.make({r+s: cs})
        return out

    def deriv(self) -> 'ExpPoly':
        return ExpPoly.make({r: [r*a + ((i+1)*p[i+1] if i+1 < len(p) else F(0))
                                for i, a in enumerate(p)] for r, p in self.terms})

    def step(self, cofactor: int | F) -> 'ExpPoly':
        return self.deriv() - self.scale(cofactor)

    def anchor(self) -> F:
        return sum((p[0] for _, p in self.terms), F(0))

    def positive_polynomial(self) -> bool:
        return all(r == 0 and all(c >= 0 for c in p) for r, p in self.terms)

    def payload(self) -> list[dict]:
        return [{"rate": rat(r), "coeffs": [rat(c) for c in p]} for r, p in self.terms]

    def problem(self) -> dict:
        return {"kind": "exp_poly_nonnegative", "anchor": [0, 1],
                "direction": "right", "terms": self.payload()}

    def complexity(self) -> int:
        return sum(len(p) for _, p in self.terms)
