"""Exact dense arithmetic used by search; the replay checker does not import this file."""
from __future__ import annotations
from fractions import Fraction as Q
from math import comb
from typing import Iterable

Poly = tuple[Q, ...]
Interval = tuple[Q, Q]

def poly(xs: Iterable[Q | int]) -> Poly:
    v = [Q(x) for x in xs]
    while len(v) > 1 and v[-1] == 0:
        v.pop()
    return tuple(v or [Q(0)])

def add(p: Poly, q: Poly) -> Poly:
    return poly((p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0)
                for i in range(max(len(p), len(q))))

def scale(p: Poly, c: Q | int) -> Poly:
    return poly(Q(c) * a for a in p)

def sub(p: Poly, q: Poly) -> Poly:
    return add(p, scale(q, -1))

def mul(p: Poly, q: Poly) -> Poly:
    out = [Q(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i+j] += a*b
    return poly(out)

def power(p: Poly, n: int) -> Poly:
    if n < 0:
        raise ValueError('negative polynomial exponent')
    r = poly([1])
    for _ in range(n):
        r = mul(r, p)
    return r

def deriv(p: Poly) -> Poly:
    return poly(i*p[i] for i in range(1, len(p)))

def evaluate(p: Poly, x: Q | int) -> Q:
    out = Q(0)
    for c in reversed(p):
        out = out*Q(x)+c
    return out

def shift(p: Poly, n: Q | int) -> Poly:
    return poly(sum((p[j]*comb(j, k)*Q(n)**(j-k) for j in range(k, len(p))), Q(0))
                for k in range(len(p)))

def ia(a: Interval, b: Interval) -> Interval:
    return a[0]+b[0], a[1]+b[1]

def im(a: Interval, b: Interval) -> Interval:
    v = [x*y for x in a for y in b]
    return min(v), max(v)

def horner(p: Poly, b: Q) -> Interval:
    out = (Q(0), Q(0))
    for c in reversed(p):
        out = ia(im(out, (Q(0), b)), (c, c))
    return out

def text(q: Q | int) -> str:
    v = Q(q)
    return f'{v.numerator}/{v.denominator}'

def enc(p: Poly) -> list[str]:
    return [text(c) for c in p]

def dec(p: list[str]) -> Poly:
    return poly(Q(c) for c in p)

def positive_shift_cutoff(p: Poly) -> int:
    """Conservative Cauchy cutoff: all coefficients of p(N+t) are positive.

    Requires a positive leading coefficient. This is a search utility only;
    replay directly checks the final shifted coefficients instead.
    """
    if p[-1] <= 0:
        raise ValueError('positive leading coefficient required')
    m = len(p)-1
    ratio = Q(0)
    for k in range(m):
        leading = comb(m, k)*p[m]
        for j in range(k, m):
            ratio = max(ratio, abs(comb(j, k)*p[j])/leading)
    return ratio.numerator // ratio.denominator + 3
