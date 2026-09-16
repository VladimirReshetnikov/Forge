"""Rational enclosures for exp at rational arguments and normalized point signs.

All rounding is explicit, directed, integer-based dyadic rounding. The positive
argument is scaled to at most 1/2, bounded by a positive Taylor series with a
geometric tail, and, for negative arguments, inverted BEFORE repeated squaring.
"""
from fractions import Fraction as Q
from .core import rat, origin


def floor_dyadic(x: Q, bits: int) -> Q:
    return Q((x.numerator << bits)//x.denominator, 1 << bits)


def ceil_dyadic(x: Q, bits: int) -> Q:
    return -floor_dyadic(-x, bits)


def exp_bounds(z, bits=96, order=32):
    z = rat(z)
    if type(bits) is not int or not 8 <= bits <= 4096:
        raise ValueError('precision outside budget')
    if type(order) is not int or not 1 <= order <= 4096:
        raise ValueError('order outside budget')
    if z == 0:
        return Q(1), Q(1)
    r, squarings = abs(z), 0
    while r > Q(1, 2):
        r /= 2
        squarings += 1
        if squarings > 4096:
            raise ValueError('range-reduction budget exceeded')
    term = Q(1)
    lower = Q(1)
    for k in range(1, order+1):
        term *= r/k
        lower += term
    first_tail = term*r/(order+1)
    upper = lower + first_tail/(1-r/Q(order+2))
    if z < 0:
        lower, upper = 1/upper, 1/lower
    lower, upper = floor_dyadic(lower, bits), ceil_dyadic(upper, bits)
    for _ in range(squarings):
        lower = floor_dyadic(lower*lower, bits)
        upper = ceil_dyadic(upper*upper, bits)
    return lower, upper


def point_bounds(a, x, bits=96, order=32):
    """Enclose exp(-shift)*a(x); the omitted multiplier is strictly positive."""
    x = rat(x)
    if x == 0:
        q = origin(a)
        return q, q
    if not a:
        return Q(0), Q(0)
    grouped = {}
    for (r, k), c in a.items():
        grouped[r] = grouped.get(r, Q(0)) + c*x**k
    grouped = {r: c for r, c in grouped.items() if c}
    if not grouped:
        return Q(0), Q(0)
    shift = max(r*x for r in grouped)
    lower, upper = Q(0), Q(0)
    for r, c in grouped.items():
        lo, hi = exp_bounds(r*x-shift, bits, order)
        if c < 0:
            lo, hi = hi, lo
        lower += c*lo
        upper += c*hi
    return lower, upper
