"""Exact canonical exponential-polynomial arithmetic. Python 3.9+, stdlib only.

f(x) = sum c_(rate,degree) x**degree exp(rate*x). No numerical transcendental
function is used by the producer or the acceptance checker.
"""
from fractions import Fraction as Q
from collections import defaultdict
from typing import Dict, Tuple, Iterable, Mapping
from math import factorial

Key = Tuple[Q, int]
Poly = Dict[Key, Q]


def rat(value):
    if isinstance(value, bool) or isinstance(value, float):
        raise ValueError('booleans and floating-point numbers are not rationals')
    if isinstance(value, Q):
        return value
    if isinstance(value, int):
        return Q(value)
    if isinstance(value, str):
        ans = Q(value)
        if str(ans) != value:
            raise ValueError('noncanonical rational spelling')
        return ans
    raise ValueError('expected a canonical rational string or integer')


def clean(items: Iterable[Tuple[Key, Q]]) -> Poly:
    d = defaultdict(Q)
    for (r, k), c in items:
        if type(k) is not int or k < 0:
            raise ValueError('invalid degree')
        d[(rat(r), k)] += rat(c)
    return dict(sorted((key, c) for key, c in d.items() if c))


def make(*terms) -> Poly:
    """Each input term is (rate, polynomial degree, coefficient)."""
    return clean((((rat(r), k), rat(c)) for r, k, c in terms))


def add(a: Poly, b: Poly) -> Poly:
    return clean(list(a.items()) + list(b.items()))


def scale(a: Poly, c) -> Poly:
    c = rat(c)
    return clean((k, v*c) for k, v in a.items())


def mul(a: Poly, b: Poly) -> Poly:
    return clean((((r+s, k+j), c*d) for (r, k), c in a.items()
                  for (s, j), d in b.items()))


def reflect(a: Poly) -> Poly:
    return clean(((-r, k), c*(-1)**k) for (r, k), c in a.items())


def op(a: Poly, rho) -> Poly:
    """Apply D-rho in the search implementation."""
    rho = rat(rho)
    out = []
    for (r, k), c in a.items():
        out.append(((r, k), (r-rho)*c))
        if k:
            out.append(((r, k-1), k*c))
    return clean(out)


def origin(a: Poly) -> Q:
    return sum((c for (_, k), c in a.items() if k == 0), Q(0))


def spectrum(a: Poly):
    degrees = {}
    for r, k in a:
        degrees[r] = max(k, degrees.get(r, -1))
    return [r for r in sorted(degrees) for _ in range(degrees[r]+1)]


def encode(a: Poly):
    return [[str(r), k, str(c)] for (r, k), c in sorted(a.items())]


def decode(rows) -> Poly:
    if not isinstance(rows, list) or len(rows) > 20000:
        raise ValueError('invalid polynomial rows')
    seen = []
    for row in rows:
        if not isinstance(row, list) or len(row) != 3:
            raise ValueError('invalid polynomial term')
        r, k, c = row
        if not isinstance(r, str) or not isinstance(c, str):
            raise ValueError('serialized rationals must be strings')
        r, c = rat(r), rat(c)
        if type(k) is not int or not 0 <= k <= 2000 or not c:
            raise ValueError('invalid or zero term')
        seen.append(((r, k), c))
    result = clean(seen)
    if encode(result) != rows:
        raise ValueError('polynomial is not canonically ordered')
    return result


def taylor_remainder(n: int, rate=1) -> Poly:
    r = rat(rate)
    return add(make((r, 0, 1)), make(*[(0, k, -r**k/Q(factorial(k)))
                                                  for k in range(n+1)]))
