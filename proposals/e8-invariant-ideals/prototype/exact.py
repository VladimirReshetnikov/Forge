"""Small exact rational linear algebra and sparse polynomial arithmetic.

Research implementation, not a formally verified kernel. All arithmetic is exact.
Python >= 3.9; no third-party packages.
"""
from fractions import Fraction as Q
from itertools import product
from typing import Dict, List, Tuple

Exponent = Tuple[int, ...]
Poly = Dict[Exponent, Q]


def rational(x):
    if type(x) is int or isinstance(x, Q):
        return Q(x)
    raise TypeError('exact integer or Fraction required')


def clean(p: Poly) -> Poly:
    return {tuple(m): rational(c) for m, c in p.items() if c != 0}


def const(n: int, c) -> Poly:
    c = rational(c)
    return {(0,) * n: c} if c else {}


def var(n: int, i: int) -> Poly:
    if not 0 <= i < n:
        raise ValueError('variable index out of range')
    m = [0] * n
    m[i] = 1
    return {tuple(m): Q(1)}


def add(p: Poly, q: Poly) -> Poly:
    r = dict(p)
    for m, c in q.items():
        r[m] = r.get(m, Q(0)) + c
    return clean(r)


def scale(c, p: Poly) -> Poly:
    c = rational(c)
    return clean({m: c * a for m, a in p.items()})


def sub(p: Poly, q: Poly) -> Poly:
    return add(p, scale(-1, q))


def mul(p: Poly, q: Poly) -> Poly:
    r: Poly = {}
    for m, a in p.items():
        for k, b in q.items():
            if len(m) != len(k):
                raise ValueError('polynomial arity mismatch')
            e = tuple(x + y for x, y in zip(m, k))
            r[e] = r.get(e, Q(0)) + a * b
    return clean(r)


def power(p: Poly, k: int, n: int) -> Poly:
    if type(k) is not int or k < 0:
        raise ValueError('nonnegative integral exponent required')
    r = const(n, 1)
    while k:
        if k & 1:
            r = mul(r, p)
        p = mul(p, p)
        k //= 2
    return r


def compose(p: Poly, substitutions: List[Poly]) -> Poly:
    n = len(substitutions)
    r: Poly = {}
    for e, c in p.items():
        if len(e) != n:
            raise ValueError('substitution arity mismatch')
        t = const(n, c)
        for x, k in zip(substitutions, e):
            t = mul(t, power(x, k, n))
        r = add(r, t)
    return r


def evaluate(p: Poly, xs):
    r = Q(0)
    for m, c in p.items():
        if len(m) != len(xs):
            raise ValueError('evaluation arity mismatch')
        z = c
        for x, k in zip(xs, m):
            z *= rational(x) ** k
        r += z
    return r


def monomials(n: int, degree: int):
    if n < 1 or degree < 0:
        raise ValueError('positive variable count and nonnegative degree required')
    return sorted((e for e in product(range(degree + 1), repeat=n)
                   if sum(e) <= degree), key=lambda e: (sum(e), e))


def rref(rows, ncols=None):
    rows = [list(map(rational, r)) for r in rows]
    n = len(rows[0]) if rows else (ncols or 0)
    if ncols is not None and ncols != n:
        raise ValueError('matrix width mismatch')
    if any(len(r) != n for r in rows):
        raise ValueError('ragged matrix')
    pivots = []
    k = 0
    for j in range(n):
        pivot = next((i for i in range(k, len(rows)) if rows[i][j]), None)
        if pivot is None:
            continue
        rows[k], rows[pivot] = rows[pivot], rows[k]
        z = rows[k][j]
        rows[k] = [a / z for a in rows[k]]
        for i in range(len(rows)):
            if i != k and rows[i][j]:
                z = rows[i][j]
                rows[i] = [a - z*b for a, b in zip(rows[i], rows[k])]
        pivots.append(j)
        k += 1
        if k == len(rows):
            break
    return rows, pivots


def nullspace(rows, ncols: int):
    rr, piv = rref(rows, ncols)
    free = [j for j in range(ncols) if j not in piv]
    out = []
    for j in free:
        v = [Q(0)] * ncols
        v[j] = Q(1)
        for i, k in enumerate(piv):
            v[k] = -rr[i][j]
        out.append(v)
    return out


def row_basis(rows, ncols: int):
    rr, _ = rref(rows, ncols)
    return [r for r in rr if any(r)]


def linear_combination(coefficients, polys):
    if len(coefficients) != len(polys):
        raise ValueError('linear combination dimension mismatch')
    r = {}
    for c, p in zip(coefficients, polys):
        r = add(r, scale(c, p))
    return r


def coefficient_rows(polys):
    support = sorted(set().union(*(p.keys() for p in polys))) if polys else []
    return [[p.get(m, Q(0)) for p in polys] for m in support]


def poly_basis(polys):
    support = sorted(set().union(*(p.keys() for p in polys))) if polys else []
    rows = [[p.get(m, Q(0)) for m in support] for p in polys]
    return [clean(dict(zip(support, r))) for r in row_basis(rows, len(support))]


def coordinates(p: Poly, basis):
    """Find rational coefficients, or None. Free coefficients are set to zero."""
    support = sorted(set(p).union(*(q.keys() for q in basis)))
    rows = [[q.get(m, Q(0)) for q in basis] + [p.get(m, Q(0))] for m in support]
    rr, piv = rref(rows, len(basis) + 1)
    if len(basis) in piv:
        return None
    result = [Q(0)] * len(basis)
    for i, j in enumerate(piv):
        result[j] = rr[i][-1]
    return result


def encode_poly(p):
    return [[list(e), c.numerator, c.denominator] for e, c in sorted(p.items())]


def decode_poly(data, n: int):
    if type(data) is not list:
        raise ValueError('polynomial must be a list')
    p = {}
    for item in data:
        if type(item) is not list or len(item) != 3:
            raise ValueError('invalid polynomial term')
        e, a, b = item
        if (type(e) is not list or len(e) != n or
            any(type(k) is not int or k < 0 for k in e) or
            type(a) is not int or type(b) is not int or b <= 0):
            raise ValueError('invalid exact coefficient or exponent')
        e = tuple(e)
        if e in p or a == 0:
            raise ValueError('duplicate exponent or noncanonical zero')
        c = Q(a, b)
        if (c.numerator, c.denominator) != (a, b):
            raise ValueError('noncanonical rational')
        p[e] = c
    return p


def format_poly(p, names):
    parts = []
    for e, c in sorted(p.items(), key=lambda z: (sum(z[0]), z[0])):
        factors = [name if k == 1 else '%s^%d' % (name, k)
                   for name, k in zip(names, e) if k]
        mon = '*'.join(factors)
        parts.append(str(c) + ('*' + mon if mon else ''))
    return ' + '.join(parts) if parts else '0'
