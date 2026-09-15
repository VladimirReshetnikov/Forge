"""Small exact sparse-polynomial checker. No SymPy/NumPy/SciPy imports.

A polynomial is a dictionary from exponent tuples to fractions. Certificates
are checked relative to an explicitly supplied target and hypotheses; the
certificate is never allowed to choose its own theorem statement.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import product
from math import comb
from typing import TypeAlias

Poly: TypeAlias = dict[tuple[int, ...], Q]

def clean(p: Poly) -> Poly:
    return {m: Q(c) for m, c in p.items() if c}

def const(n: int, c: Q | int) -> Poly:
    return {(0,) * n: Q(c)} if c else {}

def add(p: Poly, q: Poly) -> Poly:
    out = dict(p)
    for m, c in q.items():
        out[m] = out.get(m, Q(0)) + c
    return clean(out)

def scale(p: Poly, c: Q | int) -> Poly:
    return clean({m: c * a for m, a in p.items()})

def mul(p: Poly, q: Poly) -> Poly:
    out: Poly = {}
    for m, a in p.items():
        for k, b in q.items():
            if len(m) != len(k):
                raise ValueError('inconsistent polynomial arity')
            v = tuple(i+j for i, j in zip(m, k))
            out[v] = out.get(v, Q(0)) + a*b
    return clean(out)

def power(p: Poly, k: int, n: int) -> Poly:
    if k < 0:
        raise ValueError('negative exponent')
    out = const(n, 1)
    while k:
        if k & 1:
            out = mul(out, p)
        p = mul(p, p)
        k >>= 1
    return out

def evaluate(p: Poly, xs: tuple[Q, ...]) -> Q:
    return sum((c * prodq(x**e for x, e in zip(xs, m))
                for m, c in p.items()), Q(0))

def prodq(xs) -> Q:
    out = Q(1)
    for x in xs:
        out *= x
    return out

def encode(p: Poly) -> list:
    return [[list(m), str(c)] for m, c in sorted(p.items()) if c]

def decode(data: list, n: int) -> Poly:
    p: Poly = {}
    if not isinstance(data, list):
        raise ValueError('polynomial must be a list')
    for m, c in data:
        if len(m) != n or any(type(e) is not int or e < 0 for e in m):
            raise ValueError('invalid exponent vector')
        m = tuple(m)
        if m in p:
            raise ValueError('duplicate monomial')
        p[m] = Q(c)
    return clean(p)

def verify_cone(target: Poly, inequalities: list[Poly], equalities: list[Poly],
                cert: dict, n: int) -> bool:
    """Check p = sum c*s^2*prod(g_i) + sum t*h_j with c >= 0.

    The interpretation is over an ordered field of characteristic zero.
    Repeated g_i factors are sound. No floating-point tolerance is used.
    """
    try:
        out: Poly = {}
        for term in cert['nonnegative']:
            c = Q(term['coefficient'])
            if c < 0:
                return False
            sq = decode(term['square'], n)
            p = scale(mul(sq, sq), c)
            for idx in term['factors']:
                if type(idx) is not int or not 0 <= idx < len(inequalities):
                    return False
                p = mul(p, inequalities[idx])
            out = add(out, p)
        for term in cert['ideal']:
            idx = term['equality']
            if type(idx) is not int or not 0 <= idx < len(equalities):
                return False
            out = add(out, mul(decode(term['multiplier'], n), equalities[idx]))
        return clean(out) == clean(target)
    except (KeyError, ValueError, TypeError, ZeroDivisionError, IndexError):
        return False

def affine_box(p: Poly, box: list[tuple[Q, Q]], n: int) -> Poly:
    """Independently expand p(a_i + (b_i-a_i)t_i)."""
    xs: list[Poly] = []
    for i, (a, b) in enumerate(box):
        m = tuple(int(i == j) for j in range(n))
        xs.append(add(const(n, a), {m: b-a}))
    out: Poly = {}
    for m, c in p.items():
        term = const(n, c)
        for i, k in enumerate(m):
            term = mul(term, power(xs[i], k, n))
        out = add(out, term)
    return out

def bernstein_coefficients(p: Poly, box: list[tuple[Q, Q]], n: int) -> list[Q]:
    q = affine_box(p, box, n)
    deg = tuple(max((m[i] for m in q), default=0) for i in range(n))
    out = []
    for beta in product(*(range(d+1) for d in deg)):
        c = Q(0)
        for alpha, v in q.items():
            if all(a <= b for a, b in zip(alpha, beta)):
                c += v * prodq(Q(comb(b, a), comb(d, a))
                              for a, b, d in zip(alpha, beta, deg))
        out.append(c)
    return out

def verify_bernstein(target: Poly, box: list[tuple[Q, Q]], cert: dict, n: int) -> bool:
    """Check an entire covering subdivision tree, not a collection of boxes."""
    try:
        if len(box) != n or any(a >= b for a, b in box):
            return False
        def check(bx, node):
            if node.get('kind') == 'leaf':
                actual = bernstein_coefficients(target, bx, n)
                return actual == [Q(x) for x in node['coefficients']] and min(actual) >= 0
            if node.get('kind') != 'split':
                return False
            i = node['axis']
            cut = Q(node['cut'])
            if type(i) is not int or not 0 <= i < n:
                return False
            a, b = bx[i]
            if not a < cut < b:
                return False
            left, right = list(bx), list(bx)
            left[i], right[i] = (a, cut), (cut, b)
            return check(left, node['left']) and check(right, node['right'])
        return check(box, cert)
    except (KeyError, TypeError, ValueError, ZeroDivisionError, IndexError, RecursionError):
        return False
