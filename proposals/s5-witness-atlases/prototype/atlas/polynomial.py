"""Sparse rational bivariate identities and a deliberately small wire format."""
from __future__ import annotations
from fractions import Fraction as Q
from .exact import parse_q, trim

Poly2 = dict[tuple[int, int], Q]
MAX_TERMS = 10000
MAX_DEGREE = 64


def decode(items: list) -> Poly2:
    if not isinstance(items, list) or len(items) > MAX_TERMS:
        raise ValueError('invalid/oversized sparse polynomial')
    p: Poly2 = {}
    previous = None
    for row in items:
        if not isinstance(row, list) or len(row) != 3:
            raise ValueError('invalid polynomial term')
        i, j, v = row
        if type(i) is not int or type(j) is not int or min(i, j) < 0 or max(i,j) > MAX_DEGREE:
            raise ValueError('invalid degree')
        key = i, j
        if previous is not None and key <= previous:
            raise ValueError('terms must be unique and lexicographically sorted')
        q = parse_q(v)
        if q == 0:
            raise ValueError('zero sparse coefficient')
        p[key] = q
        previous = key
    return p


def encode(p: Poly2) -> list:
    return [[i, j, str(c)] for (i, j), c in sorted(p.items()) if c]


def plus(p: Poly2, q: Poly2) -> Poly2:
    r = p.copy()
    for k, c in q.items():
        r[k] = r.get(k, Q(0)) + c
        if r[k] == 0:
            del r[k]
    return r


def times(p: Poly2, q: Poly2) -> Poly2:
    r: Poly2 = {}
    for (i,j), a in p.items():
        for (k,l), b in q.items():
            key = i+k, j+l
            r[key] = r.get(key, Q(0)) + a*b
    return {k:v for k,v in r.items() if v}


def pow2(p: Poly2, n: int) -> Poly2:
    r = {(0,0):Q(1)}
    while n:
        if n & 1:
            r = times(r,p)
        p = times(p,p)
        n //= 2
    return r


def dy(p: Poly2) -> Poly2:
    return {(i,j-1):j*c for (i,j),c in p.items() if j}


def y_degree(p: Poly2) -> int:
    return max((j for i,j in p), default=-1)


def xpoly(p: Poly2) -> tuple:
    if any(j for i,j in p):
        raise ValueError('guard depends on y')
    return trim(p.get((i,0),Q(0)) for i in range(max((i for i,j in p),default=-1)+1))


def from_x(p: tuple) -> Poly2:
    return {(i,0):a for i,a in enumerate(p) if a}


def leading_y(p: Poly2) -> tuple:
    d = y_degree(p)
    return trim(p.get((i,d),Q(0)) for i in range(max((i for i,j in p if j==d), default=-1)+1))


def decode_dense(values: list) -> tuple:
    if not isinstance(values,list) or len(values)>MAX_TERMS:
        raise ValueError('invalid dense polynomial')
    p = tuple(parse_q(v) for v in values)
    if p and p[-1] == 0:
        raise ValueError('trailing zero coefficient')
    return p


def encode_dense(p: tuple) -> list[str]:
    return [str(a) for a in p]
