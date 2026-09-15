"""Small exact algebra layer for the *search* side (Python 3.10+).

The certificate replayer deliberately does not import this module.
All matrices are row-major; polynomials map exponent tuples to Fractions.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import product
from typing import Iterable

Poly = dict[tuple[int, ...], Q]


def rref(rows: Iterable[Iterable[Q]], ncols: int | None = None):
    a = [list(map(Q, row)) for row in rows]
    n = ncols if ncols is not None else (len(a[0]) if a else 0)
    if any(len(row) != n for row in a):
        raise ValueError('ragged matrix')
    pivots: list[int] = []
    r = 0
    for c in range(n):
        k = next((i for i in range(r, len(a)) if a[i][c]), None)
        if k is None:
            continue
        a[r], a[k] = a[k], a[r]
        z = a[r][c]
        a[r] = [v / z for v in a[r]]
        for i in range(len(a)):
            if i != r and a[i][c]:
                z = a[i][c]
                a[i] = [x - z*y for x, y in zip(a[i], a[r])]
        pivots.append(c)
        r += 1
        if r == len(a):
            break
    return a[:r], pivots


def nullspace(rows, ncols: int):
    a, piv = rref(rows, ncols)
    free = [i for i in range(ncols) if i not in piv]
    out = []
    for f in free:
        v = [Q(0)]*ncols
        v[f] = Q(1)
        for row, p in zip(a, piv):
            v[p] = -row[f]
        out.append(v)
    return out


def coordinates(basis, value):
    """Return coefficients in an independent row basis, or None."""
    if not basis:
        return [] if not any(value) else None
    k = len(basis)
    eqs = [[basis[j][i] for j in range(k)] + [value[i]]
           for i in range(len(value))]
    a, piv = rref(eqs, k+1)
    if k in piv:
        return None
    c = [Q(0)]*k
    for row, p in zip(a, piv):
        if p < k:
            c[p] = row[-1]
    return c


def dot(a, b):
    if len(a) != len(b):
        raise ValueError('dimension mismatch')
    return sum((Q(x)*Q(y) for x,y in zip(a,b)), Q(0))


def matmul(a, b):
    if not a:
        return []
    if not b:
        return [[] for _ in a]
    return [[dot(row, col) for col in zip(*b)] for row in a]


def clean(p: Poly) -> Poly:
    return {m: Q(c) for m,c in p.items() if c}


def const(n: int, c=0) -> Poly:
    return {(0,)*n: Q(c)} if c else {}


def var(n: int, i: int) -> Poly:
    return {tuple(int(j == i) for j in range(n)): Q(1)}


def add(*ps: Poly) -> Poly:
    out: Poly = {}
    for p in ps:
        for m,c in p.items():
            out[m] = out.get(m,Q(0)) + c
    return clean(out)


def scale(c, p: Poly) -> Poly:
    return clean({m: Q(c)*v for m,v in p.items()})


def mul(p: Poly, q: Poly) -> Poly:
    out: Poly = {}
    for a,x in p.items():
        for b,y in q.items():
            if len(a) != len(b):
                raise ValueError('polynomial arity mismatch')
            c = tuple(u+v for u,v in zip(a,b))
            out[c] = out.get(c,Q(0)) + x*y
    return clean(out)


def power(p: Poly, k: int, n: int) -> Poly:
    if k < 0:
        raise ValueError('negative polynomial power')
    out = const(n,1)
    while k:
        if k & 1:
            out = mul(out,p)
        k >>= 1
        if k:
            p = mul(p,p)
    return out


def subst(p: Poly, images: list[Poly], out_n: int) -> Poly:
    out: Poly = {}
    for mon,c in p.items():
        if len(mon) != len(images):
            raise ValueError('substitution arity mismatch')
        term = const(out_n,c)
        for x,k in zip(images,mon):
            term = mul(term,power(x,k,out_n))
        out = add(out,term)
    return out


def monomials(n: int, d: int):
    # Bounded research workloads, not a sparse production monomial generator.
    return sorted((m for m in product(range(d+1),repeat=n) if sum(m)<=d),
                  key=lambda m:(sum(m),m))


def vector(p: Poly, mons):
    allowed = set(mons)
    if set(p)-allowed:
        raise ValueError('would truncate a high-degree term')
    return [p.get(m,Q(0)) for m in mons]


def polynomial(row, mons):
    return clean(dict(zip(mons,row)))


def evaluate(p: Poly, xs):
    z = Q(0)
    for mon,c in p.items():
        t = c
        for x,k in zip(xs,mon):
            t *= Q(x)**k
        z += t
    return z


def encode(p: Poly):
    return [[list(m), [c.numerator,c.denominator]] for m,c in sorted(p.items())]


def encode_q(c):
    c=Q(c)
    return [c.numerator,c.denominator]


def pretty(p: Poly, names):
    if not p:
        return '0'
    parts=[]
    for m,c in sorted(p.items(),key=lambda mc:(sum(mc[0]),mc[0])):
        term='*'.join(f'{s}^{k}' if k!=1 else s for s,k in zip(names,m) if k)
        parts.append(f'({c})'+('*'+term if term else ''))
    return ' + '.join(parts)
