"""Small, exact arithmetic used by the replay side (Python standard library only).

Research implementation, not a formally verified or hostile-input-hardened kernel.
Polynomials use a canonical sparse rational encoding; no floating point is accepted.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from math import gcd
from typing import Iterable

class Reject(ValueError):
    """Malformed, unsupported, or invalid certificate."""

class Limit(Reject):
    """An operational cap was reached; never a mathematical refutation."""

MAX_TERMS = 20000
MAX_BITS = 8192
MAX_EXP = 256


def integer(x, lo=None, hi=None):
    if type(x) is not int or (lo is not None and x < lo) or (hi is not None and x > hi):
        raise Reject('integer outside schema bounds')
    return x


def rat(data):
    if not isinstance(data, list) or len(data) != 2:
        raise Reject('rational must be [numerator, denominator]')
    a, b = integer(data[0]), integer(data[1], 1)
    if max(abs(a).bit_length(), b.bit_length()) > MAX_BITS:
        raise Limit('rational bit cap')
    if gcd(abs(a), b) != 1:
        raise Reject('rational not in canonical form')
    return Q(a, b)


def qjson(q):
    q = Q(q)
    return [q.numerator, q.denominator]


@dataclass(frozen=True)
class P:
    n: int
    terms: tuple[tuple[tuple[int, ...], Q], ...]

    @staticmethod
    def make(n, terms):
        d = {}
        it = terms.items() if hasattr(terms, 'items') else terms
        for e, c in it:
            e, c = tuple(e), Q(c)
            if len(e) != n or any(type(v) is not int or v < 0 for v in e):
                raise Reject('invalid monomial')
            if any(v > MAX_EXP for v in e):
                raise Limit('polynomial exponent cap')
            if c:
                d[e] = d.get(e, Q(0)) + c
        d = {e:c for e,c in d.items() if c}
        if len(d) > MAX_TERMS:
            raise Limit('polynomial term cap')
        if any(max(abs(c.numerator).bit_length(), c.denominator.bit_length()) > MAX_BITS for c in d.values()):
            raise Limit('coefficient bit cap')
        return P(n, tuple(sorted(d.items())))

    @staticmethod
    def const(n, c=0):
        return P.make(n, [((0,)*n, Q(c))])

    @staticmethod
    def var(n, i):
        e = [0]*n
        e[i] = 1
        return P.make(n, [(e, 1)])

    def __bool__(self): return bool(self.terms)

    def __add__(self, b):
        if not isinstance(b, P): b = P.const(self.n, b)
        if b.n != self.n: raise Reject('ring mismatch')
        return P.make(self.n, self.terms+b.terms)

    __radd__ = __add__

    def __neg__(self): return P.make(self.n, [(e,-c) for e,c in self.terms])
    def __sub__(self, b): return self + (-b)
    def __rsub__(self, b): return -self+b

    def __mul__(self, b):
        if not isinstance(b, P): b=P.const(self.n,b)
        if b.n != self.n: raise Reject('ring mismatch')
        if len(self.terms)*len(b.terms) > 4_000_000:
            raise Limit('polynomial product cap')
        return P.make(self.n, [(tuple(x+y for x,y in zip(e,f)),c*d)
                              for e,c in self.terms for f,d in b.terms])
    __rmul__ = __mul__

    def __pow__(self, k):
        integer(k,0,MAX_EXP)
        a, b = P.const(self.n,1), self
        while k:
            if k & 1: a=a*b
            k >>= 1
            if k: b=b*b
        return a

    def eval(self, xs):
        if len(xs)!=self.n: raise Reject('evaluation arity')
        if any(not isinstance(x,(int,Q)) or isinstance(x,bool) for x in xs):
            raise Reject('only exact rational evaluation')
        out=Q(0)
        for e,c in self.terms:
            for x,k in zip(xs,e): c*=Q(x)**k
            out+=c
        return out

    def data(self): return [[list(e),qjson(c)] for e,c in self.terms]


def poly(data, n):
    if not isinstance(data,list) or len(data)>MAX_TERMS: raise Reject('polynomial encoding')
    rows=[]; prev=None
    for row in data:
        if not isinstance(row,list) or len(row)!=2 or not isinstance(row[0],list):
            raise Reject('polynomial row')
        e=tuple(integer(v,0,MAX_EXP) for v in row[0])
        if len(e)!=n or (prev is not None and e<=prev):
            raise Reject('monomials must be distinct and sorted')
        c=rat(row[1])
        if not c: raise Reject('explicit zero coefficient')
        rows.append((e,c));prev=e
    return P.make(n,rows)


def eye(d,n):
    return [[P.const(n,int(i==j)) for j in range(d)] for i in range(d)]


def matmul(A,B):
    d=len(A); n=A[0][0].n
    if len(B)!=d or any(len(row)!=d for row in A+B): raise Reject('matrix shape')
    C=[[P.const(n) for _ in range(d)] for _ in range(d)]
    for i in range(d):
        for k in range(d):
            if not A[i][k]: continue
            for j in range(d):
                if B[k][j]: C[i][j]=C[i][j]+A[i][k]*B[k][j]
    return C


def trace(A): return sum((A[i][i] for i in range(len(A))),P.const(A[0][0].n))


def sgn(x): return (x>0)-(x<0)


def variations(signs):
    nonzero=[s for s in signs if s]
    if any(s not in (-1,1) for s in nonzero): raise Reject('invalid sign')
    return sum(a!=b for a,b in zip(nonzero,nonzero[1:]))


def signature_from_signs(signs):
    d=len(signs)-1
    if not signs or signs[0]!=1: raise Reject('characteristic polynomial not monic')
    return variations(signs)-variations([s*((-1)**(d-i)) for i,s in enumerate(signs)])
