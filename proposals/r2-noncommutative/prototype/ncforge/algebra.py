"""Exact search-side word algebra. No symbol is silently commuted."""
from __future__ import annotations
from fractions import Fraction as F
from itertools import product
from typing import Iterable

Word = tuple[int, ...]
Poly = dict[Word, F]

def clean(p: Poly) -> Poly:
    return {w: F(c) for w, c in p.items() if c}

def add(p: Poly, q: Poly, scale: F = F(1)) -> Poly:
    r = p.copy()
    for w, c in q.items():
        r[w] = r.get(w, F(0)) + scale*c
        if not r[w]: del r[w]
    return r

def scale(p: Poly, a: F | int) -> Poly:
    return clean({w: a*c for w, c in p.items()})

def mul(p: Poly, q: Poly) -> Poly:
    r: Poly = {}
    for u, a in p.items():
        for v, b in q.items():
            r[u+v] = r.get(u+v, F(0)) + a*b
    return clean(r)

def sandwich(p: Poly, u: Word = (), v: Word = ()) -> Poly:
    return {u+w+v: c for w, c in p.items()}

def star(p: Poly, involution: tuple[int, ...]) -> Poly:
    return {tuple(involution[i] for i in reversed(w)): c for w, c in p.items()}

def power(p: Poly, n: int) -> Poly:
    if type(n) is not int or n < 0: raise ValueError('natural exponent required')
    q = one()
    while n:
        if n & 1: q = mul(q,p)
        p = mul(p,p); n //= 2
    return q

def one() -> Poly: return {(): F(1)}
def var(i: int) -> Poly: return {(i,): F(1)}
def degree(p: Poly) -> int: return max(map(len,p), default=0)
def homogeneous(p: Poly) -> bool: return len({len(w) for w in p}) <= 1

def words(m: int, bound: int, exact: bool = False) -> list[Word]:
    return [w for k in ([bound] if exact else range(bound+1)) for w in product(range(m),repeat=k)]

def cyclic_word(w: Word) -> Word:
    return min((w[k:]+w[:k] for k in range(len(w))), default=())

def cyclic(p: Poly) -> Poly:
    r: Poly = {}
    for w,c in p.items():
        v=cyclic_word(w); r[v]=r.get(v,F(0))+c
    return clean(r)

def encode(p: Poly) -> list:
    return [[list(w),c.numerator,c.denominator] for w,c in sorted(clean(p).items())]

def rational(q: F | int) -> list[int]:
    q=F(q); return [q.numerator,q.denominator]

def problem(p: Poly, relations: list[Poly], m: int, kind='equality',
            positives: list[Poly] | None=None, involution: tuple[int,...] | None=None) -> dict:
    return {'schema':'ncforge.problem.v1','kind':kind,'atoms':m,
            'involution':list(range(m)) if involution is None else list(involution),
            'target':encode(p),'relations':[encode(r) for r in relations],
            'positives':[encode(g) for g in (positives or [])]}

class Echelon:
    """Incremental sparse row basis, with exact original-column provenance."""
    def __init__(self):
        self.rows: dict[Word,tuple[Poly,dict[int,F]]] = {}

    def reduce(self, p: Poly) -> tuple[Poly,dict[int,F]]:
        q=p.copy(); coeff: dict[int,F]={}
        for pivot in sorted(self.rows):
            a=q.get(pivot,F(0))
            if not a: continue
            row,prov=self.rows[pivot]
            q=add(q,row,-a)
            for j,c in prov.items():
                coeff[j]=coeff.get(j,F(0))+a*c
                if not coeff[j]: del coeff[j]
        return q,coeff

    def insert(self,p: Poly,j:int) -> bool:
        q,used=self.reduce(p)
        if not q: return False
        pivot=min(q); a=q[pivot]
        prov={k:-v/a for k,v in used.items()}
        prov[j]=prov.get(j,F(0))+1/a
        self.rows[pivot]=(scale(q,1/a),prov)
        return True

    def solve(self,p:Poly) -> dict[int,F] | None:
        rem,c=self.reduce(p)
        return None if rem else c


def ldl_squares(matrix: list[list[F]]) -> list[tuple[F,list[F]]] | None:
    """Exact pivoted LDL, returning rows l with Q=sum d*l*l^T, or not PSD."""
    n=len(matrix)
    if any(len(r)!=n for r in matrix): raise ValueError('square matrix required')
    if any(matrix[i][j]!=matrix[j][i] for i in range(n) for j in range(n)): return None
    q=[[F(x) for x in row] for row in matrix]; active=list(range(n)); out=[]
    while active:
        if any(q[i][i]<0 for i in active): return None
        piv=next((i for i in active if q[i][i]>0),None)
        if piv is None:
            if any(q[i][j] for i in active for j in active): return None
            break
        d=q[piv][piv]; l=[F(0)]*n; l[piv]=1
        rest=[i for i in active if i!=piv]
        for i in rest: l[i]=q[piv][i]/d
        out.append((d,l))
        for i in rest:
            for j in rest: q[i][j]-=d*l[i]*l[j]
        active=rest
    return out
