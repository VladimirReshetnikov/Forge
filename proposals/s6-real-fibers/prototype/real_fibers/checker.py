"""Independent replay: triangular reduction, trace construction, Newton identities.

No import of SymPy, NumPy, a root solver, or the producer is permitted here.
Theorems about Hermite signatures are mathematical foundations, not proved by Python.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
from math import prod
from .exact import P, Reject, Limit, integer, poly, rat, eye, matmul, trace, sgn, signature_from_signs
from .logic import indicator, validate_formula

@dataclass
class Fiber:
    k:int
    n:int
    degrees:tuple
    fs:list
    qs:list
    formula:list
    basis:list
    tails:list

    @staticmethod
    def parse(p):
        if not isinstance(p,dict) or set(p)!={'schema','parameters','degrees','equations','atoms','formula'}:
            raise Reject('problem keys')
        if p['schema']!='forge-real-fiber-v1':raise Reject('problem schema')
        k=integer(p['parameters'],0,4)
        if not isinstance(p['degrees'],list):raise Reject('degrees')
        deg=tuple(integer(d,1,12) for d in p['degrees']);n=len(deg)
        if not 1<=n<=4 or prod(deg)>12:raise Limit('fiber dimension cap')
        if not isinstance(p['equations'],list) or len(p['equations'])!=n:raise Reject('equations')
        if not isinstance(p['atoms'],list) or len(p['atoms'])>6:raise Limit('atom cap')
        fs=[poly(f,k+n) for f in p['equations']];qs=[poly(q,k+n) for q in p['atoms']]
        tails=[]
        for i,(f,d) in enumerate(zip(fs,deg)):
            lead=P.var(k+n,k+i)**d
            tail=f-lead
            for e,c in tail.terms:
                if e[k+i]>=d or any(e[j] for j in range(k+i+1,k+n)):
                    raise Reject('not a monic triangular equation')
            # Monicity follows because the sole leading term was subtracted.
            tails.append(-tail)
        validate_formula(p['formula'],len(qs))
        basis=list(product(*(range(d) for d in deg)))
        return Fiber(k,n,deg,fs,qs,p['formula'],basis,tails)

    @property
    def d(self):return len(self.basis)

    def basis_poly(self,e):return P.make(self.k+self.n,[((0,)*self.k+tuple(e),1)])

    def reduce(self,p):
        """Substitute highest fiber variable first; well-founded triangular order."""
        for i in reversed(range(self.n)):
            axis=self.k+i;d=self.degrees[i];steps=0
            while any(e[axis]>=d for e,c in p.terms):
                out=P.const(p.n)
                for e,c in p.terms:
                    if e[axis]<d:out=out+P.make(p.n,[(e,c)])
                    else:
                        ee=list(e);ee[axis]-=d
                        out=out+P.make(p.n,[(ee,c)])*self.tails[i]
                p=out;steps+=1
                if steps>2048:raise Limit('normal form cap')
        return p

    def trace_mul(self,p):
        """Trace by diagonal coefficients of independently reduced p*b_j."""
        out=P.const(self.k)
        for b in self.basis:
            r=self.reduce(p*self.basis_poly(b))
            out=out+P.make(self.k,[(e[:self.k],c) for e,c in r.terms if e[self.k:]==b])
        return out

    def hermite(self,e):
        q=P.const(self.k+self.n,1)
        for a,j in zip(self.qs,e):q=self.reduce(q*(a**j))
        H=[[P.const(self.k) for _ in self.basis] for _ in self.basis]
        for i,bi in enumerate(self.basis):
            for j in range(i,self.d):
                bj=self.basis[j]
                h=self.trace_mul(self.reduce(q*self.basis_poly(tuple(a+b for a,b in zip(bi,bj)))))
                H[i][j]=H[j][i]=h
        return H


def check_charpoly(H,cs):
    d=len(H);one=P.const(H[0][0].n,1)
    if len(cs)!=d+1 or cs[0]!=one:raise Reject('characteristic coefficient shape')
    powers=[];T=eye(d,one.n)
    for i in range(1,d+1):
        T=matmul(T,H);powers.append(trace(T))
    for j in range(1,d+1):
        lhs=j*cs[j]
        rhs=-sum((cs[j-i]*powers[i-1] for i in range(1,j+1)),P.const(one.n))
        if lhs!=rhs:raise Reject('Newton identity failed')


@dataclass
class CheckedFiber:
    problem:dict
    fiber:Fiber
    terms:list

    def count_by_sign(self,sign_of):
        out=Q(0)
        for e,c,cs in self.terms:
            out+=c*signature_from_signs([sign_of(a) for a in cs])
        if out.denominator!=1 or not 0<=out<=self.fiber.d:
            raise Reject('impossible root count')
        return int(out)

    def count(self,parameters):
        if len(parameters)!=self.fiber.k:raise Reject('parameter arity')
        return self.count_by_sign(lambda a:sgn(a.eval(parameters)))

    def support(self):
        return sorted({p for _,_,cs in self.terms for p in cs}, key=lambda p:p.terms)


def verify(problem,certificate):
    f=Fiber.parse(problem)
    if not isinstance(certificate,dict) or set(certificate)!={'schema','queries'}:
        raise Reject('certificate keys')
    if certificate['schema']!='hermite-charpoly-v1':raise Reject('certificate schema')
    ind=indicator(f.formula,len(f.qs));want=list(ind.terms)
    rows=certificate['queries']
    if not isinstance(rows,list) or len(rows)!=len(want):raise Reject('missing or extra query')
    if len(rows)>256:raise Limit('query cap')
    terms=[]
    for row,(e,c) in zip(rows,want):
        if not isinstance(row,dict) or set(row)!={'exponents','coefficient','hermite','charpoly'}:
            raise Reject('query keys')
        if row['exponents']!=list(e) or any(type(i)is not int for i in row['exponents']):
            raise Reject('wrong sign monomial')
        if rat(row['coefficient'])!=c:raise Reject('wrong formula coefficient')
        h=row['hermite']
        if not isinstance(h,list) or len(h)!=f.d or any(not isinstance(r,list) or len(r)!=f.d for r in h):
            raise Reject('Hermite matrix dimensions')
        H=[[poly(a,f.k) for a in r] for r in h]
        if H!=f.hermite(e):raise Reject('trace-form matrix failed')
        if not isinstance(row['charpoly'],list):raise Reject('charpoly encoding')
        cs=[poly(a,f.k) for a in row['charpoly']]
        check_charpoly(H,cs);terms.append((e,c,cs))
    return CheckedFiber(problem,f,terms)
