"""Bounded coefficient synthesis for sums of binomial(n,k)**m.

This is a deliberately explicit creative-telescoping ansatz, not a full
implementation of Zeilberger's algorithm. Search failure is inconclusive.
"""
from __future__ import annotations
from math import comb,gcd
from functools import reduce
import sympy as s
from .encode import polynomial

n,k=s.symbols('n k')

def discover(m,order,coefficient_degree,numerator_degree):
    r=order
    pmon=[n**i for i in range(coefficient_degree+1)]
    umon=sorted(s.itermonomials((n,k),numerator_degree),key=lambda t:(s.total_degree(t),str(t)))
    columns=[]
    for j in range(r+1):
        weight=s.prod((n+t)**m for t in range(1,j+1))*s.prod((n+t-k)**m for t in range(j+1,r+1))
        columns.extend(s.expand(z*weight) for z in pmon)
    columns.extend(s.expand(-((n+r-k)**m*z.subs(k,k+1)-k**m*z)) for z in umon)
    coeffs=[dict(s.Poly(c,n,k,domain=s.QQ).terms()) for c in columns]
    mons=sorted(set().union(*(set(c) for c in coeffs)))
    mat=s.Matrix([[c.get(e,0) for c in coeffs] for e in mons])
    null=mat.nullspace()
    width=len(pmon)
    for v in null:
        ps=[s.expand(sum(v[j*width+i]*pmon[i] for i in range(width))) for j in range(r+1)]
        if ps[-1]==0:
            continue
        u=s.expand(sum(v[(r+1)*width+i]*z for i,z in enumerate(umon)))
        common=s.gcd_list(ps+[u])
        if common!=0:
            ps=[s.cancel(p/common) for p in ps]; u=s.cancel(u/common)
        exprs=ps+[u]
        den=s.ilcm(*[c.q for f in exprs for c in s.Poly(f,n,k).coeffs()])
        exprs=[s.expand(den*f) for f in exprs]
        content=reduce(gcd,[abs(int(c)) for f in exprs for c in s.Poly(f,n,k).coeffs()])
        exprs=[s.expand(f/content) for f in exprs]
        ps,u=exprs[:-1],exprs[-1]
        if s.Poly(ps[-1],n).LC()<0:
            ps=[-p for p in ps]; u=-u
        problem={'kind':'telescoping_problem_v1','family':'binomial_power_sum','power':m}
        cert={'kind':'binomial_telescoper_v1','order':r,'coefficients':[polynomial(p,(n,)) for p in ps],
              'numerator':polynomial(u,(n,k)), 'initial_values':[sum(comb(i,j)**m for j in range(i+1)) for i in range(r)]}
        info={'power':m,'order':r,'unknowns':len(columns),'equations':len(mons),'nullity':len(null),
              'coefficients':[str(s.factor(p)) for p in ps],'numerator':str(s.factor(u)),
              'coefficient_degree_cap':coefficient_degree,'numerator_total_degree_cap':numerator_degree}
        return (problem,cert),info
    return None,{'reason':'no_telescoper_in_ansatz','unknowns':len(columns),'equations':len(mons),'nullity':len(null)}
