"""Search-free certificate validators. Takes the authoritative problem separately.

These execute exact mathematical checks, but are neither formally verified nor
connected to the Lean kernel. They certify only their explicitly encoded models.
"""
from fractions import Fraction as Q
from .exact import *

def _model(p):
    fields(p,{'kind','dimension','initial','output','transitions'})
    if p['kind']!='linear-word': raise Invalid('model kind')
    d=integer(p['dimension'],1,MAX_DIM)
    u=vector(p['initial'],d); v=vector(p['output'],d)
    if type(p['transitions']) is not list or not 1<=len(p['transitions'])<=32:
        raise Invalid('transition count')
    ms=[matrix(m,d,d) for m in p['transitions']]
    return d,u,v,ms

def linear(p,c):
    try:
        d,u,v,ms=_model(p)
        fields(c,{'kind','basis','initial_coordinates','actions'})
        if c['kind']!='linear-closure' or type(c['basis']) is not list: return False
        r=len(c['basis'])
        if r>d: return False
        b=matrix(c['basis'],r,d); a=vector(c['initial_coordinates'],r)
        if type(c['actions']) is not list or len(c['actions'])!=len(ms): return False
        acts=[matrix(x,r,r) for x in c['actions']]
        if rowmul(a,b,d)!=u: return False
        if any(dot(row,v) for row in b): return False
        return all(matmul(b,m,d)==matmul(x,b,d) for m,x in zip(ms,acts))
    except (Invalid,TypeError,ValueError,OverflowError): return False

def counterexample(p,c):
    try:
        d,u,v,ms=_model(p); fields(c,{'kind','word','value'})
        if c['kind']!='separating-word' or type(c['word']) is not list or len(c['word'])>MAX_DIM:
            return False
        for s in c['word']: u=rowmul(u,ms[integer(s,0,len(ms)-1)])
        value=rational(c['value'])
        return value!=0 and dot(u,v)==value
    except (Invalid,TypeError,ValueError,OverflowError): return False

def telescoper(p,c):
    """Safe shift basis for sum q^k*binom(n,k)^power, n>=0.

Checks a common-denominator identity on 0<=k<=n, then every exceptional
boundary k=n+t (1<=t<=order). End fluxes follow from the fixed support and
j<order. No sampling is used by this verifier.
"""
    try:
        fields(p,{'kind','power','weight'})
        if p['kind']!='binomial-power-sum': return False
        pwr=integer(p['power'],1,8); q=rational(p['weight'])
        fields(c,{'kind','operator','flux'})
        if c['kind']!='shifted-binomial-telescoper': return False
        aa=decode_operator(c['operator']); r=len(aa)-1
        if not 1<=r<=6 or type(c['flux']) is not list or len(c['flux'])!=r: return False
        ps=[decode_poly(z) for z in c['flux']]
        # RN_i = D * binom(n+i,k)^p / binom(n,k)^p.
        rn=[]
        for i in range(r+1):
            z=const(1)
            for h in range(1,i+1): z=mul(z,power(add(mon(1),const(h)),pwr))
            for h in range(i+1,r+1): z=mul(z,power(add(sub(mon(1),mon(0,1)),const(h)),pwr))
            rn.append(z)
        residual={}
        for ai,ri in zip(aa,rn): residual=add(residual,mul(ai,ri))
        for j,pj in enumerate(ps):
            rm=mon(0,pwr)
            for h in range(1,j+1): rm=mul(rm,power(add(mon(1),const(h)),pwr))
            for h in range(j+2,r+1): rm=mul(rm,power(add(sub(mon(1),mon(0,1)),const(h)),pwr))
            residual=sub(residual,scale(mul(shift(pj,dk=1),rn[j]),q))
            residual=add(residual,mul(pj,rm))
        if residual: return False
        # Boundary identity after factoring q^(n+t), WITHOUT dividing by it.
        for t in range(1,r+1):
            residual={}
            for i,ai in enumerate(aa):
                residual=add(residual,mul(ai,power(choose_small(i,i-t),pwr)))
            for j,pj in enumerate(ps):
                residual=sub(residual,scale(mul(diagonal(pj,t+1),power(choose_small(j,j-t),pwr)),q))
                residual=add(residual,mul(diagonal(pj,t),power(choose_small(j,j-t+1),pwr)))
            if residual: return False
        return True
    except (Invalid,TypeError,ValueError,OverflowError): return False

def ore_identity(p,c):
    """Check a common LEFT multiple, not an unproved minimality assertion."""
    try:
        fields(p,{'kind','left','right'})
        if p['kind']!='common-left-multiple': return False
        a=decode_operator(p['left']); b=decode_operator(p['right'])
        fields(c,{'kind','common','left_multiplier','right_multiplier'})
        if c['kind']!='ore-multiple': return False
        l=decode_operator(c['common']); u=decode_operator(c['left_multiplier']); v=decode_operator(c['right_multiplier'])
        return ore_mul(u,a)==l==ore_mul(v,b)
    except (Invalid,TypeError,ValueError,OverflowError): return False

def singularity_plan(p,c):
    """Checks which values must be proved equal; does not prove those equalities."""
    try:
        fields(p,{'kind','operator'})
        if p['kind']!='recurrence-equality-plan': return False
        aa=decode_operator(p['operator']); r=len(aa)-1
        if r<1: return False
        lead=aa[-1]; deg=max(i for i,j in lead)
        top=lead[(deg,0)]
        fields(c,{'kind','bound','singular_indices','seed_indices'})
        if c['kind']!='singularity-cover': return False
        bound=integer(c['bound'],0,100000)
        # Standard Cauchy bound: every root has |z| <= 1+max |a_i/a_d|.
        if deg==0:
            if bound!=0: return False
        else:
            rho=1+max((abs(lead.get((i,0),0)/top) for i in range(deg)),default=Q(0))
            if bound<rho: return False
        actual=[i for i in range(bound+1) if evalp(lead,i)==0]
        seeds=sorted(set(range(r))|{i+r for i in actual})
        for key in ('singular_indices','seed_indices'):
            if type(c[key]) is not list: return False
            for x in c[key]: integer(x,0,100016)
        return c['singular_indices']==actual and c['seed_indices']==seeds
    except (Invalid,TypeError,ValueError,OverflowError): return False

CHECKERS={'linear':linear,'counterexample':counterexample,'telescoper':telescoper,
          'ore':ore_identity,'singularities':singularity_plan}

def verify_bundle(bundle):
    try:
        fields(bundle,{'checker','problem','certificate'})
        if type(bundle['checker']) is not str: return False
        fn=CHECKERS.get(bundle['checker'])
        return fn is not None and fn(bundle['problem'],bundle['certificate'])
    except (Invalid,TypeError,ValueError,OverflowError): return False
