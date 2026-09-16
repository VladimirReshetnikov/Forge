"""Exact univariate rational polynomials and open-interval Sturm counts.

The checker constructs its own remainder sequence. Endpoints must not be
roots; infinite endpoints are represented by None. This is a research checker,
not a formal proof of Sturm's theorem.
"""
from fractions import Fraction as Q
from .exact import P, Reject, Limit, sgn, variations


def trim(p):
    p=list(map(Q,p))
    while p and p[-1]==0:p.pop()
    return tuple(p)


def from_sparse(p):
    if p.n!=1:raise Reject('not univariate')
    if not p.terms:return ()
    out=[Q(0)]*(max(e[0] for e,c in p.terms)+1)
    for e,c in p.terms:out[e[0]]=c
    return trim(out)


def to_sparse(p):return P.make(1,[((i,),c) for i,c in enumerate(p)])


def ev(p,x):
    r=Q(0)
    for c in reversed(p):r=r*x+c
    return r


def add(a,b):return trim([(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))])


def mul(a,b):
    if not a or not b:return ()
    out=[Q(0)]*(len(a)+len(b)-1)
    for i,c in enumerate(a):
        for j,d in enumerate(b):out[i+j]+=c*d
    return trim(out)


def derivative(p):return trim([i*p[i] for i in range(1,len(p))])


def divrem(a,b):
    if not b:raise Reject('polynomial division by zero')
    r=list(a);q=[Q(0)]*max(0,len(a)-len(b)+1)
    while len(r)>=len(b):
        k=len(r)-len(b);c=r[-1]/b[-1];q[k]=c
        for j,d in enumerate(b):r[k+j]-=c*d
        r=list(trim(r))
    return trim(q),trim(r)


def monic(a):return trim([c/a[-1] for c in a]) if a else ()


def gcd(a,b):
    while b:a,b=b,divrem(a,b)[1]
    return monic(a)


def squarefree(a):
    if not a:raise Reject('zero has no finite squarefree root cover')
    g=gcd(a,derivative(a));q,r=divrem(a,g)
    if r:raise Reject('internal exact-division failure')
    return monic(q)


def chain(a):
    if not a:raise Reject('Sturm input zero')
    out=[a];b=derivative(a)
    if not b:return out
    out.append(b)
    while True:
        r=divrem(out[-2],out[-1])[1]
        if not r:break
        # Positive scaling controls growth without changing signs.
        r=tuple(-c for c in r);scale=abs(r[-1]);r=tuple(c/scale for c in r)
        out.append(r)
    return out


def root_count(a,l=None,r=None):
    """Distinct real roots in (l,r); finite endpoints cannot be roots."""
    if not a:raise Reject('zero polynomial has infinitely many roots')
    if l is not None and r is not None and not l<r:raise Reject('interval order')
    if (l is not None and ev(a,l)==0) or (r is not None and ev(a,r)==0):
        raise Reject('root at an isolator endpoint')
    seq=chain(a)
    def vs(x,side):
        return variations([sgn(ev(p,x)) if x is not None else sgn(p[-1])*(side**(len(p)-1)) for p in seq])
    return vs(l,-1)-vs(r,1)


def root_product(polynomials,degree_cap=160):
    """Squarefree monic product of all nonconstant nonzero input polynomials."""
    out=(Q(1),)
    for p in polynomials:
        p=from_sparse(p)
        if len(p)>1:
            # lcm of squarefree factors avoids gratuitous repeated multiplication.
            p=squarefree(p);common=gcd(out,p);quotient,rem=divrem(p,common)
            if rem:raise Reject('product division failure')
            out=monic(mul(out,quotient))
            if len(out)-1>degree_cap:raise Limit('outer root-product degree cap')
    return out
