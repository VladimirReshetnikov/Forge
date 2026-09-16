"""Exact rational enclosures and replay. No floating point, search, or CAS.

Shared by the enclosure proposer and checker; this is not an independent
implementation of the numerical kernel. See prototype/oracle.py for a
separate, non-authoritative Decimal sanity check.
"""
from __future__ import annotations
from fractions import Fraction as F
from functools import lru_cache
from .check import decode, derivative, fraction, checked_problem

Interval = tuple[F, F]


def rr(x: F): return [x.numerator, x.denominator]
def ii(a: Interval): return [rr(a[0]), rr(a[1])]
def plus(a: Interval,b: Interval) -> Interval: return (a[0]+b[0],a[1]+b[1])
def times(a: Interval,b: Interval) -> Interval:
    x = [u*v for u in a for v in b]
    return (min(x),max(x))
def scale(a: Interval,c: F) -> Interval: return times(a,(c,c))
def reciprocal(a: Interval) -> Interval:
    if a[0] <= 0 <= a[1]: raise ValueError('interval crosses zero')
    return (1/a[1],1/a[0])

def power(a: Interval,n: int) -> Interval:
    if type(n) is not int or n < 0: raise ValueError('bad power')
    if n == 0: return (F(1),F(1))
    if n % 2 == 0:
        lo = F(0) if a[0] <= 0 <= a[1] else min(a[0]**n,a[1]**n)
        return (lo,max(a[0]**n,a[1]**n))
    return (a[0]**n,a[1]**n)


@lru_cache(maxsize=4096)
def exp_bound(t: F, degree: int = 16) -> Interval:
    if type(t) is not F or type(degree) is not int or not 0 <= degree <= 64:
        raise ValueError('bad exponential enclosure input')
    if abs(t) > 64 or t.denominator.bit_length() > 128:
        raise ValueError('enclosure resource cap')
    u=abs(t); squarings=0
    while u > F(1,2):
        u /= 2; squarings += 1
    term=F(1); partial=F(1)
    for j in range(1,degree+1):
        term *= u/j
        partial += term
    next_term = term*u/(degree+1)
    ratio = u/(degree+2)
    bound=(partial,partial+next_term/(1-ratio))
    for _ in range(squarings): bound=(bound[0]**2,bound[1]**2)
    return reciprocal(bound) if t < 0 else bound


def evaluate(terms, domain: Interval, degree: int = 16) -> Interval:
    """Monomial natural interval extension; identities are NOT inferred."""
    a,b=domain
    if a>b: raise ValueError('reversed interval')
    out=(F(0),F(0))
    for (r,j),c in terms.items():
        lo,hi=sorted((r*a,r*b))
        e=(exp_bound(lo,degree)[0],exp_bound(hi,degree)[1])
        out=plus(out,scale(times(power(domain,j),e),c))
    return out


def check_refutation(problem, cert) -> bool:
    try:
        terms=checked_problem(problem)
        if set(cert) != {'kind','point','degree','enclosure'} or cert['kind'] != 'negative_point': return False
        p=fraction(cert['point'])
        if p<0: return False
        v=evaluate(terms,(p,p),cert['degree'])
        return ii(v)==cert['enclosure'] and v[1]<0
    except (ValueError,TypeError,KeyError,IndexError,AttributeError,OverflowError): return False


def _positive_cover(terms, a, b, tree, direction, budget):
    budget[0]-=1
    if budget[0]<0: return False
    if not isinstance(tree,dict): return False
    if tree.get('kind') == 'leaf':
        if set(tree) != {'kind','degree','enclosure'}: return False
        v=scale(evaluate(terms,(a,b),tree['degree']),F(direction))
        return ii(v)==tree['enclosure'] and v[0]>0
    if tree.get('kind') == 'split':
        if set(tree) != {'kind','cut','left','right'}: return False
        m=fraction(tree['cut'])
        return (a<m<b and _positive_cover(terms,a,m,tree['left'],direction,budget)
                and _positive_cover(terms,m,b,tree['right'],direction,budget))
    return False


def check_root(problem, cert) -> bool:
    try:
        if set(problem) != {'kind','terms','interval'} or problem['kind'] != 'unique_root': return False
        terms=decode(problem['terms'])
        a,b=map(fraction,problem['interval'])
        if a>=b: return False
        if set(cert) != {'kind','direction','degree','left_value','right_value','derivative_cover'} or cert['kind'] != 'unique_root': return False
        d=cert['direction']
        if type(d) is not int or d not in (-1,1): return False
        va=scale(evaluate(terms,(a,a),cert['degree']),F(d))
        vb=scale(evaluate(terms,(b,b),cert['degree']),F(d))
        if ii(va)!=cert['left_value'] or ii(vb)!=cert['right_value']: return False
        if not va[1]<0<vb[0]: return False
        return _positive_cover(derivative(terms),a,b,cert['derivative_cover'],d,[2048])
    except (ValueError,TypeError,KeyError,IndexError,AttributeError,OverflowError,RecursionError): return False
