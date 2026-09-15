"""Small, bounded, standard-library-only certificate arithmetic.

No symbolic algebra package and no search routine is imported by this module.
Polynomials are sparse dictionaries in the two variables n,k. Public decoders
reject floats, bools, noncanonical rationals, repeated terms, and extra fields.
The bounds are research safeguards, not a hostile-input security audit.
"""
from fractions import Fraction as Q
from math import comb, gcd
from typing import Any

MAX_DIM = 64
MAX_TERMS = 4096
MAX_DEGREE = 128
MAX_BITS = 4096

class Invalid(ValueError):
    pass

def integer(x: Any, lo: int, hi: int) -> int:
    if type(x) is not int or not lo <= x <= hi:
        raise Invalid('integer outside the declared domain')
    return x

def fields(obj: Any, keys: set[str]) -> None:
    if type(obj) is not dict or set(obj) != keys:
        raise Invalid('unexpected or missing object fields')

def rational(x: Any) -> Q:
    if type(x) is not list or len(x) != 2:
        raise Invalid('rational must be [numerator, denominator]')
    a,b=x
    if type(a) is not int or type(b) is not int or b <= 0:
        raise Invalid('invalid rational components')
    if max(abs(a).bit_length(),b.bit_length()) > MAX_BITS or gcd(a,b) != 1:
        raise Invalid('noncanonical or overlarge rational')
    return Q(a,b)

def encq(x: Q | int) -> list[int]:
    x=Q(x); return [x.numerator,x.denominator]

def vector(x: Any, length: int) -> list[Q]:
    if type(x) is not list or len(x) != length:
        raise Invalid('vector dimension mismatch')
    return [rational(v) for v in x]

def matrix(x: Any, rows: int, cols: int) -> list[list[Q]]:
    if type(x) is not list or len(x) != rows:
        raise Invalid('matrix dimension mismatch')
    return [vector(row,cols) for row in x]

def encvec(v): return [encq(x) for x in v]
def encmat(m): return [encvec(row) for row in m]

def rowmul(v, m, cols=None):
    if cols is None: cols=len(m[0]) if m else 0
    return [sum((v[i]*m[i][j] for i in range(len(v))),Q(0)) for j in range(cols)]

def matmul(a,b,cols=None):
    return [rowmul(row,b,cols) for row in a]

def dot(a,b): return sum((x*y for x,y in zip(a,b)),Q(0))

# Algebra on internal (already decoded) sparse polynomials.
def clean(p): return {m:Q(c) for m,c in p.items() if c}
def const(c): return {(0,0):Q(c)} if c else {}
def mon(a,b=0,c=1): return {(a,b):Q(c)} if c else {}
def add(a,b):
    d=dict(a)
    for m,c in b.items(): d[m]=d.get(m,Q(0))+c
    return clean(d)
def neg(a): return {m:-c for m,c in a.items()}
def sub(a,b): return add(a,neg(b))
def scale(a,c): return clean({m:v*c for m,v in a.items()})
def mul(a,b):
    d={}
    for (i,j),c in a.items():
        for (u,v),e in b.items():
            m=(i+u,j+v); d[m]=d.get(m,Q(0))+c*e
    return clean(d)
def power(a,p):
    out=const(1)
    for _ in range(p): out=mul(out,a)
    return out

def shift(a,dn=0,dk=0):
    d={}
    for (i,j),c in a.items():
        for u in range(i+1):
            for v in range(j+1):
                m=(u,v); z=c*comb(i,u)*dn**(i-u)*comb(j,v)*dk**(j-v)
                d[m]=d.get(m,Q(0))+z
    return clean(d)

def evalp(a,n,k=0): return sum((c*Q(n)**i*Q(k)**j for (i,j),c in a.items()),Q(0))

def diagonal(a,t):
    """Substitute k=n+t, producing a polynomial in n."""
    out={}; base=add(mon(1),const(t))
    for (i,j),c in a.items(): out=add(out,mul(mon(i,c=c),power(base,j)))
    return out

def decode_poly(x: Any, univariate=False):
    if type(x) is not list or len(x)>MAX_TERMS: raise Invalid('polynomial term bound')
    out={}; prev=None
    for term in x:
        if type(term) is not list or len(term)!=4: raise Invalid('polynomial term format')
        i=integer(term[0],0,MAX_DEGREE); j=integer(term[1],0,MAX_DEGREE)
        if i+j>MAX_DEGREE or (univariate and j): raise Invalid('polynomial degree/domain')
        m=(i,j)
        if prev is not None and m<=prev: raise Invalid('unordered or repeated monomial')
        c=rational(term[2:])
        if not c: raise Invalid('explicit zero term')
        out[m]=c; prev=m
    return out

def encpoly(p): return [[i,j,*encq(c)] for (i,j),c in sorted(p.items()) if c]

def choose_small(nshift,d):
    """Polynomial binom(n+nshift,d); d<0 denotes the zero-extension tail."""
    if d<0: return {}
    ans=const(1)
    for h in range(d): ans=scale(mul(ans,add(mon(1),const(nshift-h))),Q(1,h+1))
    return ans

def decode_operator(x):
    if type(x) is not list or not 1<=len(x)<=17: raise Invalid('operator order bound')
    out=[decode_poly(c,True) for c in x]
    if not out[-1]: raise Invalid('zero leading operator coefficient')
    return out

def ore_mul(a,b):
    """(a_i(n) E^i)(b_j(n) E^j) = a_i(n)b_j(n+i) E^(i+j)."""
    out=[{} for _ in range(len(a)+len(b)-1)]
    for i,ai in enumerate(a):
        for j,bj in enumerate(b): out[i+j]=add(out[i+j],mul(ai,shift(bj,dn=i)))
    return out
