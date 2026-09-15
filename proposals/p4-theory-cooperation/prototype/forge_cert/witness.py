"""Finite-residue witness synthesis with universally meaningful certificates."""
from math import gcd

def synthesize(a:int,b:int,m:int):
    """Find offsets d_r so n <= n+d_(n mod m) < n+m and a*k == b mod m."""
    if any(type(x) is not int for x in (a,b,m)) or m<1:
        raise ValueError('expected integer a,b and positive m')
    if b%gcd(a,m):return None
    offsets=[]
    for r in range(m):
        d=next((d for d in range(m) if (a*(r+d)-b)%m==0),None)
        if d is None:return None
        offsets.append(d)
    return {'offsets':offsets}

def verify(a,b,m,cert):
    """Finite checker + the mathematical quotient/remainder lemma in article."""
    try:
        ds=cert['offsets']
        return type(m) is int and m>0 and len(ds)==m and all(
            type(d) is int and 0<=d<m and (a*(r+d)-b)%m==0 for r,d in enumerate(ds))
    except (KeyError,TypeError,ValueError):return False

def instantiate(n,m,cert):
    if type(n) is not int or m<1:raise ValueError('invalid input')
    return n+cert['offsets'][n%m]
