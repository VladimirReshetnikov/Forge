#!/usr/bin/env python3
"""Recheck stored certificates without importing any numerical search library.

The decoder imposes modest syntactic limits. This is research tooling, not a
hardened service for hostile uploads. The checker is not formally verified.
"""
from __future__ import annotations
import argparse,json,re
from fractions import Fraction as Q
from pathlib import Path
from forge.poly import Poly
from forge.certificates import *
from forge.synthesis import check_recurrence,AffineWitness,check_affine_witness
from forge.univariate import UnivariateCertificate,check_univariate


def rational(x):
    if not isinstance(x,str) or len(x)>2500 or not re.fullmatch(r'-?[0-9]+(?:/[1-9][0-9]*)?',x):
        raise ValueError('invalid bounded rational')
    q=Q(x)
    if max(q.numerator.bit_length(),q.denominator.bit_length())>4096:
        raise ValueError('rational bit limit')
    return q


def polynomial(x):
    if not isinstance(x,dict) or set(x)!= {'n','terms'}:
        raise ValueError('invalid polynomial object')
    n=x['n'];ts=x['terms']
    if type(n) is not int or not 1<=n<=8 or not isinstance(ts,list) or len(ts)>5000:
        raise ValueError('polynomial shape/size limit')
    terms=[]
    for e,c in ts:
        if not isinstance(e,list) or len(e)!=n or any(type(k) is not int or k<0 for k in e) or sum(e)>256:
            raise ValueError('invalid monomial')
        terms.append((tuple(e),rational(c)))
    return Poly(n,tuple(terms))


def cone(x):
    if not isinstance(x,dict) or set(x)!={'terms','equality_multipliers'} or len(x['terms'])>5000:
        raise ValueError('invalid cone object')
    ts=[]
    for t in x['terms']:
        powers=t['powers']
        if len(powers)>32 or any(type(k) is not int or not 0<=k<=32 for k in powers):
            raise ValueError('invalid powers')
        ts.append(ConeTerm(rational(t['weight']),polynomial(t['square']),tuple(powers)))
    return ConeCertificate(tuple(ts),tuple(polynomial(p) for p in x['equality_multipliers']))


def tree(x,depth=0):
    if depth>64 or not isinstance(x,dict):raise ValueError('invalid tree/depth')
    if set(x)=={'leaf'}:return BernsteinLeaf(rational(x['leaf']))
    if set(x)!={'axis','point','left','right'}:raise ValueError('invalid split fields')
    return BernsteinSplit(x['axis'],rational(x['point']),tree(x['left'],depth+1),tree(x['right'],depth+1))


def verify(record):
    inp,c,f=record['input'],record['certificate'],record['family']
    if f in ('Quadratic SOS','Finite cone LP'):
        return check_cone(polynomial(inp['p']),[polynomial(p) for p in inp.get('inequalities',[])],[],cone(c))
    if f=='Bernstein box':
        box=tuple((rational(l),rational(u)) for l,u in inp['box'])
        return check_bernstein(polynomial(inp['p']),box,tree(c))
    if f=='Polynomial recurrence':
        return check_recurrence(polynomial(inp['step']),polynomial(inp['initial']),polynomial(c))
    if f=='Integral affine witness':
        cert=AffineWitness(tuple(tuple(rational(x) for x in r) for r in c['linear']),tuple(rational(x) for x in c['offset']))
        return check_affine_witness(inp['A'],inp['B'],inp['c'],cert,True)
    if f=='Univariate with zeros':
        cert=UnivariateCertificate(polynomial(c['square']),polynomial(c['residual']),tuple(polynomial(p) for p in c['chain']))
        a,b=map(rational,inp['interval'])
        return check_univariate(polynomial(inp['p']),a,b,cert)
    raise ValueError('unknown family')


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('path',nargs='?',type=Path,default=Path(__file__).resolve().parents[1]/'results/certificates.json')
    args=ap.parse_args()
    if args.path.stat().st_size>20_000_000:raise ValueError('file size limit')
    records=json.loads(args.path.read_text())
    if not isinstance(records,list) or len(records)>10000:raise ValueError('record limit')
    for r in records:
        if not verify(r):raise ValueError('REJECTED certificate '+str(r.get('id')))
    print(f'{len(records)}/{len(records)} certificates rechecked successfully (exact Python, not Lean).')


if __name__=='__main__':main()
