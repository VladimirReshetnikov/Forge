"""Untrusted rational point and root-bracket discovery."""
from __future__ import annotations
from fractions import Fraction as F
from .check import decode, derivative
from .enclosure import evaluate, scale, rr, ii
from .model import ExpPoly


def refute(f: ExpPoly, points=None, degrees=(8,16,32)) -> dict:
    if points is None:
        points=[F(0)]+[F(k,4) for k in range(1,33)]
    t=decode(f.payload())
    for p in points:
        if p<0: continue
        for degree in degrees:
            v=evaluate(t,(p,p),degree)
            if v[1]<0:
                return {'status':'certificate','certificate':{'kind':'negative_point',
                        'point':rr(p),'degree':degree,'enclosure':ii(v)}}
    return {'status':'unknown'}


def cover(terms,a,b,direction,degree=16,depth=8):
    v=scale(evaluate(terms,(a,b),degree),F(direction))
    if v[0]>0: return {'kind':'leaf','degree':degree,'enclosure':ii(v)}
    if depth<=0: return None
    m=(a+b)/2
    left=cover(terms,a,m,direction,degree,depth-1)
    if left is None: return None
    right=cover(terms,m,b,direction,degree,depth-1)
    if right is None: return None
    return {'kind':'split','cut':rr(m),'left':left,'right':right}


def root(f: ExpPoly,a: F,b: F,degree=16,depth=8) -> dict:
    if a>=b: raise ValueError('empty or reversed bracket')
    terms=decode(f.payload())
    va=evaluate(terms,(a,a),degree); vb=evaluate(terms,(b,b),degree)
    direction=1 if va[1]<0<vb[0] else -1 if vb[1]<0<va[0] else 0
    if not direction: return {'status':'unknown_endpoints'}
    tree=cover(derivative(terms),a,b,direction,degree,depth)
    if tree is None: return {'status':'unknown_derivative'}
    return {'status':'certificate','problem':{'kind':'unique_root','terms':f.payload(),
                   'interval':[rr(a),rr(b)]},
            'certificate':{'kind':'unique_root','direction':direction,'degree':degree,
                'left_value':ii(scale(va,F(direction))),
                'right_value':ii(scale(vb,F(direction))),'derivative_cover':tree}}
