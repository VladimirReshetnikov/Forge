"""Algebraic-real witness replay for a concrete rational univariate fiber."""
from .checker import Fiber
from .exact import Reject,rat,sgn
from .logic import eval_formula
from .sturm import from_sparse,root_count,gcd,ev


def verify_witness(problem,certificate):
    f=Fiber.parse(problem)
    if f.k!=0 or f.n!=1:raise Reject('witness replay is concrete and univariate')
    if not isinstance(certificate,dict) or set(certificate)!={'schema','interval'} or certificate['schema']!='algebraic-witness-v1':
        raise Reject('witness schema')
    if not isinstance(certificate['interval'],list) or len(certificate['interval'])!=2:raise Reject('witness interval')
    l,r=map(rat,certificate['interval']);p=from_sparse(f.fs[0])
    if root_count(p,l,r)!=1:raise Reject('witness is not a uniquely isolated root')
    signs=[]
    for q in f.qs:
        a=from_sparse(q)
        if not a:signs.append(0);continue
        common=gcd(p,a)
        if root_count(common,l,r)==1:signs.append(0)
        else:
            if root_count(a,l,r)!=0:raise Reject('refine isolator to separate an unrelated atom root')
            signs.append(sgn(ev(a,(l+r)/2)))
    if not eval_formula(f.formula,signs):raise Reject('isolated root does not satisfy source formula')
    return {'interval':certificate['interval'],'atom_signs':signs,'distinct_root':True}
