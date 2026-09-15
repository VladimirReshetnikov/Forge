"""Exact Bernstein coefficient search with rational box subdivision."""
from fractions import Fraction as Q
from itertools import product
from math import comb
from .polynomial import Poly
from .checkers import BernsteinLeaf, BernsteinSplit, BernsteinTree, check_bernstein


def coefficients(p: Poly, box: tuple[tuple[Q,Q],...]) -> tuple[tuple[int,...],tuple]:
    if len(box)!=p.nvars or any(a>=b for a,b in box):
        raise ValueError('strictly positive box widths required')
    ts=[Poly.variable(p.nvars,i) for i in range(p.nvars)]
    transformed=p.substitute(a+(b-a)*t for (a,b),t in zip(box,ts))
    degrees=tuple(max((m[i] for m,_ in transformed.terms),default=0) for i in range(p.nvars))
    coeffs=[]
    for k in product(*(range(d+1) for d in degrees)):
        c=Q(0)
        for m,a in transformed.terms:
            if all(mi<=ki for mi,ki in zip(m,k)):
                v=a
                for ki,mi,di in zip(k,m,degrees):
                    v*=Q(comb(ki,mi),comb(di,mi))
                c+=v
        coeffs.append((k,c))
    return degrees,tuple(coeffs)


def discover(p: Poly,box: tuple[tuple[Q,Q],...],*,depth: int=8) -> BernsteinTree | None:
    degrees,cs=coefficients(p,box)
    if all(c>=0 for _,c in cs):
        return BernsteinLeaf(box,degrees,cs)
    if depth<=0:
        return None
    # Width-based bisection is intentionally simple and deterministic.
    axis=max(range(p.nvars),key=lambda i:box[i][1]-box[i][0])
    a,b=box[axis]; cut=(a+b)/2
    bl=list(box); br=list(box); bl[axis]=(a,cut); br[axis]=(cut,b)
    l=discover(p,tuple(bl),depth=depth-1)
    if l is None: return None
    r=discover(p,tuple(br),depth=depth-1)
    if r is None: return None
    return BernsteinSplit(box,axis,cut,l,r)


def leaves(tree: BernsteinTree) -> int:
    return 1 if isinstance(tree,BernsteinLeaf) else leaves(tree.left)+leaves(tree.right)
