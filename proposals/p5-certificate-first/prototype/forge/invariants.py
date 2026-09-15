"""Sample-propose / exact-validate polynomial induction-lemma discovery."""
from fractions import Fraction as Q
import sympy as sp
from .polynomial import Poly
from .checkers import InvariantCertificate,check_invariant


def additive_invariant(increment:Poly,*,initial:Q=Q(0),degree:int|None=None) -> InvariantCertificate|None:
    """For n'=n+1, s'=s+p(n), synthesize I(n,s)=s-Q(n).

A finite table proposes Q by interpolation. Acceptance depends exclusively on
an exact polynomial identity, never on agreeing with the sampled trajectory.
"""
    if increment.nvars!=1: raise ValueError('increment must be univariate')
    degree=increment.degree+1 if degree is None else degree
    if degree<0: raise ValueError('invalid degree')
    n=sp.Symbol('n'); acc=Q(initial); points=[]
    for k in range(degree+1):
        points.append((k,sp.Rational(acc.numerator,acc.denominator)))
        acc+=increment.eval([k])
    expr=sp.Poly(sp.interpolate(points,n),n)
    q=Poly.make(2,[((int(m[0]),0),Q(int(c.p),int(c.q))) for m,c in expr.terms()])
    nv,sv=Poly.variable(2,0),Poly.variable(2,1)
    p=increment.substitute([nv])
    cert=InvariantCertificate(sv-q,(Q(0),Q(initial)),(nv+1,sv+p))
    return cert if check_invariant(cert) else None
