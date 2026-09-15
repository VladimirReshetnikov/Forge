"""Exact univariate interval certificates, including even-multiplicity zeros.

Search uses SymPy factorization as an oracle. Checking uses only Fraction/Poly.
A certificate is p=q^2*r plus a checked Sturm chain showing r has no root in
(a,b), with r((a+b)/2)>0. Endpoint values of p are checked separately.
This Python implementation is tested, not formally verified.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from .poly import Poly


def derivative(p: Poly) -> Poly:
    if p.n != 1:
        raise ValueError('univariate polynomial required')
    return Poly.make(1,[((e[0]-1,),c*e[0]) for e,c in p.terms if e[0]])


def remainder(a: Poly,b: Poly) -> Poly:
    if a.n != 1 or b.n != 1 or not b.terms:
        raise ValueError('invalid univariate division')
    r=a
    while r.terms and r.degree >= b.degree:
        q=Poly.make(1,[((r.degree-b.degree,),r.terms[-1][1]/b.terms[-1][1])])
        r-=q*b
    return r


def sturm_chain(p: Poly) -> tuple[Poly,...]:
    if p.n != 1 or not p.terms:
        raise ValueError('nonzero univariate polynomial required')
    result=[p]
    d=derivative(p)
    if not d.terms:
        return tuple(result)
    result.append(d)
    while True:
        r=-remainder(result[-2],result[-1])
        if not r.terms:
            return tuple(result)
        result.append(r)


def side_sign(p: Poly,point: Q,direction: int) -> int:
    """Sign in a punctured neighborhood point+h with sign(h)=direction."""
    if direction not in (-1,1) or not p.terms:
        raise ValueError('invalid one-sided sign query')
    order=0
    while p.terms:
        v=p.evaluate([point])
        if v:
            return (1 if v>0 else -1)*direction**order
        p=derivative(p)
        order+=1
    raise AssertionError('nonzero polynomial must have a nonzero derivative')


def variations(signs) -> int:
    return sum(a!=b for a,b in zip(signs,signs[1:]))


def open_root_count(chain: tuple[Poly,...],a: Q,b: Q) -> int:
    return variations([side_sign(p,a,1) for p in chain])-variations([side_sign(p,b,-1) for p in chain])


@dataclass(frozen=True)
class UnivariateCertificate:
    square: Poly
    residual: Poly
    chain: tuple[Poly,...]


def check_univariate(p: Poly,a: Q,b: Q,cert: UnivariateCertificate,
                     max_degree: int=256) -> bool:
    try:
        if p.n!=1 or not isinstance(a,Q) or not isinstance(b,Q) or not a<b:
            return False
        if not isinstance(cert,UnivariateCertificate):
            return False
        if any(q.n!=1 or q.degree>max_degree for q in [p,cert.square,cert.residual,*cert.chain]):
            return False
        if len(cert.chain)>max_degree+1 or not cert.residual.terms:
            return False
        if cert.square**2*cert.residual != p:
            return False
        # Recompute every signed remainder, rather than trust a root count field.
        if cert.chain != sturm_chain(cert.residual):
            return False
        if cert.chain[-1].degree!=0:  # enforce square-free residual
            return False
        if open_root_count(cert.chain,a,b)!=0:
            return False
        return (cert.residual.evaluate([(a+b)/2])>0 and
                p.evaluate([a])>=0 and p.evaluate([b])>=0)
    except (TypeError,ValueError,AttributeError,IndexError):
        return False


def univariate_search(p: Poly,a: Q,b: Q) -> UnivariateCertificate | None:
    if p.n!=1 or not isinstance(a,Q) or not isinstance(b,Q) or not a<b:
        raise ValueError('univariate polynomial and rational interval required')
    import sympy as sp
    x=sp.Symbol('x')
    if not p.terms:
        r=Poly.const(1,1)
        return UnivariateCertificate(Poly.const(1,0),r,(r,))
    s=sp.Poly.from_dict({e:sp.Rational(c.numerator,c.denominator) for e,c in p.terms},x)
    coefficient,factors=s.factor_list()
    square=Poly.const(1,1)
    residual=Poly.const(1,Q(int(coefficient.p),int(coefficient.q)))
    for f,m in factors:
        factor=Poly.make(1,[(e,Q(int(c.p),int(c.q))) for e,c in f.terms()])
        square*=factor**(m//2)
        if m%2:
            residual*=factor
    cert=UnivariateCertificate(square,residual,sturm_chain(residual))
    return cert if check_univariate(p,a,b,cert) else None


def univariate_json(cert: UnivariateCertificate) -> dict:
    return {'square':cert.square.json(),'residual':cert.residual.json(),
            'chain':[p.json() for p in cert.chain]}
