"""Independent SymPy symbolic cross-checks (test-only dependency)."""
from fractions import Fraction as Q
from itertools import product
from math import comb
import random
import pytest
import sympy as sp
from forge.poly import Poly
from forge.certificates import bernstein_coefficients
from forge.search import quadratic_sos


def symbolic(p, xs):
    return sp.Add(*(sp.Rational(c.numerator,c.denominator) *
                    sp.Mul(*(x**k for x,k in zip(xs,e))) for e,c in p.terms))


@pytest.mark.parametrize('seed',range(20))
def test_independent_bernstein_identity(seed):
    rng = random.Random(3000+seed)
    n = 1+seed%3
    variables = [Poly.var(n,i) for i in range(n)]
    xs = sp.symbols('x:'+str(n))
    exponents = list(product(range(3),repeat=n))
    p = Poly.make(n,[(e,Q(rng.randrange(-3,4),rng.randrange(1,4))) for e in exponents])
    box = tuple((Q(-i-2,3),Q(i+3,2)) for i in range(n))
    coeffs = bernstein_coefficients(p,box)
    degrees = [max(beta[i] for beta in coeffs) for i in range(n)]
    reconstructed = sp.Add(*(sp.Rational(c.numerator,c.denominator) *
        sp.Mul(*(comb(d,b)*x**b*(1-x)**(d-b) for x,b,d in zip(xs,beta,degrees)))
        for beta,c in coeffs.items()))
    transformed = symbolic(p,xs).subs({x:sp.Rational(l.numerator,l.denominator)+
        sp.Rational((u-l).numerator,(u-l).denominator)*x for x,(l,u) in zip(xs,box)},
        simultaneous=True)
    assert sp.expand(reconstructed-transformed) == 0


@pytest.mark.parametrize('seed',range(12))
def test_independent_quadratic_certificate(seed):
    rng=random.Random(5000+seed)
    n=1+seed%4
    variables=[Poly.var(n,i) for i in range(n)]
    xs=sp.symbols('x:'+str(n))
    p=Poly.const(n,0)
    for _ in range(n+1):
        q=sum((rng.randrange(-5,6)*x for x in variables),Poly.const(n,rng.randrange(-5,6)))
        p+=Q(rng.randrange(1,6),rng.randrange(1,6))*q*q
    cert=quadratic_sos(p)
    assert cert is not None
    expanded=sum((sp.Rational(t.weight.numerator,t.weight.denominator)*symbolic(t.square,xs)**2
                  for t in cert.terms),sp.S(0))
    assert sp.expand(expanded-symbolic(p,xs)) == 0
