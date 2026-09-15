"""p1-structural-search/prototype/tests/test_univariate.py, VERBATIM except for
the one import line that had to follow forge.search -> forge.bernstein.
"""
from dataclasses import replace
from fractions import Fraction as Q
import pytest
import sympy as sp
from forge.poly import Poly
from forge.bernstein import bernstein_search
from forge.univariate import *


@pytest.mark.parametrize('seed',range(30))
def test_univariate_zeros(seed):
    x=Poly.var(1,0)
    a,b=Q(-2),Q(2)
    q=(x-Q(seed-15,21))**(1+seed%3)
    if seed%2:
        q*=x*x-2  # irrational even-multiplicity zeros
    p=q*q*(x*x+Q(seed+1,7))*(x+2)*(2-x)
    cert=univariate_search(p,a,b)
    assert cert is not None and check_univariate(p,a,b,cert)
    assert not check_univariate(p+1,a,b,cert)
    assert not check_univariate(p,a,b,replace(cert,chain=cert.chain[:-1]))
    assert not check_univariate(p,a,b,replace(cert,residual=cert.residual+1))


def test_univariate_edge_cases():
    x=Poly.var(1,0)
    for p in [Poly.const(1,0),Poly.const(1,2),x*(1-x),(x-Q(1,3))**2,(x*x-2)**2]:
        a,b=(Q(0),Q(1)) if p==x*(1-x) else (Q(-2),Q(2))
        c=univariate_search(p,a,b)
        assert c is not None and check_univariate(p,a,b,c)
    for p in [x,-x*x,x*x-Q(1,100000000),-(x-Q(1,3))**2]:
        assert univariate_search(p,Q(-1),Q(1)) is None
    p=(x-Q(1,3))**2
    assert bernstein_search(p,((Q(-1),Q(1)),),max_depth=12) is None
    assert univariate_search(p,Q(-1),Q(1)) is not None


@pytest.mark.parametrize('roots',[(-2,-1,0,1,2),(-1,0,1),(0,),(1,),(-2,2),(-3,3)])
def test_sturm_open_endpoints(roots):
    x=Poly.var(1,0)
    p=Poly.const(1,1)
    for r in roots:
        p*=x-r
    chain=sturm_chain(p)
    for a,b in [(Q(-2),Q(2)),(Q(0),Q(1)),(Q(-1),Q(0))]:
        assert open_root_count(chain,a,b)==sum(a<r<b for r in roots)


@pytest.mark.parametrize('seed',range(12))
def test_sturm_independent(seed):
    x=Poly.var(1,0)
    p=x**(3+seed%5)-(seed+1)*x+Q(seed-5,3)
    chain=sturm_chain(p)
    sx=sp.Symbol('x')
    s=sp.Poly.from_dict({e:sp.Rational(c.numerator,c.denominator) for e,c in p.terms},sx)
    a,b=Q(-3),Q(3)
    # SymPy counts roots in the closed interval; remove distinct endpoint roots.
    expected=int(s.count_roots(-3,3))-int(s.eval(-3)==0)-int(s.eval(3)==0)
    assert open_root_count(chain,a,b)==expected
