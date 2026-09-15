from dataclasses import replace
from fractions import Fraction as Q
from itertools import product
import random
import pytest
from forge.poly import Poly, solve_linear
from forge.certificates import *
from forge.search import quadratic_sos,cone_search,bernstein_search
from forge.synthesis import *


def vars(n):
    return [Poly.var(n,i) for i in range(n)]

@pytest.mark.parametrize('seed',range(60))
def test_quadratic_generated(seed):
    rng = random.Random(seed)
    n = 1+seed%5
    xs = vars(n)
    p = Poly.const(n,0)
    for j in range(1+seed%7):
        q = Q(rng.randrange(-6,7),rng.randrange(1,5))
        linear = Poly.const(n,q)
        for x in xs:
            linear += Q(rng.randrange(-5,6),rng.randrange(1,5))*x
        p += Q(rng.randrange(1,8),rng.randrange(1,4))*linear**2
    cert = quadratic_sos(p)
    assert cert is not None and check_cone(p,[],[],cert)
    assert not check_cone(p+1,[],[],cert)
    if cert.terms:
        bad = replace(cert,terms=(replace(cert.terms[0],weight=Q(-1)),)+cert.terms[1:])
        assert not check_cone(p,[],[],bad)

@pytest.mark.parametrize('seed',range(20))
def test_nonnegative_not_assumed(seed):
    x,y = vars(2)
    assert quadratic_sos((seed+1)*x*y) is None
    assert quadratic_sos(-(seed+1)*x*x+y*y) is None


def test_quadratic_edges():
    x,y = vars(2)
    for p in [Poly.const(2,0),Poly.const(2,3),(x-y)**2,(x+Q(1,3))**2]:
        cert = quadratic_sos(p)
        assert cert is not None and check_cone(p,[],[],cert)
    assert quadratic_sos(x+1) is None
    assert quadratic_sos(x**4) is None
    assert quadratic_sos(x*x+Q(1,10**30)*x*y) is None


def test_cone_identity_and_scope():
    x,y = vars(2)
    p = x*(1-x)+y*(1-y)
    cert = ConeCertificate((ConeTerm(Q(1),Poly.const(2,1),(1,1,0,0)),
                            ConeTerm(Q(1),Poly.const(2,1),(0,0,1,1))))
    gs = [x,1-x,y,1-y]
    assert check_cone(p,gs,[],cert)
    assert not check_cone(p,[],[],cert)  # assumptions cannot disappear
    assert not check_cone(p,[x,1+x,y,1-y],[],cert)
    assert not check_cone(p,gs,[],replace(cert,terms=cert.terms[:1]))


def test_equality_multipliers():
    x,y = vars(2)
    h = x-y
    p = (x+1)**2 + (x*y-2)*h
    c = ConeCertificate((ConeTerm(Q(1),x+1,()),),(x*y-2,))
    assert check_cone(p,[],[h],c)
    assert not check_cone(p,[],[],c)

@pytest.mark.parametrize('seed',range(16))
def test_cone_lp(seed):
    rng = random.Random(seed)
    x,y = vars(2)
    one = Poly.const(2,1)
    candidates = [ConeTerm(Q(1),q,()) for q in [one,x,y,x*y,x+y,x-y,x*x-y*y]]
    p = sum((rng.randrange(1,6)*c.square**2 for c in candidates),Poly.const(2,0))
    cert = cone_search(p,[],candidates)
    assert cert is not None and check_cone(p,[],[],cert)
    assert not check_cone(p+Q(1,100000000),[],[],cert)


def test_cone_incomplete():
    x,y = vars(2)
    monomial_only = [ConeTerm(Q(1),q,()) for q in [Poly.const(2,1),x,y,x*y]]
    p = (x-y)**2
    assert cone_search(p,[],monomial_only) is None
    richer = monomial_only+[ConeTerm(Q(1),x-y,())]
    assert check_cone(p,[],[],cone_search(p,[],richer))


def test_cone_products():
    x,y = vars(2)
    one = Poly.const(2,1)
    gs = [x,1-x,y,1-y]
    powers = [e for e in product(range(3),repeat=4) if sum(e)<=2]
    candidates = [ConeTerm(Q(1),one,e) for e in powers]
    p = 2*x*(1-x)+3*y*(1-y)+x*y+Q(1,5)
    cert = cone_search(p,gs,candidates)
    assert cert is not None and check_cone(p,gs,[],cert)

@pytest.mark.parametrize('center',[Q(-2,3),Q(-1,3),Q(0),Q(1,3),Q(2,3)])
@pytest.mark.parametrize('eps',[Q(1,4),Q(1,16),Q(1,64)])
def test_bernstein_positive(center,eps):
    x = vars(1)[0]
    p = (x-center)**2+eps
    box = ((Q(-1),Q(1)),)
    cert = bernstein_search(p,box,max_depth=10)
    assert cert is not None and check_bernstein(p,box,cert)
    assert not check_bernstein(p-10,box,cert)


def test_bernstein_motzkin_and_corruption():
    x,y = vars(2)
    p = x**4*y**2+x**2*y**4-3*x*x*y*y+1+Q(1,16)
    small_box = ((Q(-1),Q(1)),)*2
    assert isinstance(bernstein_search(p,small_box),BernsteinLeaf)
    box = ((Q(-2),Q(2)),)*2
    cert = bernstein_search(p,box,max_depth=14)
    assert cert is not None and check_bernstein(p,box,cert)
    assert isinstance(cert,BernsteinSplit)
    assert not check_bernstein(p,box,replace(cert,point=Q(2)))
    assert not check_bernstein(p,box,replace(cert,right=BernsteinLeaf(Q(100))))
    assert not check_bernstein(p,box,replace(cert,right=None))
    assert not check_bernstein(p,box,cert,max_nodes=1)


def test_bernstein_unknown_and_degenerate():
    x = vars(1)[0]
    box = ((Q(-1),Q(1)),)
    assert bernstein_search(-x*x-Q(1,10),box) is None
    assert bernstein_search((x-Q(1,3))**2,box,max_depth=3) is None
    with pytest.raises(ValueError):
        bernstein_coefficients(x,((Q(0),Q(0)),))

@pytest.mark.parametrize('power',range(9))
def test_power_sum_synthesis(power):
    n = vars(1)[0]
    formula = synthesize_recurrence(n**power,Poly.const(1,0),max_degree=power+1)
    assert formula is not None and check_recurrence(n**power,Poly.const(1,0),formula)
    for i in range(12):
        assert formula.evaluate([i]) == sum(Q(k)**power for k in range(i))
    assert not check_recurrence(n**power,Poly.const(1,0),formula+1)

@pytest.mark.parametrize('seed',range(24))
def test_parametric_recurrence(seed):
    rng = random.Random(seed)
    n,a = vars(2)
    step = sum((Q(rng.randrange(-4,5),rng.randrange(1,4))*n**j*a**(j%2)
                for j in range(seed%4+1)),Poly.const(2,0))
    initial = a+seed
    formula = synthesize_recurrence(step,initial,max_degree=6)
    assert formula is not None and check_recurrence(step,initial,formula)
    for k in range(5):
        assert formula.evaluate([k,3]) == initial.evaluate([0,3])+sum(step.evaluate([j,3]) for j in range(k))


def test_recurrence_budget():
    n = vars(1)[0]
    assert synthesize_recurrence(n**5,Poly.const(1,0),max_degree=5) is None
    with pytest.raises(ValueError):
        synthesize_recurrence(n,n)

@pytest.mark.parametrize('seed',range(40))
def test_witness(seed):
    rng = random.Random(seed)
    k,p = 1+seed%4,1+seed%3
    a = [[(1 if i==j else rng.randrange(-3,4) if i<j else 0) for j in range(k)] for i in range(k)]
    w = [[rng.randrange(-5,6) for _ in range(p)] for _ in range(k)]
    d = [rng.randrange(-5,6) for _ in range(k)]
    b = [[sum(a[i][j]*w[j][t] for j in range(k)) for t in range(p)] for i in range(k)]
    c = [sum(a[i][j]*d[j] for j in range(k)) for i in range(k)]
    cert = synthesize_affine_witness(a,b,c,require_integral=True)
    assert cert is not None and check_affine_witness(a,b,c,cert,True)
    bad = replace(cert,offset=(cert.offset[0]+1,)+cert.offset[1:])
    assert not check_affine_witness(a,b,c,bad)


def test_witness_rejections():
    assert synthesize_affine_witness([[2]],[[1]],[0],True) is None
    rational = synthesize_affine_witness([[2]],[[1]],[0])
    assert rational is not None and check_affine_witness([[2]],[[1]],[0],rational)
    assert not check_affine_witness([[2]],[[1]],[0],rational,True)
    assert synthesize_affine_witness([[0]],[[1]],[0]) is None
    assert synthesize_affine_witness([[1],[1]],[[1],[2]],[0,0]) is None
    assert synthesize_affine_witness([[1,1]],[[1]],[0]) is not None


def test_poly_and_matrix_validation():
    with pytest.raises(ValueError):
        Poly(1,(((0,),Q(0)),))
    with pytest.raises(ValueError):
        Poly(1,(((-1,),Q(1)),))
    with pytest.raises(ValueError):
        Poly.var(2,2)
    with pytest.raises(ValueError):
        _ = Poly.var(1,0)+Poly.var(2,0)
    with pytest.raises(ValueError):
        _ = Poly.var(1,0)**-1
    with pytest.raises(ValueError):
        solve_linear([[1,2]],[1],1)
    assert solve_linear([[0]],[1],1) is None
