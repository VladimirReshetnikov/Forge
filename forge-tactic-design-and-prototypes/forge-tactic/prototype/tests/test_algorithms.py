from fractions import Fraction as Q
from dataclasses import replace
import random
import pytest
import sympy as sp
from poly import Poly, bernstein_coefficients
import cone, bernstein, invariant, horn

@pytest.mark.parametrize('seed', range(30))
def test_poly_against_sympy(seed):
    rng=random.Random(seed); xs=sp.symbols('x:2')
    def make():
        return Poly.make(2,{(i,j):Q(rng.randint(-8,8),rng.randint(1,5))
                            for i in range(3) for j in range(3-i)})
    a,b=make(),make()
    def expr(p):
        return sum(sp.Rational(c.numerator,c.denominator)*xs[0]**e[0]*xs[1]**e[1]
                   for e,c in p.terms)
    assert sp.expand(expr(a*b)-expr(a)*expr(b))==0
    assert sp.expand(expr(a+b)-expr(a)-expr(b))==0
    pt=(Q(rng.randint(-3,3),2),Q(rng.randint(-3,3),3))
    actual=expr(a).subs(dict(zip(xs,[sp.Rational(v.numerator,v.denominator) for v in pt])))
    assert a.evaluate(pt)==Q(int(actual.p),int(actual.q))


def test_polynomial_domain_validation():
    with pytest.raises(TypeError): Poly.const(1,0.1)
    with pytest.raises(TypeError): Poly.make(1,{(0,):0.0})
    with pytest.raises(ValueError): Poly(1, (((-1,),Q(1)),))
    with pytest.raises(ValueError): Poly.var(1,2)
    with pytest.raises(ValueError): Poly.var(1,0)+Poly.var(2,0)
    with pytest.raises(ValueError): Poly.var(1,0)**-1

@pytest.mark.parametrize('a,b', [(a,b) for a in range(1,6) for b in range(1,6)])
def test_product_certificate(a,b):
    x,y=Poly.var(2,0),Poly.var(2,1)
    target=x*y-a*b; ge=(x-a,y-b)
    cert=cone.search(target,ge,degree=2)
    assert cert is not None and cone.replay(target,ge,(),cert)
    assert cone.search(target,ge,degree=2,product_depth=1,binomials=False) is None


def test_cone_mutations_and_incompleteness():
    x,y=Poly.var(2,0),Poly.var(2,1); target=(x-y)**2
    cert=cone.search(target,degree=2)
    assert cert and cone.replay(target,(),(),cert)
    c,a=cert.positive[0]
    assert not cone.replay(target,(),(),replace(cert,positive=((-c,a),)))
    assert not cone.replay(target,(),(),replace(cert,positive=((c,replace(a,factors=(0,))),)))
    assert not cone.replay(target+1,(),(),cert)
    assert not cone.replay(target,(),(),replace(cert,positive=((float(c),a),)))
    # True but outside the finite degree-two binomial cone used here.
    assert cone.search((x-2*y)**2,degree=2) is None
    assert cone.search(Poly.const(2,-1),degree=2) is None


def test_mixed_certificate():
    x,y,u=[Poly.var(3,j) for j in range(3)]
    target=Poly.const(3,-1); ge=(u-Q(1,3),); eq=(x+y-1,u-x*y)
    cert=cone.search(target,ge,eq,degree=2)
    assert cert and cone.replay(target,ge,eq,cert)
    assert not cone.replay(target,(),eq,cert)
    i,m=cert.equalities[0]
    assert not cone.replay(target,ge,eq,replace(cert,equalities=((i,m+1),)+cert.equalities[1:]))
    assert not cone.replay(target,ge,tuple(reversed(eq)),cert)

@pytest.mark.parametrize('k,epsilon', [(k,Q(1,d)) for k in range(1,7) for d in (10,100,1000)])
def test_bernstein_positive(k,epsilon):
    x=Poly.var(1,0); p=(x-Q(k,7))**2+epsilon; box=((Q(0),Q(1)),)
    r=bernstein.search(p,box,strict=True)
    assert r.status=='PROVED'
    assert bernstein.replay(p,box,r.tree,strict=True)


def test_bernstein_refute_unknown_and_mutations():
    x=Poly.var(1,0); box=((Q(0),Q(1)),)
    r=bernstein.search((x-Q(1,3))**2+Q(1,100),box)
    assert isinstance(r.tree,bernstein.Split)
    assert not bernstein.replay((x-Q(1,3))**2+1,box,r.tree)
    assert not bernstein.replay((x-Q(1,3))**2+Q(1,100),box,replace(r.tree,cut=Q(0)))
    assert not bernstein.replay((x-Q(1,3))**2+Q(1,100),box,replace(r.tree,right=None))
    assert not bernstein.replay(x,box,bernstein.Leaf((Q(1),Q(1))))
    assert not bernstein.replay(x,box,bernstein.Leaf((Q(0),Q(1))),strict=True)
    assert bernstein.replay(x,box,bernstein.Leaf((Q(0),Q(1))))
    bad=bernstein.search(x-Q(1,2),box)
    assert bad.status=='REFUTED' and bernstein.check_witness(x-Q(1,2),box,bad.witness)
    assert not bernstein.check_witness(x,box,(Q(-1),))
    unresolved=bernstein.search((x*x-2)**2,((Q(1),Q(2)),),max_depth=8)
    assert unresolved.status=='UNKNOWN'
    square_cert=cone.ConeCertificate(((Q(1),cone.Atom(x*x-2)),),())
    assert cone.replay((x*x-2)**2,(),(),square_cert)
    assert bernstein.search(x,box,strict=True).status=='REFUTED'

@pytest.mark.parametrize('seed', range(15))
def test_bernstein_conversion_independent_expansion(seed):
    rng=random.Random(seed)
    p=Poly.make(2,{(i,j):Q(rng.randint(-5,5)) for i in range(3) for j in range(3)})
    box=((Q(-2),Q(3)),(Q(1),Q(4)))
    cs=bernstein_coefficients(p,box)
    # Shift so the entire supplied representation is nonnegative, then replay
    # by basis expansion (different algorithm from coefficient conversion).
    shift=-min(cs)+1
    pp=p+shift; shifted=tuple(c+shift for c in cs)
    assert bernstein.replay(pp,box,bernstein.Leaf(shifted))

@pytest.mark.parametrize('w,c', [(w,c) for w in range(-5,6) for c in range(-5,6)])
def test_invariant_synthesis(w,c):
    cert=invariant.search(Q(1),Q(w),Q(c))
    assert cert and invariant.replay(Q(1),Q(w),Q(c),cert)
    rng=random.Random(w*100+c)
    for _ in range(4):
        xs=[rng.randint(-8,8) for _ in range(rng.randrange(15))]; a=rng.randint(-10,10)
        assert invariant.run(xs,a,1,w,c)==a+w*sum(xs)+c*len(xs)
    assert not invariant.replay(Q(1),Q(w),Q(c),replace(cert,A=Q(2)))

@pytest.mark.parametrize('r', (-2,-1,0,2,3))
def test_invariant_template_unknown(r):
    assert invariant.search(Q(r),Q(2),Q(1)) is None

@pytest.mark.parametrize('seed', range(40))
def test_horn_slice_equivalence(seed):
    rng=random.Random(seed); names=[f'p{i}' for i in range(15)]
    rules=tuple(horn.Rule(rng.choice(names),tuple(rng.sample(names,rng.randrange(4))))
                for _ in range(40))
    facts=tuple(rng.sample(names,4)); goal=rng.choice(names)
    prog=horn.Program(rules)
    a,b=prog.solve(facts,goal),prog.solve(facts,goal,demand=True)
    assert a.proved==b.proved
    if a.proved:
        assert horn.replay(rules,facts,goal,a.proof)
        assert horn.replay(rules,facts,goal,b.proof)
        assert horn.replay(rules,facts,goal,horn.minimize(rules,facts,goal,a.proof))


def test_horn_cycles_and_mutations():
    rules=(horn.Rule('a',('b',)),horn.Rule('b',('a',)))
    p=horn.Program(rules)
    assert not p.solve((),'a').proved
    assert not p.solve((),'a',demand=True).proved
    assert not horn.replay(rules,(),'a',horn.Proof((('a',0),('b',1))))
    assert not horn.replay(rules,('b',),'a',horn.Proof((('a',1),)))
    assert not horn.replay(rules,('b',),'a',horn.Proof((('a',-1),)))


def test_monomial_enumeration_scaling():
    from poly import monomials
    from math import comb
    ms=monomials(10,3)
    assert len(ms)==comb(13,3)
    assert len(set(ms))==len(ms)
    assert all(m.degree<=3 for m in ms)
