from dataclasses import replace
from fractions import Fraction as Q
from itertools import product
import random
import pytest
import sympy as sp
from forge.polynomial import Poly,monomials
from forge.checkers import (ConeTerm,ConeCertificate,check_cone,check_invariant,
                            BernsteinLeaf,check_bernstein)
from forge.nonlinear import discover
from forge.bernstein import discover as bernstein,leaves
from forge.invariants import additive_invariant
from forge.demand import (Term,Atom,Rule,ProofNode,HornCertificate,check_horn,
                         demand_prove,forward_prove)

@pytest.mark.parametrize('seed',range(12))
def test_polynomial_against_sympy(seed):
    rng=random.Random(seed); xs=sp.symbols('x y z')
    def make():
        return Poly.make(3,[(rng.choice(monomials(3,3)),Q(rng.randint(-5,5),rng.randint(1,7))) for _ in range(10)])
    def convert(p):
        return sum(sp.Rational(c.numerator,c.denominator)*sp.prod(x**e for x,e in zip(xs,m)) for m,c in p.terms)
    p,q=make(),make()
    assert sp.expand(convert(p*q)-convert(p)*convert(q))==0
    assert sp.expand(convert(p+q)-convert(p)-convert(q))==0
    assert Poly.from_json(p.to_json())==p
    vals=[Q(rng.randint(-3,3),2) for _ in xs]
    assert p.eval(vals)==Q(convert(p).subs(dict(zip(xs,vals))))


def test_polynomial_rejects_malformed():
    with pytest.raises(ValueError): Poly(1,(((1,),Q(0)),))
    with pytest.raises(ValueError): Poly(1,(((-1,),Q(1)),))
    with pytest.raises(ValueError): Poly(1,(((1,),Q(1)),((1,),Q(1))))
    with pytest.raises(ValueError): _=Poly.variable(1,0)**-1
    with pytest.raises(ValueError): _=Poly.variable(1,0)+Poly.variable(2,0)

@pytest.mark.parametrize('offset',[1,2,3,5,7])
def test_automatic_binomial_squares(offset):
    x=Poly.variable(1,0); p=(x-offset)**2
    r=discover(p,degree=2)
    assert r.status=='proved' and check_cone(p,(),(),r.certificate)


def test_cauchy_schwarz_without_manual_square_hint():
    x,y,u,v=[Poly.variable(4,i) for i in range(4)]
    p=(x*x+y*y)*(u*u+v*v)-(x*u+y*v)**2
    r=discover(p,degree=4)
    assert r.status=='proved' and check_cone(p,(),(),r.certificate)

@pytest.mark.parametrize('degree',range(1,6))
def test_positive_constraint_products(degree):
    x=Poly.variable(1,0); gs=(x,1-x); p=x**degree*(1-x)**degree
    # Limit degree to <= 6 to keep dictionary compact in this unit suite.
    if degree>3:
        r=discover(p,gs,degree=6); assert r.status=='unknown'
    else:
        r=discover(p,gs,degree=2*degree)
        assert r.status=='proved' and check_cone(p,gs,(),r.certificate)


def test_equality_ideal():
    x,y=Poly.variable(2,0),Poly.variable(2,1)
    p=y*y-2*x+1; es=(y-x,)
    r=discover(p,(),es,degree=2)
    assert r.status=='proved' and check_cone(p,(),es,r.certificate)


def test_cone_tampering():
    x=Poly.variable(1,0); one=Poly.constant(1,1)
    c=ConeCertificate((ConeTerm(Q(1),one,(0,)),))
    assert check_cone(x,(x,),(),c)
    assert not check_cone(x,(),(),c)  # missing side condition
    assert not check_cone(x,(x,),(),replace(c,terms=(replace(c.terms[0],weight=Q(-1)),)))
    assert not check_cone(x,(x,),(),replace(c,terms=(replace(c.terms[0],factors=(-1,)),)))
    assert not check_cone(x+1,(x,),(),c)  # wrong target / context substitution
    assert not check_cone(x,(x,),(),replace(c,ideal=(one,)))
    # The floating tolerance exploit must be rejected exactly.
    assert not check_cone(x,(x,),(),replace(c,terms=(replace(c.terms[0],weight=Q(10**20+1,10**20)),)))

@pytest.mark.parametrize('seed',range(10))
def test_false_nonnegative_claims_are_not_certified(seed):
    x=Poly.variable(1,0); p=(x-seed)**2-Q(1,1000)
    assert p.eval([seed])<0
    assert discover(p,degree=2).status=='unknown'


def test_bernstein_subdivision_and_cover_tampering():
    x=Poly.variable(1,0); p=x*x-x+Q(1,3); box=((Q(0),Q(1)),)
    assert bernstein(p,box,depth=0) is None
    cert=bernstein(p,box,depth=4)
    assert cert is not None and leaves(cert)==2 and check_bernstein(p,box,cert)
    assert not check_bernstein(p,box,replace(cert,cut=Q(1,3)))
    assert not check_bernstein(p,box,replace(cert,right=cert.left))
    leaf=cert.left
    cs=list(leaf.coefficients); k,c=cs[0]; cs[0]=(k,c+Q(1,10**18))
    assert not check_bernstein(p,leaf.box,replace(leaf,coefficients=tuple(cs)))
    assert not check_bernstein(p,((Q(0),Q(2)),),cert)


def test_true_unknown_bernstein():
    x=Poly.variable(1,0); p=(x-Q(1,3))**2
    assert bernstein(p,((Q(0),Q(1)),),depth=6) is None
    assert discover(p,degree=2).status=='proved'

@pytest.mark.parametrize('power',range(9))
def test_additive_invariant(power):
    x=Poly.variable(1,0); p=(x+1)**power
    c=additive_invariant(p)
    assert c is not None and check_invariant(c)
    assert not check_invariant(replace(c,invariant=c.invariant+1))
    ts=list(c.transition); ts[1]+=1
    assert not check_invariant(replace(c,transition=tuple(ts)))


def test_interpolation_does_not_count_as_proof():
    x=Poly.variable(1,0)
    # This increment vanishes at all sampled n=0,1,2, but not universally.
    p=x*(x-1)*(x-2)
    assert additive_invariant(p,degree=2) is None


def horn_family(depth):
    x,a=Term('?x'),Term('a'); P=lambda t:Atom('P',(t,))
    rules=(Rule('grow_g',P(Term('g',(x,))),(P(x),)),
           Rule('grow_f',P(Term('f',(x,))),(P(x),)))
    t=a
    for _ in range(depth): t=Term('f',(t,))
    return (P(a),),rules,P(t)

@pytest.mark.parametrize('depth',[1,2,4,6,8,10])
def test_demand_forward_agree(depth):
    facts,rules,goal=horn_family(depth)
    d=demand_prove(facts,rules,goal); f=forward_prove(facts,rules,goal)
    assert d.status==f.status=='proved'
    assert d.terms_or_facts==depth+1
    assert f.terms_or_facts==2**(depth+1)-1
    assert check_horn(facts,rules,goal,d.certificate)
    assert check_horn(facts,rules,goal,f.certificate)


def test_horn_cycles_and_and_branches():
    a=Term('a'); A=lambda p:Atom(p,(a,))
    rules=(Rule('cycle1',A('P'),(A('Q'),)),Rule('cycle2',A('Q'),(A('P'),)),
           Rule('join',A('R'),(A('P'),A('Q'))))
    assert demand_prove((),rules,A('R')).status=='unknown'
    assert demand_prove((A('P'),),rules,A('R')).status=='proved'
    assert forward_prove((A('P'),),rules,A('R')).status=='proved'


def test_horn_certificate_tampering():
    facts,rules,goal=horn_family(3); c=demand_prove(facts,rules,goal).certificate
    bad=list(c.nodes); bad[-1]=replace(bad[-1],premises=(len(bad)-1,))
    assert not check_horn(facts,rules,goal,replace(c,nodes=tuple(bad)))  # circular
    bad=list(c.nodes); bad[-1]=replace(bad[-1],rule=0)
    assert not check_horn(facts,rules,goal,replace(c,nodes=tuple(bad)))
    assert not check_horn((),rules,goal,c)
    assert not check_horn(facts,rules,facts[0],c)
    assert not check_horn(facts,rules,goal,replace(c,root=-1))

@pytest.mark.parametrize('seed',range(15))
def test_ground_horn_differential(seed):
    rng=random.Random(seed); a=Term('a'); ats=[Atom(f'P{i}',(a,)) for i in range(12)]
    facts=tuple(rng.sample(ats,3)); rules=[]
    for j in range(22):
        rules.append(Rule(f'r{j}',rng.choice(ats),tuple(rng.sample(ats,rng.randint(1,3)))))
    for goal in ats:
        d=demand_prove(facts,tuple(rules),goal); f=forward_prove(facts,tuple(rules),goal)
        assert d.status==f.status
        if d.certificate: assert check_horn(facts,tuple(rules),goal,d.certificate)


def test_budgets_return_unknown():
    facts,rules,goal=horn_family(8)
    assert demand_prove(facts,rules,goal,max_depth=4).status=='unknown'
    assert demand_prove(facts,rules,goal,max_demands=3).status=='unknown'
    assert forward_prove(facts,rules,goal,max_facts=3,max_depth=8).status=='unknown'
    x=Poly.variable(1,0)
    assert discover(x*x,degree=1).status=='unknown'
    assert discover(x*x,degree=4,max_generators=1).status=='unknown'


def test_shifted_square_with_positive_rational_margin():
    x=Poly.variable(1,0)
    p=(x-Q(2,3))**2+Q(1,97)
    r=discover(p,degree=2)
    assert r.certificate and check_cone(p,(),(),r.certificate)
