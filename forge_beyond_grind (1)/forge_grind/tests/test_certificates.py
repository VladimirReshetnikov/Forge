from dataclasses import replace
from fractions import Fraction as Q
import random
import pytest
import sympy as sp
from forge_lab.poly import (Poly, ConeTerm, ConeCertificate, check_cone,
    bernstein_coefficients, BoxCertificate, check_box)
from forge_lab.nonlinear import cone_search, box_search, square_dictionary
from forge_lab.terms import V, F, NIL, Rule, Step, replay, DEFINITIONS, rigid
from forge_lab.induction import (EqGoal, prove_induction, check_induction,
    standard_bank, synthesize_accumulator, TheoremBank)
from forge_lab.horn import (Atom, Node, HornRule, check_horn, backward, forward,
    branching_problem)
from forge_lab.witness import synthesize_majorant

@pytest.mark.parametrize('seed', range(12))
def test_polynomial_against_sympy(seed):
    rng = random.Random(seed)
    xs = [Poly.var(3,i) for i in range(3)]
    syms = sp.symbols('x y z')
    def random_poly():
        terms = {tuple(rng.randrange(3) for _ in range(3)): Q(rng.randrange(-4,5),rng.randrange(1,5)) for _ in range(8)}
        return Poly.make(3,terms)
    def sym(p):
        return sum(sp.Rational(c.numerator,c.denominator)*sp.prod(s**k for s,k in zip(syms,m)) for m,c in p.terms)
    p,q = random_poly(),random_poly()
    assert sp.expand(sym(p*q) - sym(p)*sym(q)) == 0
    assert sp.expand(sym(p+q) - sym(p)-sym(q)) == 0
    coords = [Q(rng.randrange(-4,5),rng.randrange(1,5)) for _ in range(3)]
    assert sp.Rational(p.eval(coords)) == sym(p).subs(dict(zip(syms,coords)))
    sub = [x+Q(i+1,2) for i,x in enumerate(xs)]
    assert sp.expand(sym(p.substitute(sub))-sym(p).subs(dict(zip(syms,[sym(x) for x in sub])), simultaneous=True)) == 0

@pytest.mark.parametrize('seed', range(12))
def test_planted_cone_search(seed):
    rng = random.Random(seed)
    dic = square_dictionary(2,1)
    terms = tuple(ConeTerm(Q(rng.randrange(1,5),2),rng.choice(dic)) for _ in range(3))
    target = sum((t.weight*t.square**2 for t in terms),Poly.const(2,0))
    known = ConeCertificate(terms)
    assert check_cone(target,(),known)
    found,_ = cone_search(target)
    assert found is not None and check_cone(target,(),found)

@pytest.mark.parametrize('kind', ['quartic','guard_product','guard_cube','unit_interval','schur_like'])
def test_named_nonlinear(kind):
    x,y,z = [Poly.var(3,i) for i in range(3)]
    p,gs = {
        'quartic': (x**4+y**4+z**4-x*x*y*y-y*y*z*z-z*z*x*x,()),
        'guard_product':(x*y,(x,y)),
        'guard_cube':(x**3,(x,)),
        'unit_interval':(x-x*x,(x,1-x)),
        'schur_like':(x**3+y**3-x*y*(x+y),(x,y))
    }[kind]
    cert,_=cone_search(p,gs)
    assert cert is not None and check_cone(p,gs,cert)

def test_dictionary_abstains_on_true_square():
    x,y=Poly.var(2,0),Poly.var(2,1)
    p=(x+y+1)**2
    cert,_=cone_search(p)
    assert cert is None  # restricted binomial dictionary, not all SOS
    direct=ConeCertificate((ConeTerm(Q(1),x+y+1),))
    assert check_cone(p,(),direct)  # checker is more general than search

@pytest.mark.parametrize('bad', ['negative','wrong_target','bad_index','wrong_dimension'])
def test_cone_rejects_mutations(bad):
    x=Poly.var(1,0)
    p=x*x
    cert=ConeCertificate((ConeTerm(Q(1),x),))
    gs=()
    if bad=='negative': cert=ConeCertificate((ConeTerm(Q(-1),x),))
    elif bad=='wrong_target': p=p-Q(1,1000000000000)
    elif bad=='bad_index': cert=ConeCertificate((ConeTerm(Q(1),x,(0,)),))
    else: cert=ConeCertificate((ConeTerm(Q(1),Poly.var(2,0)),))
    assert not check_cone(p,gs,cert)

def test_guard_is_not_an_unconditional_fact():
    x=Poly.var(1,0)
    cert=ConeCertificate((ConeTerm(Q(1),Poly.const(1,1),(0,)),))
    assert check_cone(x,(x,),cert)
    assert not check_cone(x,(),cert)
    assert x.eval((-1,)) < 0  # conditional result alone is insufficient

def test_false_polynomial_abstains():
    x=Poly.var(1,0)
    cert,_=cone_search(x*x-1)
    assert cert is None

@pytest.mark.parametrize('margin',[Q(1,100),Q(1,10),Q(1),Q(3,1000)])
def test_bernstein_positive_margin(margin):
    x=Poly.var(1,0)
    p=(x-Q(1,2))**2+margin
    box=((Q(0),Q(1)),)
    cert,_=box_search(p,box,strict=True)
    assert cert is not None and check_box(p,box,cert,strict=True)

def test_bernstein_exact_bounds():
    x=Poly.var(1,0); p=x*x-x+Q(3,10)
    assert bernstein_coefficients(p,((Q(0),Q(1)),)) == (Q(3,10),Q(-1,5),Q(3,10))
    cert,stats=box_search(p,((Q(0),Q(1)),),strict=True)
    assert cert is not None and stats['leaves']==2
    assert cert.left.lower==cert.right.lower==Q(1,20)

@pytest.mark.parametrize('bad',['gap','bound','missing','strict_zero'])
def test_box_rejects_mutations(bad):
    x=Poly.var(1,0); box=((Q(0),Q(1)),)
    p=x*x-x+Q(3,10)
    cert,_=box_search(p,box,strict=True)
    assert cert is not None
    strict=False
    if bad=='gap': cert=replace(cert,split=Q(2))
    elif bad=='bound': cert=replace(cert,left=BoxCertificate(lower=Q(1)))
    elif bad=='missing': cert=replace(cert,right=None)
    else:
        p=x*x; cert=BoxCertificate(lower=Q(0)); strict=True
    assert not check_box(p,box,cert,strict=strict)

def test_box_nonstrict_boundary_and_false():
    x=Poly.var(1,0); box=((Q(0),Q(1)),)
    c,_=box_search(x*x,box)
    assert c is not None and check_box(x*x,box,c)
    c,_=box_search(x*x-Q(1,2),box,max_depth=4)
    assert c is None

@pytest.mark.parametrize('depth',[0,1,4,8,12])
def test_horn_searches(depth):
    g,fs,rs=branching_problem(depth)
    b,bs=backward(g,fs,rs)
    f,ss=forward(g,fs,rs,rounds=depth)
    assert b is not None and f is not None
    assert check_horn(g,fs,rs,b) and check_horn(g,fs,rs,f)
    assert len(b)==depth+1
    if depth: assert ss['generated']==2**depth

@pytest.mark.parametrize('bad',['cycle','wrong_rule','wrong_goal','missing_fact'])
def test_horn_rejects_mutations(bad):
    g,fs,rs=branching_problem(4)
    trace,_=backward(g,fs,rs); assert trace
    if bad=='cycle': trace=trace[:-1]+(replace(trace[-1],parents=(len(trace)-1,)),)
    elif bad=='wrong_rule': trace=trace[:-1]+(replace(trace[-1],rule='step.g'),)
    elif bad=='wrong_goal': g=Atom('Q',g.arg)
    else: fs=()
    assert not check_horn(g,fs,rs,trace)

def test_horn_missing_guard_not_assumed():
    x=V('x','U'); a=F('a')
    rs=(HornRule('guarded',(Atom('P',x),Atom('G',x)),Atom('Q',x)),)
    fs=(Atom('P',a),); goal=Atom('Q',a)
    trace,_=backward(goal,fs,rs)
    assert trace is None
    fs=fs+(Atom('G',a),)
    trace,_=backward(goal,fs,rs)
    assert trace and check_horn(goal,fs,rs,trace)

def test_horn_abstains_on_unbound_premise():
    x,y=V('x','U'),V('y','U')
    rs=(HornRule('unbound',(Atom('P',y),),Atom('Q',x)),)
    trace,_=backward(Atom('Q',F('a')),(Atom('P',F('a')),),rs)
    assert trace is None

def test_horn_budget_separation():
    goal,fs,rs=branching_problem(16)
    f,st=forward(goal,fs,rs,node_cap=5000)
    b,_=backward(goal,fs,rs)
    assert f is None and st['status']=='node_cap'
    assert b is not None and check_horn(goal,fs,rs,b)

def test_induction_synthesis():
    bank,stats=synthesize_accumulator()
    assert stats['candidate_count']==41
    assert stats['sample_count']==49
    assert not stats['direct_induction_succeeded']
    assert stats['specialization_checked']
    assert len(bank.rules)==3
    prev=TheoremBank()
    for name,(goal,cert) in bank.certificates.items():
        assert prev.add(name,goal,cert)

def test_induction_higher_lemmas():
    bank,_=synthesize_accumulator(); xs,ys=V('xs'),V('ys')
    goals=[('rev_append',EqGoal(F('rev',F('app',xs,ys)),F('app',F('rev',ys),F('rev',xs))),('?ys',)),
           ('rev_invol',EqGoal(F('rev',F('rev',xs)),xs),())]
    for name,goal,gen in goals:
        cert=prove_induction(goal,'?xs',bank.rules,gen)
        assert cert is not None and bank.add(name,goal,cert)

def test_induction_generalization_required():
    bank=standard_bank(); xs,acc=V('xs'),V('acc')
    goal=EqGoal(F('revAcc',xs,acc),F('app',F('rev',xs),acc))
    assert prove_induction(goal,'?xs',bank.rules) is None
    cert=prove_induction(goal,'?xs',bank.rules,('?acc',))
    assert cert and check_induction(goal,cert,bank.rules)
    assert not check_induction(goal,replace(cert,generalized=()),bank.rules)

@pytest.mark.parametrize('bad',['base_ih','bad_generalized','duplicate_generalized','rigid','false_goal','future_rule'])
def test_induction_rejects_mutations(bad):
    bank=standard_bank(); goal,cert=bank.certificates['app_right_nil']
    if bad=='base_ih': cert=replace(cert,nil_left=(Step((),'IH'),))
    elif bad=='bad_generalized': cert=replace(cert,generalized=('?absent',))
    elif bad=='duplicate_generalized': cert=replace(cert,generalized=('?xs','?xs'))
    elif bad=='rigid': goal=EqGoal(F('app',rigid('evil'),NIL),rigid('evil'))
    elif bad=='false_goal': goal=EqGoal(F('app',V('xs'),NIL),NIL)
    else: cert=replace(cert,cons_left=(Step((),'future_lemma'),))
    assert not check_induction(goal,cert)

def test_theorem_bank_rejects_duplicate():
    bank=standard_bank(); goal,cert=bank.certificates['app_right_nil']
    assert not bank.add('app_right_nil',goal,cert)
    assert not bank.add('IH',goal,cert)

def test_witness_is_universally_certified():
    w,certs,stats=synthesize_majorant()
    x=Poly.var(1,0)
    assert w==x*x+1 and certs
    assert check_cone(w-x,(),certs[0]) and check_cone(w+x,(),certs[1])
    assert w.eval((Q(1,2),))==Q(5,4)
