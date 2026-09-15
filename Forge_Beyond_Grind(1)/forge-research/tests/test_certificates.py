from copy import deepcopy
from fractions import Fraction as Q
from random import Random
from math import gcd
import pytest
import sympy as s
from forge_cert.poly import *
from forge_cert.polynomial_search import cone_search, quadratic_search, bernstein_search, sparse
from forge_cert.induction import (F,V,N,x,a,prove,verify,synthesize_lemmas,mutation_positions,
                                  sampled_counterexample)
from forge_cert.cdclt import solve,verify_unsat,verify_sat,exhaustive_oracle,pigeonhole
from forge_cert.witness import synthesize,verify as verify_witness,instantiate

sx,sy,sz=s.symbols('x y z')

@pytest.mark.parametrize('p,xs,gs,hs,d',[
    (sx*sx+sy*sy-2*sx*sy,(sx,sy),[],[],2),
    (sx**4+sy**4-2*sx*sx*sy*sy,(sx,sy),[],[],4),
    (sx*sx+sy*sy+sz*sz-sx*sy-sy*sz-sz*sx,(sx,sy,sz),[],[],2),
    (sx-sx*sx,(sx,),[sx,1-sx],[],2),
    (sx*sx+sy*sy-s.Rational(1,2),(sx,sy),[],[sx+sy-1],2),
    (sx-sx*sy,(sx,sy),[sx,sy,1-sx,1-sy],[],2),
    (s.Integer(0),(sx,),[],[],2),
])
def test_cone(p,xs,gs,hs,d):
    c,_=cone_search(p,xs,gs,hs,d)
    assert c is not None
    assert verify_cone(sparse(p,xs),[sparse(g,xs) for g in gs],[sparse(h,xs) for h in hs],c,len(xs))

@pytest.mark.parametrize('p',[sx*sx-sy*sy,-s.Integer(1),sx**4*sy*sy+sx*sx*sy**4+1-3*sx*sx*sy*sy])
def test_cone_unknown(p):
    c,_=cone_search(p,(sx,sy),degree=6)
    assert c is None

@pytest.mark.parametrize('p',[(2*sx-sy)**2,(3*sx+sy-2)**2+sy**2+s.Rational(1,3),s.Integer(0)])
def test_exact_quadratic(p):
    c=quadratic_search(p,(sx,sy));assert c is not None
    assert verify_cone(sparse(p,(sx,sy)),[],[],c,2)

@pytest.mark.parametrize('p',[sx*sx-sy*sy,-s.Integer(1),sx])
def test_quadratic_rejects(p):
    assert quadratic_search(p,(sx,sy)) is None

def test_cone_tampering():
    p=(sx-sy)**2;c,_=cone_search(p,(sx,sy),degree=2)
    t=deepcopy(c);t['nonnegative'][0]['coefficient']='-1'
    assert not verify_cone(sparse(p,(sx,sy)),[],[],t,2)
    t=deepcopy(c);t['nonnegative'][0]['square'][0][1]='999'
    assert not verify_cone(sparse(p,(sx,sy)),[],[],t,2)
    assert not verify_cone(sparse(p-1,(sx,sy)),[],[],c,2)
    t=deepcopy(c);t['nonnegative'][0]['factors']=[0]
    assert not verify_cone(sparse(p,(sx,sy)),[],[],t,2)

@pytest.mark.parametrize('p,xs,box',[
    ((sx-s.Rational(1,3))**2+s.Rational(1,10000),(sx,),[(0,1)]),
    ((sx-s.Rational(1,3))**2+(sy-s.Rational(2,3))**2+s.Rational(1,100),(sx,sy),[(0,1),(0,1)]),
    (s.Integer(0),(sx,),[(0,1)]),
    (sx+2,(sx,),[(-1,1)])])
def test_bernstein(p,xs,box):
    c,_=bernstein_search(p,xs,box,max_depth=12);assert c is not None
    assert verify_bernstein(sparse(p,xs),[(Q(a),Q(b)) for a,b in box],c,len(xs))

def test_bernstein_unknown_and_tampering():
    p=(sx-s.Rational(1,3))**2
    assert bernstein_search(p,(sx,),[(0,1)],max_depth=8)[0] is None
    c,_=bernstein_search(p+s.Rational(1,100),(sx,),[(0,1)])
    t=deepcopy(c);t['cut']='2'
    assert not verify_bernstein(sparse(p+s.Rational(1,100),(sx,)),[(Q(0),Q(1))],t,1)
    t=deepcopy(c);t['right']=t['left']
    assert not verify_bernstein(sparse(p+s.Rational(1,100),(sx,)),[(Q(0),Q(1))],t,1)

def test_structural_and_ablations():
    lemmas,records=synthesize_lemmas()
    assert [r['status'] for r in records]==['proved','proved','rejected_by_counterexample','rejected_by_counterexample','proved']
    assert mutation_positions()=={'qrev':{1}}
    lhs=F('qrev',x,a);rhs=F('app',F('rev',x),a)
    assert prove(lhs,rhs,(),generalize=False) is None
    assert prove(lhs,rhs,(),generalize=True) is None
    assert prove(lhs,rhs,lemmas,generalize=False) is None
    c=prove(lhs,rhs,lemmas,generalize=True)
    assert verify(lhs,rhs,c,lemmas)
    t=deepcopy(c);t['generalized']=[]
    assert not verify(lhs,rhs,t,lemmas)
    t=deepcopy(c);t['branches']=t['branches'][:1]
    assert not verify(lhs,rhs,t,lemmas)
    lhs=F('rev',F('rev',x));rhs=x
    c=prove(lhs,rhs,lemmas);assert verify(lhs,rhs,c,lemmas)

@pytest.mark.parametrize('seed',range(12))
def test_random_cdclt(seed):
    rng=Random(seed)
    for _ in range(25):
        nodes=3
        atoms={v:(rng.randrange(nodes),rng.randrange(nodes),rng.randrange(-3,4)) for v in range(1,6)}
        cnf=[[rng.choice((-1,1))*rng.randrange(1,6) for _ in range(rng.randrange(1,4))]
             for _ in range(rng.randrange(1,12))]
        r=solve(cnf,atoms,nodes);expected=exhaustive_oracle(cnf,atoms,nodes)
        assert (r['status']=='sat')==expected
        assert (verify_sat if expected else verify_unsat)(cnf,atoms,nodes,r)

@pytest.mark.parametrize('p',range(2,7))
def test_pigeonholes(p):
    cnf=pigeonhole(p,p-1);r=solve(cnf)
    assert verify_unsat(cnf,{},1,r)

def test_cdclt_tampering_and_edges():
    atoms={1:(0,1,0),2:(1,0,-1)};cnf=[[1],[2]];r=solve(cnf,atoms,2)
    assert verify_unsat(cnf,atoms,2,r)
    t=deepcopy(r)
    for p in t['proof']:
        if p['kind']=='theory':p['cycle']=[1];break
    assert not verify_unsat(cnf,atoms,2,t)
    t=deepcopy(r);t['proof'][-1]['pivot']=999
    assert not verify_unsat(cnf,atoms,2,t)
    t=deepcopy(r);t['root']=0
    assert not verify_unsat(cnf,atoms,2,t)
    for cnf in ([],[[]],[[1,-1]]):
        r=solve(cnf)
        assert (verify_sat if r['status']=='sat' else verify_unsat)(cnf,{},1,r)

@pytest.mark.parametrize('m',range(1,21))
def test_witness(m):
    for aa in range(-3,6):
        for bb in range(0,6):
            c=synthesize(aa,bb,m)
            if bb%gcd(aa,m):assert c is None;continue
            assert verify_witness(aa,bb,m,c)
            for n in (-100,-1,0,1,17,10**20+7):
                k=instantiate(n,m,c)
                assert n<=k<n+m and (aa*k-bb)%m==0
    c=synthesize(1,1,m);t=deepcopy(c);t['offsets'][0]=m
    assert not verify_witness(1,1,m,t)

def test_induction_bundle_dependency_check():
    from forge_cert.induction import verify_bundle
    _,rs=synthesize_lemmas()
    assert verify_bundle(rs)
    t=deepcopy(rs);t[4]['name']=t[0]['name']
    assert not verify_bundle(t)

def test_induction_bundle_rejects_forward_dependency():
    from forge_cert.induction import verify_bundle
    _,rs=synthesize_lemmas()
    # rev_app requires associativity, which must not be available early.
    assert not verify_bundle([rs[4],rs[0],rs[1]])

def test_induction_bundle_requires_target_even_if_status_is_tampered():
    from forge_cert.induction import verify_bundle
    _,rs=synthesize_lemmas()
    assert verify_bundle(rs,required=['rev_app'])
    rs[-1]['status']='unknown'
    assert not verify_bundle(rs,required=['rev_app'])
