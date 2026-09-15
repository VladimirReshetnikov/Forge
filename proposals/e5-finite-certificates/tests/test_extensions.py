"""Regression, schema, differential, and adversarial controls.

Parametrization counts tests, not solved Lean goals or mathematical theorems.
"""
from __future__ import annotations
import copy, json, random, subprocess, sys
from pathlib import Path
from fractions import Fraction as Q
import pytest
import sympy as s
from prototype import checkers as c
from prototype.search import (linear_problem, linear_search, ideal_problem, ideal_search,
                              sum_problem, sum_search, enc, dec)

ROOT=Path(__file__).resolve().parents[1]
BUNDLES=sorted((ROOT/'results'/'certificates').glob('*.json'))
NEGATIVES=sorted((ROOT/'results'/'counterexamples').glob('*.json'))

@pytest.mark.parametrize('path',BUNDLES,ids=lambda p:p.stem)
def test_stored_certificate(path):
    b=c.load_bundle(path)
    assert c.verify(b['problem'],b['certificate'])

@pytest.mark.parametrize('path',NEGATIVES,ids=lambda p:p.stem)
def test_stored_counterexample(path):
    b=c.load_bundle(path)
    assert c.counterexample(b['problem'],b['counterexample'])
    bad=copy.deepcopy(b['counterexample']);bad['value']=[0,1]
    assert not c.counterexample(b['problem'],bad)

@pytest.mark.parametrize('path',BUNDLES,ids=lambda p:p.stem)
def test_target_binding_and_coverage(path):
    b=c.load_bundle(path);p=b['problem'];cert=b['certificate'];bad=copy.deepcopy(p)
    if p['kind']=='linear':
        # Shift initial state in a coordinate actually observed by the target.
        j=next(j for j,z in enumerate(p['target']) if z[0])
        a=Q(*bad['initial'][j])+1;bad['initial'][j]=[a.numerator,a.denominator]
        assert not c.verify(bad,cert)
        altered=copy.deepcopy(cert);altered['action_weights']=altered['action_weights'][:-1]
        assert not c.verify(p,altered)
    elif p['kind']=='ideal':
        xs=s.symbols(f'x0:{p["dimension"]}')
        bad['target']=enc(dec(p['target'],xs)+1,xs)
        assert not c.verify(bad,cert)
        altered=copy.deepcopy(cert);altered['action_weights']=[]
        assert not c.verify(p,altered)
    else:
        k=s.Symbol('k');bad['weight']=enc(dec(p['weight'],(k,))+1,(k,))
        assert not c.verify(bad,cert)
        altered=copy.deepcopy(cert);altered['p1']=[]
        assert not c.verify(p,altered)

@pytest.mark.parametrize('raw',[[1.0,1],[True,1],[1,0],[2,2],[0,2],[1,-1],'1/2',[]])
def test_bad_rationals(raw):
    with pytest.raises(c.Invalid):c.rat(raw)

@pytest.mark.parametrize('raw',[
    [[[0],[1,1]],[[0],[2,1]]], # duplicate
    [[[1],[1,1]],[[0],[2,1]]], # out of order
    [[[-1],[1,1]]], [[[129],[1,1]]], [[[0],[0,1]]],
    [[[0,1],[1,1]]], [[[False],[1,1]]]
])
def test_bad_polynomials(raw):
    with pytest.raises(c.Invalid):c.poly(raw,1)

def test_duplicate_json_keys(tmp_path):
    p=tmp_path/'bad.json';p.write_text('{"problem":1,"problem":2}')
    with pytest.raises(c.Invalid):c.load_bundle(p)

def test_float_json(tmp_path):
    p=tmp_path/'bad.json';p.write_text('{"x":0.0}')
    with pytest.raises(c.Invalid):c.load_bundle(p)

def test_no_site_packages():
    run=subprocess.run([sys.executable,'-S',str(ROOT/'prototype/checkers.py'),
        str(ROOT/'results/certificates'),str(ROOT/'results/counterexamples')],capture_output=True,text=True,check=False)
    assert run.returncode==0,run.stdout+run.stderr
    assert '"site_packages_enabled": false' in run.stdout

def test_zero_target():
    p=linear_problem([[[2,1],[1,2]]],[1,3],[0,0]);r=linear_search(p)
    assert r['certificate']['basis']==[]
    assert c.verify(p,r['certificate'])

def test_word_direction():
    A=s.zeros(3);B=s.zeros(3);A[1,2]=1;B[0,1]=1
    p=linear_problem([A,B],[0,0,1],[1,0,0]);r=linear_search(p)
    assert r['word']==[0,1] and c.counterexample(p,r)
    r['word']=[1,0]
    assert not c.counterexample(p,r)

def test_nonlinear_budget_does_not_refute():
    x,y,z,w=s.symbols('x y z w');a,b=s.symbols('a b')
    p=ideal_problem((x,y,z,w),[(y*y,x,w*w,z)],(a,b),[a,b,a,-b],x-z)
    assert ideal_search(p,max_extensions=0)['status']=='unknown'
    r=ideal_search(p)
    assert r['stats']['generators']==2 and c.verify(p,r['certificate'])

def test_singular_leading_coefficient_requires_extra_seed():
    # Two distinct sequences meet this recurrence and the n=0 seed.
    # The certificate proves a recurrence; it deliberately makes no uniqueness claim.
    r=sum_search(sum_problem(1,1));n=s.Symbol('n');cert=r['certificate']
    p0,p1=dec(cert['p0'],(n,)),dec(cert['p1'],(n,))
    assert p1.subs(n,0)==0
    def actual(N):return sum(K*s.binomial(N,K) for K in range(N+1))
    def wrong(N):return 2*actual(N)
    assert actual(0)==wrong(0) and actual(1)!=wrong(1)
    for N in range(12):
        assert p1.subs(n,N)*wrong(N+1)+p0.subs(n,N)*wrong(N)==0

def test_pole_free_endpoint():
    r=sum_search(sum_problem(2));n,k=s.symbols('n k')
    polynomial=dec(r['certificate']['r'],(n,k))
    for N in range(15):
        # A(n,0) is defined as zero, NOT choose(n,Nat.sub(0,1)).
        low=polynomial.subs({n:N,k:0})*0**2
        high=polynomial.subs({n:N,k:N+2})*s.binomial(N,N+1)**2
        assert low==high==0
    # Generic rational Gosper form is undefined at k=n+1.
    denom=(n+1-k)**2
    assert denom.subs(k,n+1)==0

def test_sparse_arithmetic_differential():
    rng=random.Random(93873);xs=s.symbols('x y');u=s.Symbol('u')
    for _ in range(60):
        p=sum(rng.randint(-3,3)*xs[0]**rng.randrange(4)*xs[1]**rng.randrange(4) for __ in range(5))
        q=sum(rng.randint(-3,3)*xs[0]**rng.randrange(3)*xs[1]**rng.randrange(3) for __ in range(4))
        pp,qq=c.poly(enc(p,xs),2),c.poly(enc(q,xs),2)
        assert c.add(pp,qq)==c.poly(enc(p+q,xs),2)
        assert c.mul(pp,qq)==c.poly(enc(p*q,xs),2)
        values=[c.poly(enc(u+1,(u,)),1),c.poly(enc(u*u,(u,)),1)]
        composed=s.expand(p.subs({xs[0]:u+1,xs[1]:u*u},simultaneous=True))
        assert c.compose(pp,values,1)==c.poly(enc(composed,(u,)),1)
