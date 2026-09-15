from __future__ import annotations
from copy import deepcopy
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json
import random
import sympy as sp
import pytest
from forge_delta import checker as ck
from forge_delta.search import solve, Span, encode, decode, machine, Limits, conserved_target_only
from forge_delta.cases import machine_cases, logical_cases, SEED
from forge_delta.kripke import (find_countermodel,verify_countermodel,truth_bits,tree_frames,
                               atom,imp,conj,disj,neg,bot,sequent,formula,parse_problem)

MACHINES=machine_cases()
LOGICAL=logical_cases()

@pytest.mark.parametrize('case',MACHINES,ids=lambda c:c['name'])
def test_machine_cases(case):
    r=solve(case['problem'],case['limits'])
    assert r['status']==case['expected']
    if r['status']=='proved':assert ck.verify_positive(case['problem'],r['certificate'])
    if r['status']=='refuted':assert ck.verify_negative(case['problem'],r['certificate'])
    if r['status']=='unknown':assert 'certificate' not in r

@pytest.mark.parametrize('case',LOGICAL,ids=lambda c:c['name'])
def test_kripke_cases(case):
    r=find_countermodel(case['problem'])
    assert r['status']==case['expected']
    if r['status']=='ipc_countermodel':
        assert verify_countermodel(case['problem'],r['certificate'])
        assert r['certificate']['worlds']==case['min_worlds']

@pytest.fixture(scope='module')
def delayed():
    c=MACHINES[0];return c['problem'],solve(c['problem'])['certificate']

@pytest.mark.parametrize('mutation',range(14))
def test_reject_corrupt_positive(delayed,mutation):
    p,c=map(deepcopy,delayed)
    if mutation==0:c['basis'][0][0][0][1][0]+=1
    if mutation==1:c['edge_coordinates']=[]
    if mutation==2:c['edge_coordinates'][0]=c['edge_coordinates'][0][:-1]
    if mutation==3:c['goal_coordinates'][0][0]=[]
    if mutation==4:c['goal_coordinates'][0][0][0]=[99,1]
    if mutation==5:c['edge_coordinates'][0][0][0]['coordinates'][0]=[99,1]
    if mutation==6:c['edge_coordinates'][0][0][0]['input_exponent']=[1]
    if mutation==7:c['basis'][0][0][0][1]=[2,2]
    if mutation==8:c['basis'][0][0][0][1]=[True,1]
    if mutation==9:c['basis'][0][0][0][1]=[1.0,1]
    if mutation==10:c['goals']=p['goals']  # cannot replace target from certificate
    if mutation==11:p['initial']['state'][0]=[1,1]
    if mutation==12:p['edges'][0]['update'][3].append([[0]*5,[1,1]])
    if mutation==13:c['basis'][0][0]=list(reversed(c['basis'][0][0]))
    assert not ck.verify_positive(p,c)

@pytest.mark.parametrize('mutation',range(10))
def test_reject_corrupt_trace(mutation):
    p=deepcopy(MACHINES[1]['problem']);c=solve(p)['certificate']
    if mutation==0:c['steps']=c['steps'][:-1]
    if mutation==1:c['steps'][0]['edge']=1
    if mutation==2:c['steps'][0]['input']=[]
    if mutation==3:c['steps'][0]['input'][0]=[1,0]
    if mutation==4:c['goal_index']=1
    if mutation==5:c['goal']=[]
    if mutation==6:p=deepcopy(MACHINES[0]['problem'])  # valid trace on different machine cannot donate evidence
    if mutation==7:c['steps'][0]['input'][0]=[True,1]
    if mutation==8:c['steps'][0]['input'][0]=[0,2]
    if mutation==9:p['semantics']='bounded-integer-input'
    assert not ck.verify_negative(p,c)

@pytest.mark.parametrize('mutation',range(12))
def test_reject_corrupt_kripke(mutation):
    case=next(c for c in LOGICAL if c['name']=='excluded_middle')
    p=deepcopy(case['problem']);c=find_countermodel(p)['certificate']
    if mutation==0:c['relation'][0][0]=False
    if mutation==1:c['relation'][1][0]=True
    if mutation==2:c['relation'][0][1]=False
    if mutation==3:c['valuation']['P']=[True,False]
    if mutation==4:c['valuation']['P']=[False,False] # LEM now true
    if mutation==5:c['root']=1
    if mutation==6:c['valuation']['Q']=[False,False]
    if mutation==7:c['relation'][0][0]=1
    if mutation==8:c['worlds']=True
    if mutation==9:c['goal']=p['goal']
    if mutation==10:p['logic']='Lean-Classical'
    if mutation==11:p['context']=[atom('P')]
    assert not verify_countermodel(p,c)


def test_nontransitive_relation_rejected():
    p=sequent(atom('P'))
    c={'kind':'finite_kripke_countermodel','worlds':4,'root':0,
       'relation':[[True,True,True,True],[False,True,True,False],
                   [False,False,True,True],[False,False,False,True]],
       'valuation':{'P':[False]*4}}
    assert not verify_countermodel(p,c)


def test_unknown_and_cutoffs():
    p=MACHINES[0]['problem']
    for lim in [Limits(max_basis_per_node=1),Limits(max_work=0)]:
        r=solve(p,lim);assert r['status']=='unknown' and 'certificate' not in r
    p=next(c['problem'] for c in MACHINES if c['name']=='seven_sample_trap')
    r=solve(p,Limits(max_grid_points=1));assert r['status']=='unknown'
    p=sequent(disj(atom('P'),neg(atom('P'))))
    assert find_countermodel(p,max_worlds=1)['status']=='unknown'
    assert find_countermodel(p,max_models=0)['status']=='unknown'


def test_samples_are_not_proofs():
    p=next(c['problem'] for c in MACHINES if c['name']=='seven_sample_trap')
    n,u,q,node,initial,edges,goals=ck.parse_problem(p)
    for v in range(7):
        state=[ck.evaluate(f,initial+[Q(v)]) for f in edges[0]['update']]
        assert ck.evaluate(goals[0][0],state)==0
    r=solve(p)
    assert r['certificate']['steps'][0]['input']==[[7,1]]


def test_scope_binding():
    p=next(c['problem'] for c in MACHINES if c['name']=='alternating_control')
    r=solve(p);assert r['status']=='proved'
    c=deepcopy(r['certificate']);c['edge_coordinates'].reverse()
    # Both edge matrices happen to be equal here, so a swap would not be corrupt.
    # Change a source control node in the externally supplied machine instead.
    other=deepcopy(p);other['edges'][0]['src']=1
    assert not ck.verify_positive(other,c)
    badtrace={'kind':'execution_counterexample','steps':[{'edge':1,'input':[[0,1]]}],'goal_index':0}
    assert not ck.verify_negative(p,badtrace)


def test_ablation_is_not_complete():
    assert not conserved_target_only(MACHINES[0]['problem'])
    assert solve(MACHINES[0]['problem'])['status']=='proved'
    assert conserved_target_only(next(c['problem'] for c in MACHINES if c['name']=='square_of_sum'))

@pytest.mark.parametrize('seed',range(10))
def test_differential_sparse_substitution(seed):
    rng=random.Random(SEED+seed);x,y,u=sp.symbols('x0 x1 u0')
    for _ in range(20):
        p=sum(rng.randint(-3,3)*x**rng.randrange(4)*y**rng.randrange(4) for _ in range(6))
        f=x+y+u;g=2*x-y*u+1
        raw=encode(p,(x,y));images=[ck.polynomial(encode(z,(x,y,u)),3) for z in [f,g]]
        result=ck.substitute(ck.polynomial(raw,2),images,3)
        expected=ck.polynomial(encode(sp.expand(p.xreplace({x:f,y:g})),(x,y,u)),3)
        assert result==expected
        vals=[Q(rng.randint(-2,2),rng.randint(1,3)) for _ in range(3)]
        exact=sp.expand(p.xreplace({x:f,y:g})).xreplace(dict(zip((x,y,u),vals,strict=True)))
        assert ck.evaluate(result,vals)==Q(int(exact.p),int(exact.q))

@pytest.mark.parametrize('seed',range(10))
def test_differential_kripke_truth(seed):
    rng=random.Random(SEED+seed);p,q=map(atom,['P','Q'])
    fs=[p,q,bot()]
    for _ in range(12):
        a,b=rng.choices(fs,k=2);fs.append(rng.choice([imp,conj,disj])(a,b))
    for n in range(1,4):
        for succ in tree_frames(n):
            upward=[b for b in range(1<<n) if all(not(b>>w&1) or b&s==s for w,s in enumerate(succ))]
            for pa,qa in product(upward,repeat=2):
                val={'P':pa,'Q':qa};full=(1<<n)-1
                # Deliberately direct recursive reference, independent of bit arithmetic.
                def force(w,f):
                    if f[0]=='var':return bool(val[f[1]]&(1<<w))
                    if f[0]=='bot':return False
                    if f[0]=='and':return force(w,f[1]) and force(w,f[2])
                    if f[0]=='or':return force(w,f[1]) or force(w,f[2])
                    return all(not(succ[w]&(1<<v)) or not force(v,f[1]) or force(v,f[2]) for v in range(n))
                for f in fs:
                    ft=formula(f);bits=truth_bits(ft,val,succ,full,{})
                    for w in range(n):assert bool(bits&(1<<w))==force(w,ft)
                    # Exercise the *actual* checker at the root too.
                    prob=sequent(f);_,_,names=parse_problem(prob)
                    cert={'kind':'finite_kripke_countermodel','worlds':n,'root':0,
                          'relation':[[bool(s>>j&1) for j in range(n)] for s in succ],
                          'valuation':{name:[bool(val[name]>>j&1) for j in range(n)] for name in names}}
                    assert verify_countermodel(prob,cert)==(not force(0,ft))


def test_exact_span_coordinates():
    x,y=sp.symbols('x y');s=Span((x,y))
    for p in [x+y,x-y,x*x+y*y,2*x+2*y,x*y]:s.insert(p,{})
    assert len(s.basis)==4
    goal=3*x+7*y+5*x*y-2*(x*x+y*y)
    c=s.coordinates(goal)
    assert sp.expand(sum(a*b for a,b in zip(c,s.basis,strict=True))-goal)==0

@pytest.mark.parametrize('text',[
    '{"x":1,"x":2}', '{"x":1.0}', '{"x":NaN}', '{"x":Infinity}'
])
def test_decoder_rejects_ambiguous_json(tmp_path,text):
    f=tmp_path/'bad.json';f.write_text(text)
    with pytest.raises((ck.Invalid,ValueError)):ck.load_json(f)


def test_partial_order_not_only_tree():
    # The checker accepts a diamond partial order, although the bounded
    # proposer enumerates only trees.
    p=sequent(atom('P'))
    c={'kind':'finite_kripke_countermodel','worlds':4,'root':0,
       'relation':[[True,True,True,True],[False,True,False,True],
                   [False,False,True,True],[False,False,False,True]],
       'valuation':{'P':[False,False,False,True]}}
    assert verify_countermodel(p,c)


def test_stored_corpus_replays_without_site_packages():
    import subprocess,sys
    root=Path(__file__).resolve().parents[1]
    p=subprocess.run([sys.executable,'-S',str(root/'replay.py')],cwd=root,
                     capture_output=True,text=True,timeout=20,check=True)
    out=json.loads(p.stdout)
    assert out['site_packages_loaded'] is False
    assert out['replayed']=={'proved':37,'refuted':28,'ipc_countermodel':8,'unknown_no_claim':9}


def test_certificate_representation_cap_is_unknown():
    # Valid state-affine problem, but M(u)=u^96 exceeds the checker's
    # per-payload-exponent encoding bound of 64. No unaccepted proof escapes.
    x,u=sp.symbols('x0 u0')
    p=machine(1,1,[0],[(0,0,'scale',[u**32*x])],[[x**3]])
    r=solve(p)
    assert r['status']=='unknown' and 'certificate' not in r
    assert 'replay' in r['reason']
