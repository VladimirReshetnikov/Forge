"""Deterministic mechanism experiments. These are NOT Lean/grind benchmarks.

From the package root: python prototype/run_all.py
Requires NumPy, SciPy and SymPy for search/cross-checks, not certificate replay.
The script overwrites results/ and generated lean/ConeExamples.lean.
"""
from __future__ import annotations
import csv
import json
import platform
import random
import sys
from dataclasses import replace
from fractions import Fraction as Q
from pathlib import Path
from time import perf_counter
import numpy
import scipy
import sympy as sp
from polynomial import Poly, monomials, bernstein_coefficients, expand_bernstein
from cone import Atom,ConeCertificate,check_cone,dictionary,solve_cone,lean_proof
from bernstein import Leaf,Split,certify,check_tree,tree_json
from induction import Kernel,examples,prove_induction,InductionProof,EqualityProof,Equation,F,V,Step
from horn import Rule,Proof,chain_problem,solve as horn_solve,check as horn_check
from replay import replay,induction_json
from quadratic import solve_quadratic

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'results'; CERT=OUT/'certificates'
CERT.mkdir(parents=True,exist_ok=True)
RNG=random.Random(20260914)
assertions=0

def require(condition: bool, message: str) -> None:
    global assertions
    assertions += 1
    if not condition: raise AssertionError(message)


def dump(name,data):
    (OUT/name).write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')


def certdump(name,data):
    require(replay(data),f'Saved certificate must replay: {name}')
    (CERT/(name+'.json')).write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')


def csvdump(name,rows):
    keys=list(dict.fromkeys(k for r in rows for k in r))
    with (OUT/name).open('w',newline='') as f:
        w=csv.DictWriter(f,keys);w.writeheader();w.writerows(rows)


def randpoly(n,degree=3,terms=6):
    ms=monomials(n,degree)
    return sum((Q(RNG.randint(-5,5),RNG.randint(1,7))*RNG.choice(ms) for _ in range(terms)),Poly.const(n,0))


def property_tests():
    for j in range(120):
        n=1+j%3; p,q,r=randpoly(n),randpoly(n),randpoly(n)
        point=tuple(Q(RNG.randint(-3,3),RNG.randint(1,5)) for _ in range(n))
        require((p*(q+r))==p*q+p*r,'Distributivity')
        require((p*q).evaluate(point)==p.evaluate(point)*q.evaluate(point),'Evaluation homomorphism')
        box=tuple((Q(RNG.randint(-3,-1)),Q(RNG.randint(1,3))) for _ in range(n))
        ds,cs=bernstein_coefficients(p,box)
        require(expand_bernstein(n,ds,cs)==p.affine_box(box),'Independent Bernstein round trip')
        syms=sp.symbols('u:'+str(n))
        expr=sum(sp.Rational(c.numerator,c.denominator)*sp.prod(x**k for x,k in zip(syms,m)) for m,c in p.terms)
        got=expr.subs(dict(zip(syms,[sp.Rational(x.numerator,x.denominator) for x in point])))
        require(got==sp.Rational(p.evaluate(point).numerator,p.evaluate(point).denominator),'SymPy evaluation agreement')
    try: Poly.const(1,0.1)
    except TypeError: require(True,'Reject float polynomial input')
    else: require(False,'Float silently accepted')
    return {'random_polynomials':120,'assertions':481}


def cone_tests():
    x,y=Poly.var(2,0),Poly.var(2,1)
    one=Poly.const(2,1)
    cases=[
        ('square_difference',(x-y)**2,(),2),
        ('quartic_sum',(x-y)**2+(x*y-1)**2,(),4),
        ('quartic_gap',x**4+y**4-2*x*x*y*y,(),4),
        ('quadratic_three_terms',(x+y)**2+(x-1)**2+Q(1,3)*y*y,(),2),
        ('product_nonnegative',x*y,(x,y),2),
        ('unit_square_product',x*(1-x)*y*(1-y),(x,1-x,y,1-y),4),
        ('hypothesis_square',x*(x-y)**2,(x,),3),
        ('weighted_box',Q(2,3)*(x-y)**2+x*(1-x),(x,1-x),2),
        ('box_quartic',x*(1-x)*(y-1)**2,(x,1-x),4),
        ('rational_square',(x-Q(1,2))**2,(),2),
    ]
    # This degree-4 product needs products of four individual constraints.
    rows=[];generated=[];good=[]
    for name,p,hs,deg in cases:
        for mode in ('diagonal','pair_squares','products'):
            order=4 if name=='unit_square_product' else 2
            atoms=dictionary(2,deg,hs,pair_squares=mode!='diagonal',product_order=order if mode=='products' else 0)
            t=perf_counter();c,s=solve_cone(p,hs,atoms);elapsed=perf_counter()-t
            rows.append({'case':name,'mode':mode,'solved':c is not None,'total_seconds':elapsed,**s})
            if c is not None:
                require(check_cone(p,hs,c),'Cone exact replay')
            if mode=='products':
                good.append(c is not None)
                if c:
                    certdump('cone_'+name,{'kind':'cone','target':p.to_json(),'hypotheses':[h.to_json() for h in hs],'certificate':c.to_json()})
                    generated.append(lean_proof('forge_'+name,p,hs,c,('x','y')))
    # A positive square outside a small dictionary; failure is not falsity.
    p=(x+3*y)**2
    c,s=solve_cone(p,(),dictionary(2,2,()))
    require(c is None,'Restricted pair dictionary should miss unequal rank-one square')
    rows.append({'case':'unequal_square','mode':'default_dictionary','solved':False,**s})
    c,s=solve_cone(p,(),dictionary(2,2,(),extra_squares=(x+3*y,)))
    require(c is not None,'Explicit basis enrichment should solve unequal square')
    rows.append({'case':'unequal_square','mode':'enriched_dictionary','solved':True,**s})
    certdump('cone_enriched_square',{'kind':'cone','target':p.to_json(),'hypotheses':[],'certificate':c.to_json()})
    # Constructed family: not an independently sampled theorem distribution.
    atoms=dictionary(2,4,(x,y),product_order=2)
    for i in range(30):
        selected=RNG.sample(list(atoms),3)
        weights=[Q(RNG.randint(1,4),RNG.randint(1,4)) for _ in selected]
        p=sum((w*a.expand((x,y)) for w,a in zip(weights,selected)),Poly.const(2,0))
        c,s=solve_cone(p,(x,y),atoms)
        require(c is not None and check_cone(p,(x,y),c),'Constructed cone family')
    p=(x-y)**2
    goodcert=ConeCertificate(((Q(1),Atom(x-y)),))
    negatives=[
       not check_cone(p+Q(1,10**20),(),goodcert),
       not check_cone(p,(),ConeCertificate(((Q(-1),Atom(x-y)),))),
       not check_cone(p,(),ConeCertificate(((Q(1),Atom(x-y,(7,))),))),
       not check_cone(p,(),ConeCertificate(((1.0,Atom(x-y)),))),
       not check_cone(p,(),ConeCertificate(((Q(1),Atom(Poly.var(1,0))),))),
    ]
    for ok in negatives: require(ok,'Reject corrupt cone certificate')
    c,s=solve_cone(-one,(),dictionary(2,2,()))
    require(c is None,'Negative constant not certified')
    (ROOT/'lean'/'ConeExamples.lean').write_text('-- GENERATED, NOT COMPILED in the supplied experiment.\nimport Mathlib\n\n'+'\n'.join(generated))
    csvdump('cone.csv',rows)
    return {'curated_cases':len(cases),'full_solved':sum(good),
            'diagonal_solved':sum(r['solved'] for r in rows if r['mode']=='diagonal'),
            'pair_squares_solved':sum(r['solved'] for r in rows if r['mode']=='pair_squares'),
            'constructed_cases':30,'constructed_solved':30,'corruption_rejections':len(negatives),
            'basis_enrichment_control':'unknown -> checked_python'}


def quadratic_tests():
    rows=[];extra_lean=[]
    curated=[]
    x,y=Poly.var(2,0),Poly.var(2,1)
    curated=[('unequal_square',(x+3*y)**2),('rational_center',(x-Q(1,2))**2),
             ('mixed_affine',Q(2,3)*(x+2*y-3)**2+Q(5,7)*(2*x-y+1)**2),
             ('zero',Poly.const(2,0))]
    for name,p in curated:
        t=perf_counter();c,s=solve_quadratic(p);elapsed=perf_counter()-t
        require(c is not None and check_cone(p,(),c),'Exact quadratic PSD decomposition')
        rows.append({'case':name,'solved':c is not None,'total_seconds':elapsed,**s})
        certdump('quadratic_'+name,{'kind':'cone','target':p.to_json(),'hypotheses':[],'certificate':c.to_json()})
        extra_lean.append(lean_proof('forge_quadratic_'+name,p,(),c,('x','y')))
    for i in range(60):
        n=1+i%5
        p=Poly.const(n,0)
        for _ in range(1+i%6):
            q=randpoly(n,degree=1,terms=n+1)
            p+=Q(RNG.randint(1,5),RNG.randint(1,5))*q*q
        c,s=solve_quadratic(p)
        require(c is not None and check_cone(p,(),c),'Generated rational PSD quadratic')
    for p in (-1+x*x,x*y,x*x-y*y,(x+y)**2-Q(1,10**20)):
        c,s=solve_quadratic(p)
        require(c is None,'Do not certify indefinite quadratic')
    (ROOT/'lean'/'QuadraticExamples.lean').write_text('-- GENERATED, NOT COMPILED in this environment.\nimport Mathlib\n\n'+'\n'.join(extra_lean))
    csvdump('quadratic.csv',rows)
    return {'curated_cases':4,'curated_solved':4,'constructed_cases':60,'constructed_solved':60,
            'negative_controls_rejected':4,'search':'exact rational symmetric pivoting; no numeric oracle'}


def bernstein_tests():
    x,y=Poly.var(2,0),Poly.var(2,1)
    box=((Q(0),Q(1)),)*2
    cases=[
      ('one_plus_square',1+x*x,True),
      ('square_gap',(x-y)**2+Q(1,100),True),
      ('sum_centered',(x-Q(1,3))**2+(y-Q(2,3))**2+Q(1,20),True),
      ('product_centered',(x*y-Q(1,3))**2+Q(1,25),True),
      ('quartic_gap',(x*x-y)**2+Q(1,20),True),
      ('box_positive',1-x*(1-x)*y*(1-y),True),
      ('unit_product',x*(1-x)*y*(1-y),False),
      ('dyadic_zero',(x-Q(1,2))**2,False),
      ('nondyadic_zero',(x-Q(1,3))**2,False),
      ('negative_constant',Poly.const(2,-1),False),
    ]
    rows=[];accepted=[]
    for name,p,strict in cases:
        for mode,depth in [('no_subdivision',0),('adaptive',12)]:
            t=perf_counter();c,s=certify(p,box,max_depth=depth,strict=strict);elapsed=perf_counter()-t
            rows.append({'case':name,'mode':mode,'solved':c is not None,'strict':strict,'total_seconds':elapsed,**s})
            if c:
                require(check_tree(p,box,c,strict=strict),'Bernstein replay')
                if mode=='adaptive':
                    certdump('bernstein_'+name,{'kind':'bernstein','target':p.to_json(),'box':[[str(a),str(b)] for a,b in box],
                         'strict':strict,'certificate':tree_json(c)})
                    accepted.append(name)
    require('nondyadic_zero' not in accepted,'Nondyadic root should expose subdivision limitation')
    require('negative_constant' not in accepted,'Negative polynomial cannot be certified')
    p=1+x*x;ds,cs=bernstein_coefficients(p,box);good=Leaf(ds,cs)
    corruption=[
       not check_tree(p,box,Leaf(ds,(cs[0]+1,)+cs[1:])),
       not check_tree(p,box,Leaf(ds,tuple(float(v) for v in cs))),
       not check_tree(p,box,Split(0,Q(0),good,good)),
       not check_tree(p,box,Split(5,Q(1,2),good,good)),
       not check_tree(p,box,Split(0,Q(1,2),good,good)), # leaf polynomials belong to unsplit box
       not check_tree(p,box,Leaf((100000,2),cs)),
       not check_tree(Poly.const(2,0),box,Leaf((0,0),(Q(0),)),strict=True),
    ]
    for ok in corruption: require(ok,'Reject corrupt Bernstein certificate')
    csvdump('bernstein.csv',rows)
    return {'cases':len(cases),'expected_true_cases':9,
            'no_subdivision_solved':sum(r['solved'] for r in rows if r['mode']=='no_subdivision'),
            'adaptive_solved':len(accepted),'corruption_rejections':len(corruption),
            'nondyadic_boundary_case':'unknown at depth 12','negative_case':'unknown, not certified'}


def induction_tests():
    rows=[];saved=[];forged_rejected=0
    for gen in (False,True):
        k=Kernel()
        for e,subject in examples():
            t=perf_counter();p=prove_induction(k,e,subject,generalization=gen);elapsed=perf_counter()-t
            rows.append({'case':e.name,'generalization':gen,'solved':p is not None,'total_seconds':elapsed,
                         'generalized_parameters':','.join(p.generalize) if p else '',
                         'rewrite_steps':sum(len(s) for s in (p.base.left,p.base.right,p.step.left,p.step.right)) if p else None})
            if p:
                require(k.check(e,p),'Induction exact replay')
                if gen:
                    saved.append(induction_json(e,p))
                    bad=replace(p,generalize=(subject,))
                    require(not k.check(e,bad),'Reject generalizing induction subject');forged_rejected+=1
                    if p.step.left:
                        s=p.step.left[0]
                        corrupt=replace(p,step=replace(p.step,left=(replace(s,rule='unregistered_rule'),)+p.step.left[1:]))
                        require(not k.check(e,corrupt),'Reject invented proof rule');forged_rejected+=1
                    if p.generalize:
                        require(not k.check(e,replace(p,generalize=())),'Reject IH used at changed parameter without generalization')
                        forged_rejected+=1
                k.install(e,p)
        # False theorem, including legitimate induction target, must remain unproved.
        e=Equation('false_reverse',F('rev',V('xs','L')),F('nil'))
        require(prove_induction(k,e,'xs',generalization=gen) is None,'Reject false induction conjecture')
    certdump('induction_sequence',{'kind':'induction_sequence','theorems':saved})
    csvdump('induction.csv',rows)
    return {'theorems':8,'without_generalization':sum(r['solved'] for r in rows if not r['generalization']),
            'with_generalization':sum(r['solved'] for r in rows if r['generalization']),
            'corruption_rejections':forged_rejected,'subject_selection':'supplied in this prototype'}


def horn_tests():
    rows=[]
    for length in (8,16,32):
        for decoys in (0,100,1000,10000):
            args=chain_problem(length,decoys)
            for demand in (False,True):
                t=perf_counter();p,s=horn_solve(*args,demand=demand,budget=100);elapsed=perf_counter()-t
                rows.append({'chain_length':length,'decoys':decoys,'demand':demand,'solved':p is not None,'total_seconds':elapsed,**s})
                require((p is not None)==(demand or decoys==0),'Ground Horn synthetic budget behavior')
                if p:
                    require(horn_check(*args,p),'Horn replay')
                    if length==16 and decoys==10000 and demand:
                        facts,rules,target=args
                        certdump('horn_demand_chain',{'kind':'horn','facts':sorted(facts),'target':target,
                                  'rules':[{'name':r.name,'premises':list(r.premises),'conclusion':r.conclusion} for r in rules],
                                  'certificate':list(p.applications)})
    for j in range(250):
        names=[f'f{i}' for i in range(12)]
        facts=frozenset(RNG.sample(names,RNG.randrange(5)))
        rs=tuple(Rule(f'r{i}',tuple(RNG.choices(names,k=RNG.randrange(4))),RNG.choice(names)) for i in range(35))
        target=RNG.choice(names)
        known=set(facts)
        while True:
            before=len(known)
            for r in rs:
                if set(r.premises)<=known: known.add(r.conclusion)
            if len(known)==before: break
        for demand in (False,True):
            p,_=horn_solve(facts,rs,target,demand=demand)
            require((p is not None)==(target in known),'Horn agreement with naive least-fixed-point closure')
            if p: require(horn_check(facts,rs,target,p),'Random Horn proof replay')
    args=chain_problem(2,0)
    bads=[Proof(((9,'p1'),)),Proof(((0,'p9'),)),Proof(((1,'p2'),))]
    for p in bads: require(not horn_check(*args,p),'Reject malformed Horn proof')
    csvdump('horn.csv',rows)
    return {'synthetic_problems':12,'firing_budget':100,
            'unsliced_solved':sum(r['solved'] for r in rows if not r['demand']),
            'sliced_solved':sum(r['solved'] for r in rows if r['demand']),
            'random_graphs':250,'random_mode_comparisons':500,'corruption_rejections':len(bads)}


def main():
    t=perf_counter()
    summary={}
    for label,fn in [('polynomial_properties',property_tests),('cone',cone_tests),('quadratic',quadratic_tests),('bernstein',bernstein_tests),('induction',induction_tests),('horn',horn_tests)]:
        t0=perf_counter();summary[label]=fn();summary[label]['suite_seconds']=perf_counter()-t0
        print(label,summary[label],flush=True)
    summary['assertions_passed']=assertions
    summary['total_seconds']=perf_counter()-t
    summary['environment']={'python':sys.version,'platform':platform.platform(),'machine':platform.machine(),
                            'numpy':numpy.__version__,'scipy':scipy.__version__,'sympy':sp.__version__,'seed':20260914,
                            'lean_status':'NOT_RUN: no Lean executable available in this environment'}
    summary['interpretation']='Mechanism experiments and negative controls; not a Lean/grind comparison. Timings are single runs, not calibrated benchmarks.'
    dump('summary.json',summary)
    print('ASSERTIONS PASSED',assertions)

if __name__=='__main__': main()
