"""Reproduce the three extension experiments; standard library only.

Default output is ../reproduced-results, never the distributed evidence folder.
The fixtures are deliberately small algorithm tests, not tactic benchmarks.
"""
from __future__ import annotations
import argparse
from copy import deepcopy
from dataclasses import replace
from itertools import product
import json
from pathlib import Path
import platform
import random
import shutil
import sys
from time import perf_counter

from exact import Q,const,var,add,scale,mul,monomials,vector,rref,encode
from invariant_space import Problem,discover,conserved_dimension,affine_dual_relations,coupled_example
import continuation_synth as synth
import cyclic_rank as cyclic
from replay import check_space,check_rank,check_church_index,check_ideal,check_orbit_counterexample
import ideal_closure

SEED=20260915


def affine_cases(count=72):
    rng=random.Random(SEED)
    for i in range(count):
        n=2 if i%2==0 else 3
        d=1 if i%3==0 else 2
        xs=[var(n,j) for j in range(n)]
        fs=[]
        for a in range(1+i%3):
            # Every third instance preserves a coordinate. Other instances are
            # unconstrained small integer-affine systems, often with no relation.
            f=[]
            for j in range(n):
                if i%3==0 and j==n-1:
                    f.append(xs[j])
                else:
                    f.append(add(const(n,rng.randint(-2,2)),
                              *[scale(rng.randint(-2,2),x) for x in xs]))
            fs.append(f)
        init=[const(0,rng.randint(-2,2)) for _ in range(n)]
        yield Problem(f'affine_{i:03}',n,d,0,init,fs,{})


def nonlinear_cases(count=40):
    rng=random.Random(SEED+1)
    x,y,z=[var(3,i) for i in range(3)]; xx=mul(x,x); t=var(1,0); tt=mul(t,t)
    for i in range(count):
        c,b=rng.randint(-3,3),rng.randint(-3,3)
        e1=add(y,scale(-c,xx)); e2=add(z,scale(-b,xx))
        fs=[]
        for _ in range(1+i%3):
            a=rng.choice([-3,-2,-1,1,2,3])
            m=[rng.randint(-3,3) for _ in range(4)]
            fs.append([scale(a,x),add(scale(c*a*a,xx),scale(m[0],e1),scale(m[1],e2)),
                       add(scale(b*a*a,xx),scale(m[2],e1),scale(m[3],e2))])
        yield Problem(f'nonlinear_{i:03}',3,2,1,[t,scale(c,tt),scale(b,tt)],fs,
                      add(e1,scale(2,e2)))


def changed_numerator(pair,delta=1):
    q=Q(*pair)+delta
    return [q.numerator,q.denominator]


def mutations(space_entry,rank_entry,church_entry):
    """Named, targeted corruptions; each is checked against the original input."""
    out=[]
    def run(name,kind,entry,mutate):
        e=deepcopy(entry);mutate(e)
        check={'space':check_space,'rank':check_rank,'church':check_church_index}[kind]
        ok,msg=check(e['problem'],e['certificate'])
        out.append(dict(name=name,accepted=ok,reason=msg))
        if ok: raise AssertionError(f'corruption accepted: {name}')
    run('space_wrong_action','space',space_entry,lambda e:e['certificate']['actions'][0][0].__setitem__(0,[99,1]))
    run('space_missing_transition','space',space_entry,lambda e:e['certificate']['actions'].pop())
    run('space_wrong_target','space',space_entry,lambda e:e['certificate']['target_coefficients'].__setitem__(0,[17,1]))
    run('space_changed_initialization','space',space_entry,lambda e:e['problem']['init'][0].append([[0],[1,1]]))
    run('space_float_coefficient','space',space_entry,lambda e:e['certificate']['basis'][0][0].__setitem__(1,0.5))
    run('space_duplicate_monomial','space',space_entry,lambda e:e['certificate']['basis'][0].append(e['certificate']['basis'][0][0]))
    run('space_noncanonical_rational','space',space_entry,lambda e:e['certificate']['basis'][0][0].__setitem__(1,[2,2]))
    run('space_wrong_arity','space',space_entry,lambda e:e['problem']['transitions'][0].pop())
    run('rank_missing_call','rank',rank_entry,lambda e:e['certificate']['edges'].pop())
    run('rank_erased_phase','rank',rank_entry,lambda e:e['certificate']['layers'][0]['P'].__setitem__(0,0))
    run('rank_bad_pivot','rank',rank_entry,lambda e:e['certificate']['edges'][0].__setitem__('pivot',2))
    run('rank_removed_domain_certificate','rank',rank_entry,lambda e:e['certificate']['edges'][0].__setitem__('target_nonnegative',[]))
    run('rank_negative_multiplier','rank',rank_entry,lambda e:e['certificate']['edges'][0]['decrease'].__setitem__(0,[-1,1]))
    run('rank_changed_update','rank',rank_entry,lambda e:e['problem']['edges'][1]['updates'][0].__setitem__(0,0))
    run('rank_boolean_integer','rank',rank_entry,lambda e:e['certificate']['layers'][0]['P'].__setitem__(0,True))
    def step(e): return e['certificate']['term']['fn']['step']['body']['body']['body']
    run('church_wrong_predecessor','church',church_entry,lambda e:step(e)['positive']['arg'].__setitem__('offset',1))
    run('church_wrong_zero_result','church',church_entry,lambda e:step(e).__setitem__('zero',{'op':'var','id':'default'}))
    run('church_wrong_negative_result','church',church_entry,lambda e:step(e).__setitem__('negative',{'op':'var','id':'head'}))
    run('church_wrong_carrier','church',church_entry,lambda e:e['certificate']['term']['fn'].__setitem__('carrier',{'tag':'A','args':[]}))
    run('church_binder_capture','church',church_entry,lambda e:e['certificate']['term']['fn']['step'].__setitem__('id','default'))
    run('church_outer_index_escape','church',church_entry,lambda e:step(e)['positive']['arg'].__setitem__('arg',{'op':'var','id':'outerIndex'}))
    run('church_unrestricted_semantics','church',church_entry,lambda e:e['problem'].__setitem__('semantics','all-arbitrary-Church-values'))
    run('church_wrong_final_input','church',church_entry,lambda e:e['certificate']['term']['fn'].__setitem__('input',{'op':'var','id':'otherInput'}))
    return out


def main(out:Path):
    out.mkdir(parents=True,exist_ok=True)
    started=perf_counter();entries=[];results={}
    p=coupled_example();c,m=discover(p)
    assert check_space(p.encoded(),c)[0]
    space={'problem':p.encoded(),'certificate':c};entries.append(space)
    degree1=discover(replace(p,degree=1))[1]
    m['conserved_dimension']=conserved_dimension(p);m['degree_one']=degree1
    results['coupled_example']=m
    aff=[]
    for p in affine_cases():
        c,m=discover(p)
        from replay import poly
        basis=[vector(poly(q,p.n),monomials(p.n,p.degree)) for q in c['basis']]
        want=affine_dual_relations(p)
        assert rref(basis,len(monomials(p.n,p.degree)))[0]==want,p.name
        assert check_space(p.encoded(),c)[0],p.name
        entries.append(dict(problem=p.encoded(),certificate=c))
        aff.append(dict(name=p.name,degree=p.degree,n=p.n,dimension=m['fixed_point_dimension']))
    results['affine_differential']=dict(count=len(aff),all_agree=True,cases=aff,
        nontrivial_invariant_cases=sum(c['dimension']>0 for c in aff))
    nls=[]
    for p in nonlinear_cases():
        c,m=discover(p); assert check_space(p.encoded(),c)[0],p.name
        assert m['target_in_span']
        entries.append(dict(problem=p.encoded(),certificate=c));nls.append(dict(name=p.name,dimension=m['fixed_point_dimension']))
    results['nonlinear_family']=dict(count=len(nls),all_targets_derived=True,cases=nls)
    x=var(1,0)
    limited=Problem('degree_growth_limitation',1,1,0,[const(0,0)],[[mul(x,x)]],x)
    _,lm=discover(limited)
    assert lm['fixed_point_dimension']==0 and not lm['target_in_span']
    results['degree_growth_negative_control']=lm
    ideal_rows=[];ideal_positive=None;orbit_negative=None
    for p in ideal_closure.fixtures():
        c,m=ideal_closure.complete(p)
        check=check_ideal if m['status']=='found' else check_orbit_counterexample
        assert check(p.encoded(),c)[0],p.name
        entry=dict(problem=p.encoded(),certificate=c);entries.append(entry)
        if ideal_positive is None and p.name=='ideal_power_curve_02':ideal_positive=entry
        if p.name=='orbit_counterexample_noncommuting':orbit_negative=entry
        ideal_rows.append(dict(name=p.name,**m))
    limited_ideal,lmi=ideal_closure.complete(coupled_example(),max_generators=1)
    assert limited_ideal is None and lmi['status']=='unknown'
    results['ideal_completion']=dict(cases=ideal_rows,budget_control=lmi)
    rank_rows=[];rank_entry=None
    for p in cyclic.fixtures():
        c,m=cyclic.synthesize(p);sct=cyclic.size_change(p)
        if c:
            assert check_rank(p,c)[0]
            entry=dict(problem=p,certificate=c);entries.append(entry)
            if rank_entry is None:rank_entry=entry
            m['layers']=c['layers']
        rank_rows.append(dict(name=p['name'],ranking=m,size_change=sct))
    assert sum(x['ranking']['status']=='found' for x in rank_rows)==4
    assert [x['size_change']['criterion_met'] for x in rank_rows]==[True]*4+[False]*2
    results['cyclic_graphs']=rank_rows
    rows=[];last=None
    for noise in [0,4,8,12]:
        t0=perf_counter();flat,fm=synth.synthesize(noise,False);fm['seconds']=perf_counter()-t0
        t0=perf_counter();term,lm=synth.synthesize(noise,True);lm['seconds']=perf_counter()-t0
        assert flat==term
        ce=synth.certificate(term,noise);assert check_church_index(ce['problem'],ce['certificate'])[0]
        rows.append(dict(noise=noise,flat=fm,local=lm));last=(term,noise,ce)
    term,noise,church_entry=last;entries.append(church_entry)
    checks=0
    for alphabet in [(0,1),('red','green')]:
        default=('outside-alphabet',)
        for length in range(7):
            for xs in product(alphabet,repeat=length):
                for index in list(range(-3,length+4))+[-2**80,2**80]:
                    assert synth.execute(term,default,list(xs),index,noise)==synth.reference_index(default,xs,index)
                    checks+=1
    cut,cutm=synth.synthesize(12,False,cap=256);assert cut is None and cutm['status']=='truncated'
    # Correlated holes: independent projections are not a correct join.
    allowed={(0,1),(1,0)}
    projection_product=set(product({a for a,b in allowed},{b for a,b in allowed}))
    assert (0,0) in projection_product and (0,0) not in allowed
    results['continuation_synthesis']=dict(cases=rows,exhaustive_behavior_checks=checks,
        alpha_equivalent_terms=True,generated_term=synth.pretty(term),bounded_control=cutm,
        correlation_control=dict(allowed=sorted(allowed),projection_product=sorted(projection_product)))
    results['mutations']=mutations(space,rank_entry,church_entry)
    def extra_mutation(name,entry,mutate,check):
        e=deepcopy(entry);mutate(e);ok,msg=check(e['problem'],e['certificate'])
        assert not ok,name
        results['mutations'].append(dict(name=name,accepted=ok,reason=msg))
    extra_mutation('ideal_wrong_multiplier',ideal_positive,
        lambda e:e['certificate']['actions'][0][0].__setitem__(0,[]),check_ideal)
    extra_mutation('ideal_dropped_action',ideal_positive,
        lambda e:e['certificate']['actions'].pop(),check_ideal)
    extra_mutation('ideal_wrong_target',ideal_positive,
        lambda e:e['certificate'].__setitem__('target_coefficients',[[]]),check_ideal)
    extra_mutation('ideal_changed_initialization',ideal_positive,
        lambda e:e['problem']['init'][0].append([[0],[1,1]]),check_ideal)
    extra_mutation('orbit_reversed_word',orbit_negative,
        lambda e:e['certificate']['word'].reverse(),check_orbit_counterexample)
    extra_mutation('orbit_missing_step',orbit_negative,
        lambda e:e['certificate']['word'].pop(),check_orbit_counterexample)
    extra_mutation('orbit_wrong_label',orbit_negative,
        lambda e:e['certificate']['word'].__setitem__(0,99),check_orbit_counterexample)
    extra_mutation('orbit_wrong_parameter_arity',orbit_negative,
        lambda e:e['certificate']['parameters'].append([1,1]),check_orbit_counterexample)
    results['metadata']=dict(seed=SEED,python=sys.version,platform=platform.platform(),
       third_party_dependencies=[],lean_available=shutil.which('lean') is not None,
       lean_kernel_checked=False,elapsed_seconds=perf_counter()-started,
       experiment_scope='Synthetic finite-fragment tests, not Lean/Djex end-to-end benchmarks',
       accepted_certificates=len(entries))
    (out/'results.json').write_text(json.dumps(results,indent=2)+'\n')
    (out/'certificates.json').write_text(json.dumps({'certificates':entries},indent=2)+'\n')
    print(json.dumps({k:v for k,v in results['metadata'].items()},indent=2))
    print(f"Affine differential cases: {len(aff)}; nonlinear cases: {len(nls)}; "
          f"behavior checks: {checks}; rejected mutations: {len(results['mutations'])}")

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out',type=Path,default=Path(__file__).resolve().parents[1]/'reproduced-results')
    args=ap.parse_args();main(args.out)
