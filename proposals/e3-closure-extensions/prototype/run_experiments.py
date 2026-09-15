#!/usr/bin/env python3
"""Deterministic research experiments; writes only to an explicit output directory.

Units are cases, independent oracle comparisons, and diagnostic evaluations.
Nothing in this runner invokes Lean or benchmarks an existing Lean tactic.
"""
from __future__ import annotations
import argparse, copy, csv, itertools, json, math, platform, random, sys
from collections import Counter
from pathlib import Path
from time import perf_counter
import sympy as sp
from forge_closure.search import (ClosureLimits, make_problem, pullback_search,
    ideal_search, make_moment, telescoper_search, moore_search, expression)
from forge_closure.checker import verify, Invalid

SEED = 20260915

def gfp_equivalent(p):
    """Independent oracle: greatest fixed point, no reachability/BFS."""
    l,r = p['left'],p['right']
    relation={(i,j) for i,x in enumerate(l['outputs']) for j,y in enumerate(r['outputs']) if x==y}
    while True:
        smaller={(i,j) for i,j in relation if all((l['transitions'][i][a],r['transitions'][j][a]) in relation for a in range(p['alphabet_size']))}
        if smaller==relation:
            return (l['initial'],r['initial']) in relation
        relation=smaller


def random_machine(rng,n,k):
    return {'initial':rng.randrange(n),'transitions':[[rng.randrange(n) for _ in range(k)] for _ in range(n)],'outputs':[rng.randrange(3) for _ in range(n)]}


def relabel_machine(rng,m,k):
    n=len(m['outputs']); permutation=list(range(n)); rng.shuffle(permutation)
    out=[None]*(n+1); trans=[None]*(n+1)
    for old,new in enumerate(permutation):
        out[new]=m['outputs'][old]
        trans[new]=[permutation[j] for j in m['transitions'][old]]
    out[n]=999; trans[n]=[n]*k  # deliberately unreachable junk
    return {'initial':permutation[m['initial']],'transitions':trans,'outputs':out}


def observation(m,word):
    s=m['initial']
    for a in word:s=m['transitions'][s][a]
    return m['outputs'][s]


def run(out):
    out.mkdir(parents=True,exist_ok=True)
    certdir=out/'certificates'; certdir.mkdir(exist_ok=True)
    rng=random.Random(SEED); cases=[]; bundles={}; diagnostics=[]
    def save(name,family,p,r,expected=None):
        if expected is not None and r['status']!=expected:
            raise AssertionError((name,r,expected))
        row={'name':name,'family':family,'status':r['status'],'reason':r.get('reason'),**r['statistics']}
        if r.get('certificate') is not None:
            start=perf_counter(); verify(p,r['certificate']); row['replay_seconds']=perf_counter()-start
            bundle={'case':name,'problem':p,'certificate':r['certificate']}
            data=json.dumps(bundle,sort_keys=True,indent=2)+'\n'
            (certdir/(name+'.json')).write_text(data)
            row['bundle_bytes']=len(data.encode()); bundles[name]=bundle
        cases.append(row)
        return r
    x,y,u,v,t=sp.symbols('x y u v t')
    coupled=make_problem((x,y,u,v),[(y,x+y,v,u+v)],(0,1,0,1),[x*x+y*y-u*u-v*v])
    save('coupled_quadratic','vector_named',coupled,pullback_search(coupled),'proved')
    cassini=make_problem((x,y,t),[(y,x+y,-t)],(0,1,1),[y*y-x*y-x*x-t])
    save('cassini_sign','vector_named',cassini,pullback_search(cassini),'proved')
    square=make_problem((x,y),[(x*x,y*y)],(2,2),[x-y])
    save('squaring_vector_ceiling','vector_ablation',square,pullback_search(square),'unknown')
    save('squaring_ideal','ideal_named',square,ideal_search(square),'proved')
    # First nonzero target occurs for word [0,1], not [1,0].
    # State x flags a preceding 0; symbol 1 copies x into target y.
    order=make_problem((x,y),[(sp.Integer(1),y),(x,x)],(0,0),[y])
    save('ordered_word_vector','vector_negative',order,pullback_search(order),'refuted')
    save('ordered_word_ideal','ideal_negative',order,ideal_search(order),'refuted')
    assert bundles['ordered_word_vector']['certificate']['word']==[0,1]
    # Two arbitrary affine updates, synchronized copies, quadratic observation.
    for i in range(24):
        matrices=[[[rng.randrange(-2,3) for _ in range(2)] for _ in range(2)] for _ in range(2)]
        shifts=[[rng.randrange(-2,3) for _ in range(2)] for _ in range(2)]
        fs=[]
        for a,c in zip(matrices,shifts):
            fs.append((a[0][0]*x+a[0][1]*y+c[0],a[1][0]*x+a[1][1]*y+c[1],a[0][0]*u+a[0][1]*v+c[0],a[1][0]*u+a[1][1]*v+c[1]))
        init=[rng.randrange(-2,3),rng.randrange(-2,3)]
        coeff=[rng.randrange(-2,3) for _ in range(5)]
        q=coeff[0]*x*x+coeff[1]*x*y+coeff[2]*y*y+coeff[3]*x+coeff[4]*y
        g=q-q.subs({x:u,y:v},simultaneous=True)
        p=make_problem((x,y,u,v),fs,init+init,[g])
        save(f'affine_pair_{i:02}','vector_generated',p,pullback_search(p),'proved')
    # Synchronized nonlinear scalar maps, two transition symbols.
    for i in range(16):
        degree=2+i%3; c=rng.randrange(-3,4); d=rng.randrange(-2,3)
        fs=[(x**degree+c*x+d,y**degree+c*y+d),(x*x+c,y*y+c)]
        z=rng.randrange(-2,3)
        p=make_problem((x,y),fs,(z,z),[x-y])
        save(f'nonlinear_pair_{i:02}','ideal_generated',p,ideal_search(p),'proved')
    # An evolving product requires an additional ideal generator.
    p=make_problem((x,y),[(y,x+y)],(0,0),[x*y])
    save('ideal_joint_product','ideal_named',p,ideal_search(p),'proved')
    # False polynomial assertions, not only changed initial-state examples.
    for i in range(16):
        p=make_problem((x,y),[(y,x+i+1)],(0,0),[x])
        save(f'false_recurrence_{i:02}','vector_negative',p,pullback_search(p),'refuted')
    # Differential finite-state corpus with 120 forced equivalences and 120 random pairs.
    oracle_count=0
    for i in range(240):
        k=1+i%3; nl=rng.randrange(2,9)
        l=random_machine(rng,nl,k)
        r=relabel_machine(rng,l,k) if i%2==0 else random_machine(rng,rng.randrange(2,9),k)
        p={'kind':'moore_equivalence_v1','alphabet_size':k,'left':l,'right':r}
        truth=gfp_equivalent(p); oracle_count+=1
        save(f'moore_{i:03}','finite_state',p,moore_search(p),'proved' if truth else 'refuted')
    length=17
    l={'initial':0,'transitions':[[min(i+1,length)] for i in range(length+1)],'outputs':[0]*length+[1]}
    r={'initial':0,'transitions':[[0]],'outputs':[0]}
    p={'kind':'moore_equivalence_v1','alphabet_size':1,'left':l,'right':r}
    samples=[observation(l,[0]*i)==observation(r,[0]*i) for i in range(9)]
    rr=save('late_difference','finite_state_ablation',p,moore_search(p),'refuted')
    assert all(samples) and len(rr['certificate']['word'])==length
    save('late_difference_budget','finite_state_budget',p,moore_search(p,max_pairs=8),'unknown')
    diagnostics.append({'kind':'bounded_sampling_ablation','sampled_lengths':list(range(9)),'all_samples_agree':all(samples),'shortest_counterexample_length':length})
    # Polynomial moments: exact symbolic certificates, then separate numeric diagnostics.
    k,n=sp.symbols('k n')
    moment_specs=[(m,k**r) for m in (1,2) for r in range(4)]
    moment_specs.extend([(1,2*k*k+3*k+1),(2,2*k*k+3*k+1)])
    numeric_checks=0
    for i,(m,w) in enumerate(moment_specs):
        p=make_moment(m,w,k)
        r=save(f'moment_{i:02}','telescoping',p,telescoper_search(p,max_degree=6,max_u_degree=9),'proved')
        a=expression(r['certificate']['a'],(n,)); b=expression(r['certificate']['b'],(n,))
        for j in range(21):
            def moment(z):return sum(w.subs(k,h)*math.comb(z,h)**m for h in range(z+1))
            assert a.subs(n,j)*moment(j+1)==b.subs(n,j)*moment(j)
            numeric_checks+=1
        diagnostics.append({'kind':'moment_formula','name':f'moment_{i:02}','power':m,'weight':str(w),'a':str(a),'b':str(b),'u':str(expression(r['certificate']['u'],(n,k))),'start':r['certificate']['start']})
    p=make_moment(1,k**3,k)
    save('cubic_moment_low_cap','telescoping_budget',p,telescoper_search(p,max_degree=4,max_u_degree=5),'unknown')
    p=make_moment(3,sp.Integer(1),k)
    save('franel_capped_first_order','telescoping_budget',p,telescoper_search(p,max_degree=1,max_u_degree=2),'unknown')
    # Targeted invalid certificates. These are NOT arbitrary mutations: each breaks a requirement.
    mutations=[]
    def reject(name,key,edit):
        b=copy.deepcopy(bundles[key]); edit(b)
        try:verify(b['problem'],b['certificate'])
        except Invalid as e:mutations.append({'name':name,'rejected':True,'message':str(e)})
        else:raise AssertionError('accepted invalid mutation '+name)
    reject('closure_bad_coefficient','coupled_quadratic',lambda b:b['certificate']['steps'][0][0].__setitem__(0,[1,1]))
    reject('closure_missing_transition','coupled_quadratic',lambda b:b['certificate'].__setitem__('steps',[]))
    reject('closure_wrong_initial','coupled_quadratic',lambda b:b['problem']['initial'].__setitem__(0,[1,1]))
    reject('closure_target_not_bound','coupled_quadratic',lambda b:b['problem']['targets'][0].append([[0,0,0,0],[1,1]]))
    reject('closure_float_coefficient','coupled_quadratic',lambda b:b['certificate']['steps'][0][0].__setitem__(0,[0.0,1]))
    reject('closure_boolean_coefficient','coupled_quadratic',lambda b:b['certificate']['steps'][0][0].__setitem__(0,[False,1]))
    reject('closure_zero_denominator','coupled_quadratic',lambda b:b['certificate']['steps'][0][0].__setitem__(0,[0,0]))
    reject('closure_unreduced_rational','coupled_quadratic',lambda b:b['certificate']['steps'][0][0].__setitem__(0,[0,2]))
    reject('ideal_bad_multiplier','squaring_ideal',lambda b:b['certificate']['steps'][0][0].__setitem__(0,[]))
    reject('ideal_missing_generator','ideal_joint_product',lambda b:b['certificate']['basis'].pop())
    reject('negative_word_reversed','ordered_word_vector',lambda b:b['certificate']['word'].reverse())
    reject('negative_word_empty','ordered_word_ideal',lambda b:b['certificate'].__setitem__('word',[]))
    reject('negative_word_invalid_symbol','ordered_word_vector',lambda b:b['certificate'].__setitem__('word',[2]))
    eqkey=next(name for name,b in bundles.items() if b['certificate']['kind']=='moore_bisimulation_v1' and len(b['certificate']['relation'])>1)
    root=[bundles[eqkey]['problem']['left']['initial'],bundles[eqkey]['problem']['right']['initial']]
    reject('machine_relation_missing_root',eqkey,lambda b:b['certificate']['relation'].remove(root))
    reject('machine_relation_duplicate',eqkey,lambda b:b['certificate']['relation'].append(copy.deepcopy(root)))
    reject('machine_observation_changed',eqkey,lambda b:b['problem']['right']['outputs'].__setitem__(root[1],9999))
    reject('machine_word_too_short','late_difference',lambda b:b['certificate']['word'].pop())
    reject('machine_word_invalid_symbol','late_difference',lambda b:b['certificate'].__setitem__('word',[1]))
    reject('telescoper_wrong_flux','moment_04',lambda b:b['certificate'].__setitem__('u',[]))
    reject('telescoper_zero_leading','moment_00',lambda b:b['certificate'].__setitem__('a',[]))
    reject('telescoper_wrong_weight','moment_04',lambda b:b['problem'].__setitem__('weight',[[[1],[1,1]]]))
    reject('telescoper_wrong_power','moment_04',lambda b:b['problem'].__setitem__('power',1))
    reject('telescoper_forbidden_power_zero','moment_00',lambda b:b['problem'].__setitem__('power',0))
    reject('telescoper_bad_regularity_sign','moment_00',lambda b:b['certificate'].__setitem__('sign',-1))
    # k^2 binomial moment has a(0)=0 after cancellation, so start=0 is invalid.
    singular=next(name for name,b in bundles.items() if b['certificate']['kind']=='binomial_flux_v1' and b['certificate']['start']>0)
    reject('telescoper_false_regularity_start',singular,lambda b:b['certificate'].__setitem__('start',0))
    (out/'mutations.json').write_text(json.dumps(mutations,indent=2)+'\n')
    (out/'diagnostics.json').write_text(json.dumps(diagnostics,indent=2)+'\n')
    fields=sorted(set().union(*(set(c) for c in cases)))
    with (out/'cases.csv').open('w',newline='') as f:
        wr=csv.DictWriter(f,fieldnames=fields); wr.writeheader(); wr.writerows(cases)
    families={}
    for name in sorted(set(c['family'] for c in cases)):
        cc=[c for c in cases if c['family']==name]
        families[name]={'cases':len(cc),'outcomes':dict(Counter(c['status'] for c in cc)),'search_seconds_total':sum(c['seconds'] for c in cc),'replay_seconds_total':sum(c.get('replay_seconds',0) for c in cc)}
    summary={'seed':SEED,'python':sys.version,'platform':platform.platform(),'sympy':sp.__version__,
      'lean_status':'NOT_RUN: no Lean executable available','comparison_against_lean_tactics':'NOT_RUN',
      'case_count':len(cases),'certificate_bundles':len(bundles),'outcomes':dict(Counter(c['status'] for c in cases)),
      'independent_finite_state_oracle_comparisons':oracle_count,'diagnostic_moment_evaluations':numeric_checks,
      'targeted_invalid_mutations':len(mutations),'all_targeted_invalid_mutations_rejected':all(m['rejected'] for m in mutations),
      'families':families,'limits':{'closure':ClosureLimits().__dict__,'ideal_multiplier_degree':4,'moore_pairs':10000,
        'moment_coefficient_degree':6,'moment_flux_degree':9,'negative_moment_coefficient_degree':1,'negative_moment_flux_degree':2}}
    (out/'run.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':
    parser=argparse.ArgumentParser(); parser.add_argument('--out',type=Path,default=Path('reproduced-results'))
    args=parser.parse_args(); run(args.out)
