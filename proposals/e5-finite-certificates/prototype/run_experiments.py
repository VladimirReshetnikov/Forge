"""Deterministic self-contained corpus; writes only the selected output directory.

Default output: reproduced-results (does not overwrite the recorded run).
Run from the archive root with python -m prototype.run_experiments.
"""
from __future__ import annotations
import argparse, copy, csv, json, platform, random, sys, time
from fractions import Fraction
from itertools import product
from math import comb
from pathlib import Path
from statistics import median
import sympy as s
from .search import linear_problem, linear_search, ideal_problem, ideal_search, sum_problem, sum_search, dec, enc, matrix_from
from .checkers import verify, counterexample

SEED=2026091507

def replay_counterexample(p, r):
    if p['kind']=='linear':
        state=s.Matrix([s.Rational(*z) for z in p['initial']])
        for a in r['word']:
            state=matrix_from(p['actions'][a])*state
        value=(s.Matrix([[s.Rational(*z) for z in p['target']]])*state)[0]
    else:
        xs=s.symbols(f'x0:{p["dimension"]}'); ts=s.symbols(f't0:{p["parameters"]}')
        subst=dict(zip(ts,r['parameters']))
        state=[dec(z,ts).subs(subst) for z in p['initial']]
        for a in r['word']:
            old=dict(zip(xs,state))
            state=[dec(z,xs).subs(old,simultaneous=True) for z in p['actions'][a]]
        value=dec(p['target'],xs).subs(dict(zip(xs,state)),simultaneous=True)
    return value!=0 and value==s.Rational(*r['value'])

def build_cases():
    rng=random.Random(SEED)
    cases=[]
    # Unobserved coordinates evolve arbitrarily; reachable target row space is small.
    for d in range(2,8):
        for trial in range(3):
            r=max(1,d//2)
            acts=[]
            for a in range(2):
                M=s.Matrix(d,d,lambda i,j:rng.randint(-2,2))
                for i in range(r):
                    for j in range(r,d):M[i,j]=0
                acts.append(M)
            initial=[0]*r+[rng.randint(-2,2) for _ in range(d-r)]
            q=[1]+[0]*(d-1)
            p=linear_problem(acts,initial,q)
            cases.append((f'linear_invariant_d{d}_{trial}',p,'certified',{}))
    # Independently represented weighted automata: second via exact basis change.
    for d in range(2,6):
        P=s.eye(d)
        for i in range(d-1):P[i,i+1]=i+1
        Ms=[s.Matrix(d,d,lambda i,j:rng.randint(-2,2)) for _ in range(2)]
        acts=[s.diag(M,P*M*P.inv()) for M in Ms]
        z=s.Matrix([rng.randint(-2,2) for _ in range(d)])
        q=s.Matrix([[1]+[0]*(d-1)])
        p=linear_problem(acts,list(z)+list(P*z),list(q)+list(-q*P.inv()))
        cases.append((f'linear_equivalence_d{d}',p,'certified',{}))
    # Distinguishing word first appears at the sharp length D-1 bound.
    for d in range(2,9):
        M=s.zeros(d)
        for i in range(d-1):M[i,i+1]=1
        p=linear_problem([M],[0]*(d-1)+[1],[1]+[0]*(d-1))
        cases.append((f'linear_late_error_d{d}',p,'counterexample',{}))
    # Noncommuting actions test the action-word direction.
    for trial in range(6):
        acts=[s.Matrix(3,3,lambda i,j:rng.randint(-1,1)) for _ in range(2)]
        acts[0][0,2]=1  # Guarantee the declared negative expectation.
        p=linear_problem(acts,[0,0,1],[1,0,0])
        cases.append((f'linear_random_false_{trial}',p,'counterexample',{}))
    M0=s.zeros(3); M1=s.zeros(3); M0[1,2]=1; M1[0,1]=1
    cases.append(('linear_word_order',linear_problem([M0,M1],[0,0,1],[1,0,0]),'counterexample',{}))
    x,y,z,w,t=s.symbols('x y z w t');a,b=s.symbols('a b')
    p=ideal_problem((x,y,z,w),[(y*y,x,w*w,z)],(a,b),[a,b,a,-b],x-z)
    cases.append(('ideal_mutual_squares',p,'certified',{}))
    cases.append(('ideal_budget',p,'unknown',{'max_extensions':0}))
    bad=ideal_problem((x,y,z,w),[(y*y,x,w*w+1,z)],(a,b),[a,b,a,-b],x-z)
    cases.append(('ideal_mutant_update',bad,'counterexample',{}))
    bad=ideal_problem((x,y,z,w),[(y*y,x,w*w,z)],(a,b),[a,b,a,b+1],x-z)
    cases.append(('ideal_mutant_initial',bad,'counterexample',{}))
    for scale in [1,2,3,5]:
        # xy=scale*z; deliberately non-conserved under both updates.
        acts=[(x*x,y*y,scale*z*z),(x**3,y**3,scale**2*z**3)]
        p=ideal_problem((x,y,z),acts,(a,b),[scale*a,b,a*b],x*y-scale*z)
        cases.append((f'ideal_product_scale{scale}',p,'certified',{}))
    p=ideal_problem((x,y,t),[(y,x+y,-t)],(a,),[0,1,-1],x*x+x*y-y*y-t)
    cases.append(('ideal_cassini',p,'certified',{}))
    p=ideal_problem((x,y,t),[(y,x+y,t)],(a,),[0,1,-1],x*x+x*y-y*y-t)
    cases.append(('ideal_cassini_mutant',p,'counterexample',{}))
    # A chain forces automatic strengthening by several observables.
    for d in [3,4,5]:
        xs=s.symbols(f'x0:{d}');zs=s.symbols(f'z0:{d}'); vs=xs+zs
        F=list(xs[1:])+[xs[0]**2]+list(zs[1:])+[zs[0]**2]
        ps=s.symbols(f'a0:{d}')
        p=ideal_problem(vs,[F],ps,list(ps)+list(ps),xs[0]-zs[0])
        cases.append((f'ideal_chain_d{d}',p,'certified',{}))
    for m, moments in [(1,range(4)),(2,range(3))]:
        for j in moments:
            cases.append((f'sum_binomial_m{m}_moment{j}',sum_problem(m,j),'certified',{'max_p_degree':3,'max_r_degree':6 if (m,j) in [(1,3),(2,2)] else 4}))
    for m,j in [(1,3),(2,2)]:
        cases.append((f'sum_m{m}_moment{j}_small_template',sum_problem(m,j),'unknown',{'max_p_degree':3,'max_r_degree':4}))
    cases.append(('sum_franel_order1_budget',sum_problem(3),'unknown',{'max_p_degree':2,'max_r_degree':2}))
    return cases

def observations(problem, certificate):
    """Numerical differential checks only; not counted as universal proof."""
    if problem['kind']=='binomial_sum':
        n,k=s.symbols('n k'); m=problem['power'];w=dec(problem['weight'],(k,))
        p0,p1=dec(certificate['p0'],(n,)),dec(certificate['p1'],(n,))
        for N in range(31):
            sn=sum(w.subs(k,K)*comb(N,K)**m for K in range(N+1))
            sn1=sum(w.subs(k,K)*comb(N+1,K)**m for K in range(N+2))
            assert p0.subs(n,N)*sn+p1.subs(n,N)*sn1==0
        return 31
    if problem['kind']=='linear':
        acts=[matrix_from(a) for a in problem['actions']]
        q=s.Matrix([[s.Rational(*z) for z in problem['target']]])
        s0=s.Matrix([s.Rational(*z) for z in problem['initial']])
        count=0
        for L in range(5):
            for word in product(range(len(acts)),repeat=L):
                z=s0
                for a in word:z=acts[a]*z
                assert (q*z)[0]==0
                count+=1
        return count
    return 0

def mutate_cert(cert):
    """Perturb each stored nonzero polynomial coefficient or matrix entry.
    Accepted mutations are reported, not assumed unsound: redundant certificates
    can have several valid representations. Tests separately require targeted
    invalid mutations to fail.
    """
    kind=cert['kind']; paths=[]
    if kind=='linear':
        for i,row in enumerate(cert['basis']):
            for j in range(len(row)):paths.append(('basis',i,j))
        for i in range(len(cert['target_weights'])):paths.append(('target_weights',i))
        for a,M in enumerate(cert['action_weights']):
            for i,row in enumerate(M):
                for j in range(len(row)):paths.append(('action_weights',a,i,j))
    else:
        poly_paths=[]
        if kind=='ideal':
            poly_paths += [('generators',i) for i in range(len(cert['generators']))]
            poly_paths += [('target_weights',i) for i in range(len(cert['target_weights']))]
            for a,H in enumerate(cert['action_weights']):
                for i,row in enumerate(H):
                    for j in range(len(row)):poly_paths.append(('action_weights',a,i,j))
        else:poly_paths=[(k,) for k in ('p0','p1','r','relation_multiplier')]
        for pp in poly_paths:
            v=cert
            for a in pp:v=v[a]
            paths += [pp+(i,1) for i in range(len(v))]
    for path in paths:
        mutated=copy.deepcopy(cert);v=mutated
        for p in path[:-1]:v=v[p]
        old=Fraction(*v[path[-1]]);new=old+1
        v[path[-1]]=[new.numerator,new.denominator]
        yield path,mutated

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,default=Path('reproduced-results'));args=ap.parse_args()
    out=args.output;out.mkdir(parents=True,exist_ok=True);(out/'certificates').mkdir(exist_ok=True);(out/'counterexamples').mkdir(exist_ok=True)
    rows=[];mutations=[]
    (out/'problems.json').write_text(json.dumps([{'name':name,'problem':p,'expected':e,'options':o} for name,p,e,o in build_cases()],indent=2)+'\n')
    for name,p,expected,options in build_cases():
        worker={'linear':linear_search,'ideal':ideal_search,'binomial_sum':sum_search}[p['kind']]
        start=time.perf_counter_ns();r=worker(p,**options);search_ns=time.perf_counter_ns()-start
        assert r['status']==expected,(name,r)
        row={'name':name,'family':p['kind'],'expected':expected,'status':r['status'],'search_ms':search_ns/1e6,
             'check_ms':None,'certificate_bytes':0,'observations':0,'stats':r['stats']}
        if r['status']=='certified':
            c=r['certificate']; checks=[]
            for _ in range(5):
                start=time.perf_counter_ns();ok=verify(p,c);checks.append(time.perf_counter_ns()-start);assert ok,name
            row['check_ms']=median(checks)/1e6
            row['observations']=observations(p,c)
            payload={'case':name,'problem':p,'certificate':c}
            data=json.dumps(payload,sort_keys=True,separators=(',',':'))+'\n'
            (out/'certificates'/f'{name}.json').write_text(data)
            row['certificate_bytes']=len(data.encode())
            for path,mutated in mutate_cert(c):
                accepted=verify(p,mutated)
                mutations.append({'case':name,'path':list(path),'accepted':accepted})
        elif r['status']=='counterexample':
            assert replay_counterexample(p,r) and counterexample(p,r),name
            (out/'counterexamples'/f'{name}.json').write_text(json.dumps({'case':name,'problem':p,'counterexample':r},sort_keys=True)+'\n')
            row['counterexample']={key:r[key] for key in ('word','parameters','value') if key in r}
        else:row['reason']=r['reason']
        rows.append(row)
        print(name,r['status'],round(row['search_ms'],3),'ms',flush=True)
    env={'python':sys.version,'sympy':s.__version__,'platform':platform.platform(),'seed':SEED,
         'lean_status':'NOT_RUN: no Lean executable in this environment',
         'timing_protocol':'search once; checker median of five warm invocations; perf_counter_ns; process/import time excluded'}
    summary={'environment':env,'cases':rows,'totals':{'cases':len(rows),
        'certified':sum(r['status']=='certified' for r in rows),'counterexample':sum(r['status']=='counterexample' for r in rows),
        'unknown':sum(r['status']=='unknown' for r in rows),'mutations':len(mutations),
        'mutations_accepted':sum(r['accepted'] for r in mutations)}}
    (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    (out/'mutations.json').write_text(json.dumps(mutations,indent=2)+'\n')
    fields=['name','family','expected','status','search_ms','check_ms','certificate_bytes','observations']
    with (out/'measurements.csv').open('w',newline='') as f:
        wr=csv.DictWriter(f,fieldnames=fields);wr.writeheader();wr.writerows({k:r[k] for k in fields} for r in rows)
    print(json.dumps(summary['totals'],indent=2))
if __name__=='__main__':main()
