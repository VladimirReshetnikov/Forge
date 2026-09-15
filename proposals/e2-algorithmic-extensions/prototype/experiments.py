"""Deterministic generation, replay, negative controls, ablations, and receipts.

Run from any directory. Search uses SymPy. checker.py never imports this file.
Times are one-run observations, NOT stock-tactic benchmarks.
"""
from __future__ import annotations
from copy import deepcopy
from fractions import Fraction as Q
import json
import argparse
from math import comb, factorial
import platform
from pathlib import Path
from random import Random
import subprocess
import sys
from time import perf_counter
import sympy as s
import search as eng
from checker import verify, unique_object, Reject, poly, subst, Work

SEED=20260915
OUT=Path(__file__).resolve().parents[1]/'reproduced-results'

def write(name,obj):
    (OUT/name).write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')

def main():
    global OUT
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=OUT)
    args=parser.parse_args()
    OUT=args.output.resolve()
    if OUT.exists() and any(OUT.iterdir()):
        raise SystemExit('Output must be absent or empty; recorded results are never overwritten.')
    OUT.mkdir(parents=True,exist_ok=True)
    rng=Random(SEED)
    problems={}; certs={}; rows=[]; attacks=[]; checks=[]
    def check(label, condition):
        if not condition:
            raise AssertionError(label)
        checks.append(label)
    def record(name,pc,info,elapsed,ablation=None):
        check(name+'/search_success',pc is not None)
        p,c=pc
        start=perf_counter(); ok,why=verify(p,c); replay=perf_counter()-start
        check(name+'/exact_replay',ok)
        problems[name]=p;certs[name]=c
        row={'id':name,'kind':p['kind'],'search_seconds':elapsed,'replay_seconds':replay,
             'certificate_bytes':len(json.dumps(c,separators=(',',':'))),'details':info}
        if ablation is not None:row['conservation_only']=ablation
        rows.append(row)
    def run(name,fn,*args):
        st=perf_counter();pc,info=fn(*args);tm=perf_counter()-st
        record(name,pc,info,tm)
    x,y,z,u,v,k=s.symbols('x y z u v k')
    invcases=[
        ('scaled_graph',([x,y,z],[u,v],[u,v,u*v],[[2*x,3*y,6*z]],2,z-x*y)),
        ('mutual_cycle',([x,y],[],[0,0],[[y,2*x]],1,x)),
        ('square_counter',([x,y],[],[0,0],[[x+1,y+2*x+1]],2,y-x*x)),
        ('rotation_circle',([x,y],[],[1,0],[[y,-x]],2,x*x+y*y-1)),
        ('relational_accumulators',([x,y,z],[u],[0,u,u],[[x+1,y+x+1,z+x+1]],1,y-z)),
        ('two_branch_graph',([x,y,z],[u,v],[u,v,u*v],[[2*x,3*y,6*z],[-x,4*y,-4*z]],2,z-x*y)),
    ]
    for j in range(18):
        branches=[]
        for _ in range(2):
            a,b,c,d=[rng.randint(-3,3) for _ in range(4)]
            lam=rng.choice([-3,-2,2,3,4])
            branches.append([a*x+b*y,c*x+d*y,(a+c)*x+(b+d)*y+lam*(z-x-y)])
        invcases.append((f'affine_planted_{j:02d}',([x,y,z],[u,v],[u,v,u+v],branches,1,z-x-y)))
    for name,args in invcases:
        st=perf_counter();pc,info=eng.invariant(*args);tm=perf_counter()-st
        ablation=eng.conserved(*args)
        record(name,pc,info,tm,ablation)
        dims=info['dimensions']
        check(name+'/dimension_chain',all(a>=b for a,b in zip(dims,dims[1:])) and len(dims)<=info['features']+2)
    unknowns=[]
    for name,args in [
        ('nonlinear_degree_escape',([x],[],[0],[[x*x]],1,x)),
        ('false_reachable_target',([x],[],[0],[[x+1]],2,x)),
        ('omitted_guard',([x],[],[0],[[x+1]],1,x)),
    ]:
        pc,info=eng.invariant(*args)
        check(name+'/unknown',pc is None)
        unknowns.append({'id':name,'kind':'invariant','status':'UNKNOWN','details':info})
    # The guard omitted in the third example is x<0: no step is enabled at zero.
    # Forgetting it is deliberately conservative, not a counterexample to soundness.
    hyper=[('factorial_weight',(k+1)**2,k,[s.Integer(1),k]),
           ('reciprocal_pair',k,k+2,[s.Integer(1)]),
           ('shifted_reciprocal',k+3,k+5,[s.Integer(1)])]
    for r in [-3,-2,2,3,5,s.Rational(1,2)]:
        tag=str(r).replace('/','_').replace('-','m')
        hyper += [(f'geometric_{tag}',r,1,[s.Integer(1)]),
                  (f'weighted_geometric_{tag}',r*(k+1),k,[s.Integer(1),k])]
    for name,A,B,ds in hyper:
        run(name,eng.gosper,A,B,k,ds,5)
    for name,A,B in [('factorial_unknown',k+1,1),('harmonic_unknown',k,k+1)]:
        pc,info=eng.gosper(A,B,k,[s.Integer(1),k,k+1],5)
        check(name+'/unknown',pc is None)
        unknowns.append({'id':name,'kind':'gosper','status':'UNKNOWN','details':info})
    st=perf_counter();pc,info=eng.binomial_square_telescoper();tm=perf_counter()-st
    record('binomial_square_telescoper',pc,info,tm)
    # Independent concrete sequence/boundary regression: not used to accept identities.
    boundary_checks=0
    for n in range(31):
        def choose(N,K): return comb(N,K) if 0<=K<=N else 0
        def t(N,K): return choose(N,K)**2
        def G(K): return Q(K*K*(2*K-3*n-3), (n+1)**2)*t(n+1,K)
        for j in range(n+2):
            check(f'binomial_boundary/{n}/{j}', (n+1)*t(n+1,j)-2*(2*n+1)*t(n,j)==G(j+1)-G(j))
            boundary_checks+=1
        check(f'binomial_sum/{n}',sum(t(n,j) for j in range(n+1))==comb(2*n,n))
        check(f'binomial_flux/{n}',G(0)==0 and G(n+2)==0 and G(n+1)==-(n+1))
    # Check concrete sequence identity for the singular-denominator factorial case.
    for a in range(1,9):
        for b in range(a,12):
            check(f'factorial_sum/{a}/{b}',sum(j*factorial(j) for j in range(a,b))==factorial(b)-factorial(a))
    X={(0,):Q(1)};Y={(1,):Q(1)};one={():Q(1)}
    add,mul,pow,scale=eng.nc_add,eng.nc_mul,eng.nc_pow,eng.nc_scale
    comm=add(mul(X,Y),scale(mul(Y,X),-1))
    weyl=add(comm,scale(one,-1))
    for d in range(2,9):
        f=add(add(mul(X,pow(Y,d)),scale(mul(pow(Y,d),X),-1)),scale(pow(Y,d-1),-d))
        run(f'weyl_commutator_{d}',eng.two_sided,[weyl],f,2,d+1)
    for q in [-2,-1,2,3,Q(1,2)]:
        rel=add(mul(X,Y),scale(mul(Y,X),-q))
        f=add(mul(pow(X,2),pow(Y,2)),scale(mul(pow(Y,2),pow(X,2)),-q**4))
        run(f'q_commute_{str(q).replace("/","_")}',eng.two_sided,[rel],f,2,4)
    rels=[add(pow(X,2),scale(X,-1)),add(pow(Y,2),scale(Y,-1)),comm]
    join=add(add(X,Y),scale(mul(X,Y),-1))
    run('commuting_idempotent_join',eng.two_sided,rels,add(pow(join,2),scale(join,-1)),2,4)
    # Random guaranteed ideal members, independent of any rewrite orientation.
    for j in range(12):
        f={}
        for _ in range(5):
            r=rng.randrange(3); ell=rng.randrange(3); rr=rng.randrange(3-ell)
            l=tuple(rng.randrange(2) for _ in range(ell))
            vword=tuple(rng.randrange(2) for _ in range(rr))
            coef=rng.choice([-3,-2,-1,1,2,3])
            f=add(f,scale(mul(mul({l:Q(1)},rels[r]),{vword:Q(1)}),coef))
        if not f: f=comm.copy()
        run(f'nc_planted_{j:02d}',eng.two_sided,rels,f,2,4)
    for name,rs,f in [('commutativity_not_given',[],comm),('one_sided_trap',[mul(X,Y)],mul(Y,X))]:
        pc,info=eng.two_sided(rs,f,2,5)
        check(name+'/unknown',pc is None)
        unknowns.append({'id':name,'kind':'two_sided','status':'UNKNOWN','details':info})
    # Mutations alter binding, coefficients, closure, and word orientation.
    def attack(name,p,c):
        ok,why=verify(p,c)
        check(name+'/reject',not ok)
        attacks.append({'id':name,'reason':why})
    for name,p in problems.items():
        c=deepcopy(certs[name]);kind=p['kind']
        if kind=='invariant': c['target_coeffs']=['0']*len(c['target_coeffs'])
        elif kind=='gosper': c['U']=[]
        elif kind=='telescoper': c['c1']=[]
        else: c['terms']=[]
        attack(name+'/missing_payload',p,c)
        c=deepcopy(certs[name]);c['unexpected_field']=True
        attack(name+'/unknown_field',p,c)
    for name in [r['id'] for r in rows if r['kind']=='invariant']:
        p=deepcopy(problems[name]);c=deepcopy(certs[name]);p['target']=eng.enc(1,[x]*0+[x,y,z][:p['arity']])
        attack(name+'/wrong_target',p,c)
        c=deepcopy(certs[name]);c['matrices']=c['matrices'][:-1]
        attack(name+'/missing_branch',problems[name],c)
    # A valid first-branch invariant that is not stable under a added second branch.
    p=deepcopy(problems['scaled_graph']); c=deepcopy(certs['scaled_graph'])
    p['transitions'].append([eng.enc(x,[x,y,z]),eng.enc(y,[x,y,z]),eng.enc(z+1,[x,y,z])]);c['matrices'].append(deepcopy(c['matrices'][0]))
    attack('invariant/unproved_added_branch',p,c)
    p=deepcopy(problems['factorial_weight']);c=deepcopy(certs['factorial_weight']);c['V']=[]
    attack('gosper/zero_denominator',p,c)
    c=deepcopy(certs['factorial_weight']);c['U'][0]['c']=1.0
    attack('gosper/floating_coefficient',problems['factorial_weight'],c)
    c=deepcopy(certs['factorial_weight']);c['U'][0]['c']='2/2'
    attack('gosper/noncanonical_rational',problems['factorial_weight'],c)
    c=deepcopy(certs['factorial_weight']);c['U'].append(deepcopy(c['U'][0]))
    attack('gosper/duplicate_monomial',problems['factorial_weight'],c)
    c=deepcopy(certs['binomial_square_telescoper']); c['c1']=eng.enc(k,[s.Symbol('n'),k])
    attack('telescoper/k_dependent_coefficient',problems['binomial_square_telescoper'],c)
    p=deepcopy(problems['weyl_commutator_4']);p['relations'][0]=eng.nc_enc(scale(weyl,-1))
    attack('nc/changed_relation',p,certs['weyl_commutator_4'])
    c=deepcopy(certs['weyl_commutator_4']);c['terms'][0]['relation']=True
    attack('nc/boolean_relation_index',problems['weyl_commutator_4'],c)
    c=deepcopy(certs['weyl_commutator_4']);c['terms'][0]['left']=[20]
    attack('nc/unknown_letter',problems['weyl_commutator_4'],c)
    c=deepcopy(certs['weyl_commutator_4']);c['terms'][0]['coefficient']='1/99999999999999999999'
    attack('nc/tiny_exact_mutation',problems['weyl_commutator_4'],c)
    try:
        json.loads('{"a":1,"a":2}',object_pairs_hook=unique_object)
        check('decoder/duplicate_json_key',False)
    except Reject:
        check('decoder/duplicate_json_key',True)
    # Different algorithms: sparse checker substitution vs SymPy expand.
    for j in range(100):
        p=sum(rng.randint(-3,3)*x**a*y**b for a in range(3) for b in range(3-a))
        t=[rng.randint(-3,3)*x+rng.randint(-2,2)*y+rng.randint(-2,2),x-y]
        got=subst(poly(eng.enc(p,[x,y]),2),[poly(eng.enc(z,[x,y]),2) for z in t],2,Work())
        expected=poly(eng.enc(eng.substitute(p,[x,y],t),[x,y]),2)
        check(f'differential/substitution/{j}',got==expected)
    summary={'seed':SEED,'python':sys.version,'platform':platform.platform(),'sympy':s.__version__,
             'status':'PYTHON_SEARCH_AND_REPLAY_ONLY','lean_status':'NOT_RUN_NO_EXECUTABLE',
             'stock_tactic_comparison':'NOT_RUN',
             'accepted_certificates':len(problems),'rejected_mutations':len(attacks),
             'assertions':len(checks),'differential_substitution_cases':100,
             'binomial_pointwise_regressions':boundary_checks,'binomial_n_range':[0,30],
             'expected_unknowns':len(unknowns),
             'families':{kind:sum(r['kind']==kind for r in rows) for kind in ['invariant','gosper','telescoper','two_sided']},
             'invariant_ablation':{'same_feature_cases':len(invcases),'subspace_solved':len(invcases),
                                  'conservation_only_solved':sum(bool(r.get('conservation_only')) for r in rows)},
             'search_seconds_by_family':{kind:sum(r['search_seconds'] for r in rows if r['kind']==kind) for kind in ['invariant','gosper','telescoper','two_sided']},
             'replay_seconds_by_family':{kind:sum(r['replay_seconds'] for r in rows if r['kind']==kind) for kind in ['invariant','gosper','telescoper','two_sided']}}
    write('problems.json',problems);write('certificates.json',certs)
    write('measurements.json',rows);write('mutations.json',attacks);write('unknowns.json',unknowns)
    write('assertions.json',checks);write('summary.json',summary)
    completed=subprocess.run([sys.executable,'-S',str(Path(__file__).with_name('checker.py')),str(OUT/'problems.json'),str(OUT/'certificates.json')],capture_output=True,text=True,timeout=45)
    (OUT/'stdlib-replay.log').write_text(completed.stdout+completed.stderr)
    check('subprocess/stdlib_only',completed.returncode==0)
    summary['assertions']=len(checks)
    summary['stdlib_replay_returncode']=completed.returncode
    write('summary.json',summary);write('assertions.json',checks)
    print(json.dumps(summary,indent=2))

if __name__=='__main__': main()
