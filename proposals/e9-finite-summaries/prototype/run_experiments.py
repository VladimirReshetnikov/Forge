#!/usr/bin/env python3
"""Deterministic research corpus. Writes only to a new/empty output directory."""
import argparse,json,random,time,platform,sys,math,copy
from pathlib import Path
from fractions import Fraction as Q
from itertools import product
from collections import Counter
import sympy as s
from forge_summaries.exact import *
from forge_summaries.linear_search import search,model,polynomial_input_search
from forge_summaries.lift import compile_lift
from forge_summaries.telescoping_search import attempt,poly,n,k
from forge_summaries.ore_search import common_left_multiple,singularity_cover
from forge_summaries.check import verify_bundle

SEED=681437

def main(out):
    out=Path(out)
    if out.exists() and any(out.iterdir()): raise SystemExit('output directory must be new or empty')
    out.mkdir(parents=True,exist_ok=True)
    rng=random.Random(SEED); entries=[]; runs=[]; mutations=[]; start=time.perf_counter()
    def record(name,checker,problem,certificate,stats=None):
        b={'checker':checker,'problem':problem,'certificate':certificate}
        assert verify_bundle(b),('certificate failed',name)
        entries.append({'name':name,'bundle':b}); runs.append({'name':name,'checker':checker,**(stats or {})})
    def word_case(name,u,ms,v):
        t=time.perf_counter(); c,stats=search(u,ms,v)
        stats['search_seconds']=time.perf_counter()-t
        checker='linear' if c['kind']=='linear-closure' else 'counterexample'
        record(name,checker,model(u,ms,v),c,stats); return c
    # All words of length <= d-1: a deliberately exponential differential oracle.
    differential=0; finite_evaluations=0
    for d in range(1,6):
        for trial in range(20):
            ms=[[[Q(rng.randint(-2,2)) for _ in range(d)] for _ in range(d)] for _ in range(2)]
            u=[Q(rng.randint(-2,2)) for _ in range(d)]; v=[Q(rng.randint(-2,2)) for _ in range(d)]
            c=word_case(f'random-d{d}-{trial:02}',u,ms,v)
            oracle=True
            for length in range(d):
                for word in product(range(2),repeat=length):
                    row=u
                    for a in word: row=rowmul(row,ms[a])
                    finite_evaluations+=1
                    if dot(row,v): oracle=False
            assert oracle==(c['kind']=='linear-closure')
            differential+=1
    # Equivalent realizations, randomly changed by invertible triangular coordinates.
    for d in range(2,7):
        for trial in range(8):
            A=[s.Matrix([[rng.randint(-3,3) for _ in range(d)] for _ in range(d)]) for _ in range(2)]
            T=s.eye(d)
            for i in range(d):
                T[i,i]=rng.choice([1,2,3])
                for j in range(i+1,d): T[i,j]=rng.randint(-2,2)
            Ti=T.inv(); u=s.Matrix([[rng.randint(-2,2) for _ in range(d)]]); v=s.Matrix([rng.randint(-2,2) for _ in range(d)])
            conv=lambda x:Q(int(x.p),int(x.q))
            init=list(map(conv,list(u)+list(u*T)))
            output=list(map(conv,list(v)+list(-Ti*v)))
            ms=[[[conv(x) for x in row] for row in s.diag(a,Ti*a*T).tolist()] for a in A]
            c=word_case(f'conjugate-d{d}-{trial:02}',init,ms,output)
            assert c['kind']=='linear-closure'
    # Tight witness-length controls. No word shorter than d-1 separates.
    for d in range(2,25):
        M=[[int(j==i+1) for j in range(d)] for i in range(d)]
        u=[int(i==0) for i in range(d)]; v=[int(i==d-1) for i in range(d)]
        c=word_case(f'delayed-d{d}',u,[M],v)
        assert c['kind']=='separating-word' and len(c['word'])==d-1
    # Exact polynomial lift: all finite words over a pair of affine transitions.
    a,b,c,x=s.symbols('a b c x')
    u,ms,v,liftstats=compile_lift([a,b,c],[0,1,1],[[b,a+b,-c],[a+b,a+2*b,c]],b*b-a*b-a*a-c,2)
    cert=word_case('cassini-one-or-two-steps',u,ms,v); assert cert['kind']=='linear-closure'
    runs[-1].update(liftstats)
    # Infinite input alphabet: the grid is a complete spanning alphabet, not samples.
    h,j,g=s.symbols('h j g')
    for base in [-2,0,1,3]:
        u,co,v,st=compile_lift([h,j,g],[0,0,0],[[base*h+x,base*j+2*x+3,base*g+1]],j-2*h-3*g,1,x)
        t=time.perf_counter(); cert,stats=polynomial_input_search(u,co,v)
        assert cert['kind']=='linear-closure'
        record(f'horner-polynomial-input-b{base}','linear',model(u,co,v),cert,{**st,**stats,'search_seconds':time.perf_counter()-t})
    # A degree-two input bug vanishes at 0 and 1, but is exposed by required grid 0,1,2.
    u,co,v,st=compile_lift([h],[0],[[h+x*(x-1)]],h,1,x)
    cert,stats=polynomial_input_search(u,co,v)
    values=[[[sum(co[t][i][j]*z**t for t in range(len(co))) for j in range(len(u))] for i in range(len(u))] for z in range(len(co))]
    assert cert['kind']=='separating-word' and cert['word']==[2]
    record('polynomial-input-grid-trap','counterexample',model(u,values,v),cert,{**st,**stats})
    # Prescribed bounded telescoper requests, including honest misses.
    requests=[(1,Q(q),1,0,0) for q in range(-5,6)]
    requests += [(2,Q(q),2,1,1) for q in [-3,-2,-1,0,2,3,4]]
    requests += [(2,Q(1),1,1,1),(2,Q(1,2),2,1,1),(2,Q(-2,3),2,1,1),
                 (3,Q(1),2,2,2),(4,Q(1),3,3,3),
                 (3,Q(1),1,1,1),(4,Q(1),1,1,1)]
    unknown=[]; direct_checks=0
    for p,q,r,da,dp in requests:
        name=f'telescope-p{p}-q{q}-r{r}-a{da}-f{dp}'
        t=time.perf_counter(); cert,stats=attempt(p,q,r,da,dp); stats['search_seconds']=time.perf_counter()-t
        problem={'kind':'binomial-power-sum','power':p,'weight':encq(q)}
        if cert is None:
            unknown.append({'name':name,**stats,'status':'UNKNOWN_FIXED_ANSATZ'});continue
        record(name,'telescoper',problem,cert,stats)
        aa=decode_operator(cert['operator']); ps=[decode_poly(z) for z in cert['flux']]
        choose=lambda n,k:math.comb(n,k) if 0<=k<=n else 0
        seq=lambda n:sum((q**k*choose(n,k)**p for k in range(n+1)),Q(0))
        for nn in range(21):
            assert sum(evalp(ai,nn)*seq(nn+i) for i,ai in enumerate(aa))==0
            direct_checks+=1
            # All interior and boundary cells, including q=0 and n=0.
            for kk in range(nn+r+1):
                flux=lambda k:sum(evalp(pj,nn,k)*q**k*choose(nn+j,k-1)**p for j,pj in enumerate(ps))
                lhs=sum(evalp(ai,nn)*q**kk*choose(nn+i,kk)**p for i,ai in enumerate(aa))
                assert lhs==flux(kk+1)-flux(kk)
        plan=singularity_cover(aa)
        assert plan is not None
        record(name+'-seeds','singularities',{'kind':'recurrence-equality-plan','operator':cert['operator']},plan)
    # Noncommutative common-left-multiple identities.
    ore_requests=[([poly(-c),poly(1)],[poly(-d),poly(1)],1,0) for c,d in [(2,3),(-1,1),(0,5),(2,2)]]
    ore_requests += [([poly(-n-1),poly(1)],[poly(-2*n-2),poly(1)],1,2),
                     ([poly(-n-1),poly(1)],[poly(-2),poly(1)],1,2)]
    for i,(A,B,mo,md) in enumerate(ore_requests):
        t=time.perf_counter(); cert,stats=common_left_multiple(A,B,mo,md)
        assert cert is not None
        record(f'ore-{i}','ore',{'kind':'common-left-multiple','left':[encpoly(a) for a in A],
                               'right':[encpoly(b) for b in B]},cert,{**stats,'search_seconds':time.perf_counter()-t})
    # Natural leading-coefficient singularities and required seed resets.
    rootsets=[[],[0],[5],[0,3],[1,2],[2,4],[3,7],[0,1,5]]
    for roots in rootsets:
        for order in [1,2,3]:
            lead=poly(s.prod(n-r for r in roots)); A=[scale(lead,-2)]+[{}]*(order-1)+[lead]
            cert=singularity_cover(A); assert cert is not None
            record(f'singular-{roots}-r{order}','singularities',{'kind':'recurrence-equality-plan','operator':[encpoly(z) for z in A]},cert)
    # Every mutation has a known invalidating change, not random noise.
    for entry in entries:
        b=entry['bundle']; bad=copy.deepcopy(b); c=bad['certificate'];typ=b['checker']
        if typ=='linear':
            # Change authoritative initial vector but not its certified coordinates.
            bad['problem']['initial'][0][0]+=bad['problem']['initial'][0][1]
        elif typ=='counterexample': c['value']=[0,1]
        elif typ=='telescoper':
            pp=decode_poly(c['operator'][-1]);c['operator'][-1]=encpoly(add(pp,const(1)))
        elif typ=='ore':
            pp=decode_poly(c['common'][-1]);c['common'][-1]=encpoly(add(pp,const(1)))
        else: c['seed_indices']=c['seed_indices'][1:]
        rejected=not verify_bundle(bad);assert rejected,(entry['name'],'mutation survived')
        mutations.append({'name':entry['name'],'kind':typ,'rejected':rejected})
    # Report one corpus, never pool upstream Forge's unrelated nine runs.
    summary={'seed':SEED,'python':sys.version,'sympy':s.__version__,'platform':platform.platform(),
      'status':'PASS','lean_status':'NOT_RUN_NO_EXECUTABLE','elapsed_seconds':time.perf_counter()-start,
      'certificate_entries':len(entries),'by_checker':dict(Counter(e['bundle']['checker'] for e in entries)),
      'differential_models':differential,'exhaustive_word_evaluations':finite_evaluations,
      'direct_recurrence_checks':direct_checks,'mutation_cases':len(mutations),
      'rejected_mutations':sum(x['rejected'] for x in mutations),'unknown_requests':unknown}
    for name,obj in [('certificates.json',{'schema':'forge-finite-summaries-v1','entries':entries}),
                     ('runs.json',runs),('mutations.json',mutations),('summary.json',summary)]:
        (out/name).write_text(json.dumps(obj,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--out',required=True);args=ap.parse_args();main(args.out)
