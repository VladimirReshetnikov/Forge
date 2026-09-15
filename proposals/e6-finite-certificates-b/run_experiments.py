#!/usr/bin/env python3
"""Deterministic experiments. Default output never overwrites recorded results."""
from __future__ import annotations
import argparse,json,platform,random,sys,time
from pathlib import Path
import sympy as s
from prototype import ideal,weighted,telescoping
from prototype.check import verify

SEED=20260915

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--out',default='reproduced-results'); args=ap.parse_args()
    out=Path(args.out); out.mkdir(parents=True,exist_ok=True)
    rng=random.Random(SEED)
    corpus=[]; records=[]
    def run(case_id,family,fn,details=None):
        start=time.perf_counter(); answer,info=fn(); search=time.perf_counter()-start
        row={'id':case_id,'family':family,'search_seconds':search,'search_info':info,'details':details or {}}
        if answer is None:
            row['outcome']='unknown'
        else:
            problem,cert=answer
            t=time.perf_counter(); receipt=verify(problem,cert); replay=time.perf_counter()-t
            row.update(outcome=cert['kind'],replay_seconds=replay,replay_details=receipt,
                       certificate_bytes=len(json.dumps(cert,separators=(',',':')).encode()))
            corpus.append({'id':case_id,'problem':problem,'certificate':cert})
        records.append(row)
        print(case_id,row['outcome'],round(search,4),flush=True)
    x,y,z,t=s.symbols('x y z t')
    fixtures=[
      ('curve_scaling',(x,y),[((t,),[t,t*t])],[([2*x,4*y],[])],x*x-y,2),
      ('curve_nonlinear',(x,y),[((t,),[t,t*t])],[([x*x,y*y],[])],x*x-y,2),
      ('curve_two_branches',(x,y),[((t,),[t,t*t])],[([x+1,y+2*x+1],[]),([x*x,y*y],[])],x*x-y,2),
      ('mutual_swap',(x,y,z),[((t,),[0*x,0*x,t])],[([y,x,z+1],[])],x,1),
      ('guarded_update',(x,y),[((t,),[0*x,t])],[([x+y,y+1],[y])],x,1),
      ('finite_orbit_degree2',(x,),[((),[s.Integer(0)])],[([1-x],[])],x*x-x,2),
      ('two_initial_maps',(x,),[((),[s.Integer(0)]),((),[s.Integer(1)])],[([1-x],[])],x*x-x,2),
      ('degree1_miss',(x,),[((),[s.Integer(0)])],[([1-x],[])],x*x-x,1),
      ('false_invariant',(x,),[((),[s.Integer(0)])],[([x+1],[])],x,2),
    ]
    for name,vs,init,trs,goal,d in fixtures:
        cons=ideal.conserved_dimension(vs,init,trs,d)
        run('ideal_'+name,'ideal',lambda vs=vs,init=init,trs=trs,goal=goal,d=d: ideal.discover(vs,init,trs,goal,d),
            {'degree':d,'conserved_subspace_dimension':cons,'goal':str(goal),'variables':[str(v) for v in vs],
             'initial':[[[str(v) for v in p],[str(v) for v in im]] for p,im in init],
             'transitions':[[[str(v) for v in im],[str(v) for v in gs]] for im,gs in trs]})
    for i in range(20):
        a=rng.choice([-3,-2,-1,1,2,3]); b=rng.randint(-3,3); c=rng.choice([-2,-1,1,2]); d=rng.randint(-2,2); e=rng.randint(-3,3)
        tx=(x-b)/a; curve=c*tx**2+d*tx+e; error=y-curve
        f=tx**2+rng.randint(-2,2)
        factor=x+y+rng.randint(-2,2)
        ims=[s.expand(a*f+b),s.expand(c*f*f+d*f+e+factor*error)]
        run(f'ideal_random_curve_{i:02}','ideal',lambda a=a,b=b,c=c,d=d,e=e,ims=ims,error=error:
            ideal.discover((x,y),[((t,),[a*t+b,c*t*t+d*t+e])],[(ims,[])],error,2),
            {'parameters':[a,b,c,d,e],'degree':2})
    run('weighted_subsequence_product','weighted',lambda:weighted.discover(*weighted.subsequence_identity()))
    for i in range(20):
        n=2+i%4
        a=s.zeros(1,n); a[0,0]=1
        ms={letter:s.Matrix(n,n,lambda _i,_j:rng.randint(-2,2)) for letter in ('a','b')}
        beta=s.Matrix([rng.randint(-2,2) for _ in range(n)])
        change=s.eye(n)
        for j in range(n):
            change[j,j]=rng.choice([1,2,3])
            for h in range(j+1,n): change[j,h]=rng.randint(-2,2)
        inv=change.inv()
        left=(a,ms,beta)
        right=(a*change,{letter:inv*m*change for letter,m in ms.items()},inv*beta)
        triple=weighted.difference(left,right)
        run(f'weighted_similarity_{i:02}','weighted',lambda triple=triple:weighted.discover(*triple),{'component_dimension':n})
        ar,mr,br=right
        delta=s.zeros(n,1); delta[0]=ar[0,1]; delta[1]=-ar[0,0]
        bad=weighted.difference(left,(ar,mr,br+delta))
        run(f'weighted_inequivalent_{i:02}','weighted',lambda bad=bad:weighted.discover(*bad),{'component_dimension':n,'initial_outputs_agree':True})
    for n in range(3,8):
        a=s.zeros(1,n); a[0,0]=1
        m=s.zeros(n,n)
        for i in range(n-1):m[i,i+1]=1
        beta=s.zeros(n,1);beta[n-1]=1
        run(f'weighted_delayed_{n}','weighted',lambda a=a,m=m,beta=beta:weighted.discover(a,{'a':m},beta),{'first_distinguishing_length':n-1})
    run('weighted_zero_initial','weighted',lambda:weighted.discover(s.zeros(1,3),{'a':s.eye(3)},s.ones(3,1)))
    run('weighted_empty_alphabet','weighted',lambda:weighted.discover(s.Matrix([[1,1]]),{},s.Matrix([1,-1])))
    for m,r,pd,ud in [(1,1,0,0),(2,1,1,1),(3,2,2,5)]:
        run(f'telescope_binomial_power_{m}','telescoping',lambda m=m,r=r,pd=pd,ud=ud:telescoping.discover(m,r,pd,ud))
    for m,r,pd,ud in [(2,1,0,0),(3,1,2,2)]:
        run(f'telescope_bounded_miss_{m}','telescoping',lambda m=m,r=r,pd=pd,ud=ud:telescoping.discover(m,r,pd,ud))
    meta={'seed':SEED,'python':sys.version,'sympy':s.__version__,'platform':platform.platform(),
          'lean_status':'NOT_RUN: Lean and Lake executables unavailable in this runtime',
          'timing_scope':'single ordered local run; search and independent replay timed separately; not a Lean comparison',
          'cases':records}
    (out/'certificates.json').write_text(json.dumps(corpus,indent=2)+'\n')
    (out/'experiments.json').write_text(json.dumps(meta,indent=2)+'\n')
    summary={}
    for family in ('ideal','weighted','telescoping'):
        rs=[r for r in records if r['family']==family]
        summary[family]={'attempts':len(rs),'outcomes':{k:sum(r['outcome']==k for r in rs) for k in sorted({r['outcome'] for r in rs})},
                         'search_seconds_total':sum(r['search_seconds'] for r in rs),
                         'replay_seconds_total':sum(r.get('replay_seconds',0) for r in rs)}
    (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))
if __name__=='__main__':main()
