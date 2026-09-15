"""Reproduce the controlled Python experiments. No Lean/grind benchmark is run."""
from __future__ import annotations
from dataclasses import asdict
from fractions import Fraction as Q
from pathlib import Path
from time import perf_counter
import csv, json, platform, sys
import numpy, scipy, sympy, pytest
from poly import Poly
import cone, bernstein, invariant, horn

OUT=Path(__file__).resolve().parents[1]/'results'
OUT.mkdir(exist_ok=True)

def dump(name,obj):
    (OUT/name).write_text(json.dumps(obj,indent=2)+'\n')

def csvwrite(name, rows):
    with (OUT/name).open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0])); w.writeheader(); w.writerows(rows)

def timed(call):
    start=perf_counter(); value=call(); return value,perf_counter()-start

# Imports are not included in timings. A warmup absorbs the initial HiGHS start.
x,y=Poly.var(2,0),Poly.var(2,1)
cone.search(x*x,degree=2)
problems=[]
for a in range(1,6):
    for b in range(1,6):
        problems.append((f'product_{a}_{b}','products',x*y-a*b,(x-a,y-b),()))
for a in range(1,6):
    for b in range(3):
        problems.append((f'square_{a}_{b}','squares',a*(x-y)**2+b*x*x,(),()))
x3,y3,u=[Poly.var(3,j) for j in range(3)]
for q in (Q(1,3),Q(2,5),Q(1,2),Q(3,4),Q(1),Q(5,4)):
    problems.append((f'mixed_{q}','mixed',Poly.const(3,-1),(u-q,),(x3+y3-1,u-x3*y3)))
for a in range(1,4):
    for b in range(1,4):
        problems.append((f'diagonal_{a}_{b}','diagonal',a*x*x+b*y*y,(),()))
for a in range(1,6):
    problems.append((f'equality_{a}','equalities',(a*x+y+1)*(x+y-1),(),(x+y-1,)))
rows=[]
for name,family,p,ge,eq in problems:
    for variant,binomials,depth in [('sparse',False,1),('enriched',True,2)]:
        cert,seconds=timed(lambda:cone.search(p,ge,eq,degree=2,binomials=binomials,product_depth=depth))
        valid,checking=(timed(lambda:cone.replay(p,ge,eq,cert)) if cert else (False,0.0))
        if cert and not valid: raise AssertionError(name)
        rows.append(dict(problem=name,family=family,variant=variant,status='PROVED' if valid else 'UNKNOWN',
                         search_seconds=seconds,replay_seconds=checking,
                         positive_atoms=len(cert.positive) if cert else 0,
                         equality_multipliers=len(cert.equalities) if cert else 0))
        if name=='mixed_1/3' and variant=='enriched':
            dump('mixed_certificate.json', {'target':p.to_json(),'ge':[q.to_json() for q in ge],
                    'eq':[q.to_json() for q in eq], 'certificate':cert.to_json()})
csvwrite('cone.csv',rows)
cone_summary={v:{'proved':sum(r['status']=='PROVED' for r in rows if r['variant']==v),
                 'total':len(problems),
                 'search_seconds':sum(r['search_seconds'] for r in rows if r['variant']==v),
                 'replay_seconds':sum(r['replay_seconds'] for r in rows if r['variant']==v)}
              for v in ('sparse','enriched')}

# Strictly positive benchmarks; unsplit and subdivided certificate search.
x=Poly.var(1,0); box=((Q(0),Q(1)),); brows=[]
for k in range(1,7):
    for d in (10,100,1000):
        p=(x-Q(k,7))**2+Q(1,d)
        unsplit=bernstein.search(p,box,strict=True,max_depth=0)
        result,seconds=timed(lambda:bernstein.search(p,box,strict=True,max_depth=12))
        valid,checking=timed(lambda:bernstein.replay(p,box,result.tree,strict=True))
        assert result.status=='PROVED' and valid
        nodes,leaves=bernstein.size(result.tree)
        brows.append(dict(problem=f'quadratic_{k}_7_eps_1_{d}',
                          unsplit=unsplit.status,subdivided=result.status,
                          nodes=nodes,leaves=leaves,search_seconds=seconds,replay_seconds=checking))
        if k==2 and d==100:
            dump('bernstein_certificate.json',{'polynomial':p.to_json(),'box':[['0','1']],
                 'strict':True,'tree':bernstein.tree_json(result.tree)})
# Additional positive two-variable domain examples.
x,y=Poly.var(2,0),Poly.var(2,1)
for d in (10,100,1000):
    p=(x-Q(2,7))**2+(y-Q(3,7))**2+Q(1,d); box2=((Q(0),Q(1)),)*2
    unsplit=bernstein.search(p,box2,strict=True,max_depth=0)
    result,seconds=timed(lambda:bernstein.search(p,box2,strict=True,max_depth=18))
    valid,checking=timed(lambda:bernstein.replay(p,box2,result.tree,strict=True))
    assert result.status=='PROVED' and valid
    nodes,leaves=bernstein.size(result.tree)
    brows.append(dict(problem=f'bivariate_eps_1_{d}',unsplit=unsplit.status,subdivided=result.status,
                      nodes=nodes,leaves=leaves,search_seconds=seconds,replay_seconds=checking))
csvwrite('bernstein.csv',brows)
bern_summary={'total':len(brows),'unsplit_proved':sum(r['unsplit']=='PROVED' for r in brows),
              'subdivided_proved':len(brows),'min_leaves':min(r['leaves'] for r in brows),
              'max_leaves':max(r['leaves'] for r in brows),
              'search_seconds':sum(r['search_seconds'] for r in brows),
              'replay_seconds':sum(r['replay_seconds'] for r in brows)}

# Induction coefficient synthesis and replay of universal base/step identities.
irows=[]
for w in range(-5,6):
    for c in range(-5,6):
        cert,seconds=timed(lambda:invariant.search(Q(1),Q(w),Q(c)))
        valid,checking=timed(lambda:invariant.replay(Q(1),Q(w),Q(c),cert))
        assert valid
        irows.append(dict(w=w,c=c,A=str(cert.A),B=str(cert.B),C=str(cert.C),D=str(cert.D),
                          search_seconds=seconds,replay_seconds=checking))
csvwrite('invariants.csv',irows)
inv_summary={'proved':len(irows),'total':len(irows),
             'search_seconds':sum(r['search_seconds'] for r in irows),
             'replay_seconds':sum(r['replay_seconds'] for r in irows),
             'out_of_template_unknown':sum(invariant.search(Q(r),Q(2),Q(1)) is None for r in (-2,-1,0,2,3))}

# Explicitly noisy finite ground Horn workloads. Count early-goal baseline too.
hrows=[]
for noise in (10,100,1000):
    useful=tuple(horn.Rule(f'u{k+1}',(f'u{k}',)) for k in range(12))
    unrelated=tuple(horn.Rule(f'n{j}_{k+1}',(f'n{j}_{k}',)) for j in range(noise) for k in range(24))
    rules=useful+unrelated; facts=('u0',)+tuple(f'n{j}_0' for j in range(noise)); goal='u12'
    prog,index_seconds=timed(lambda:horn.Program(rules))
    for variant,demand,early in [('full_closure',False,False),('early_goal',False,True),('demand',True,True)]:
        result=prog.solve(facts,goal,demand=demand,stop_at_goal=early)
        assert result.proved and horn.replay(rules,facts,goal,result.proof)
        minimized=horn.minimize(rules,facts,goal,result.proof)
        hrows.append(dict(noise_chains=noise,variant=variant,total_rules=len(rules),
                          selected_rules=result.selected_rules,firings=result.firings,
                          index_seconds=index_seconds,query_seconds=result.seconds,
                          cold_total_seconds=index_seconds+result.seconds,
                          original_proof_steps=len(result.proof.steps),minimized_steps=len(minimized.steps)))
csvwrite('horn.csv',hrows)

summary={'scope':'Python algorithm experiments only; no Lean compiler and no grind execution',
         'cone':cone_summary,'bernstein':bern_summary,'invariants':inv_summary,'horn':hrows,
         'tests':'See pytest.txt for the actual separate pytest run.'}
dump('summary.json',summary)
dump('environment.json',{'python':sys.version,'platform':platform.platform(),
     'numpy':numpy.__version__,'scipy':scipy.__version__,'sympy':sympy.__version__,
     'pytest':pytest.__version__,'lean':'not installed; no Lean tests executed',
     'reported_timings':'single warm runs; imports excluded; environment-specific, not significance estimates'})
print(json.dumps(summary,indent=2))
