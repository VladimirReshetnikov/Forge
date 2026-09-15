#!/usr/bin/env python3
"""Reproduce synthetic algorithm experiments; NOT a benchmark against Lean/grind."""
from __future__ import annotations
import csv,json,platform,sys,time
from collections import Counter
from fractions import Fraction as Q
from math import gcd
from pathlib import Path
from random import Random
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'prototype'))
import sympy as sp
import scipy,numpy
from forge_cert import poly,polynomial_search as ps,induction as ind,cdclt as sat,witness as wit

ROWS=[];ARTIFACTS=[]
def timed(f):
    start=time.perf_counter();value=f()
    return value,1000*(time.perf_counter()-start)
def record(family,name,status,search_ms,check_ms,artifact=None,**stats):
    data={'family':family,'id':name,'status':status,
          'search_ms':round(search_ms,6),'check_ms':round(check_ms,6),
          'certificate_bytes':0 if artifact is None else len(json.dumps(artifact,sort_keys=True).encode()),
          **stats}
    ROWS.append(data)
    if artifact is not None:ARTIFACTS.append({'family':family,'id':name,**artifact})

def main():
    rng=Random(20260914)
    x,y,z=sp.symbols('x y z')
    cases=[('amgm',x*x+y*y-2*x*y,(x,y),[],[],2),
      ('quartic',x**4+y**4-2*x*x*y*y,(x,y),[],[],4),
      ('cyclic',x*x+y*y+z*z-x*y-y*z-z*x,(x,y,z),[],[],2),
      ('box',x-x*x,(x,),[x,1-x],[],2),
      ('simplex',x*x+y*y-sp.Rational(1,2),(x,y),[],[x+y-1],2),
      ('upper_product',x-x*y,(x,y),[x,y,1-x,1-y],[],2),
      ('zero',sp.Integer(0),(x,),[],[],2),
      ('false_indefinite',x*x-y*y,(x,y),[],[],6),
      ('motzkin',x**4*y*y+x*x*y**4+1-3*x*x*y*y,(x,y),[],[],6)]
    # Favorable-by-construction family from the very same finite certificate cone.
    mons=[sp.Integer(1),x,y,x*x,x*y,y*y]
    for i in range(40):
        p=sum(sp.Rational(rng.randrange(1,8),rng.randrange(1,5)) *
              (rng.choice(mons)+rng.choice([-1,1])*rng.choice(mons))**2 for _ in range(3))
        cases.append((f'manufactured_{i:02}',sp.expand(p),(x,y),[],[],4))
    for name,p,xs,gs,hs,d in cases:
        (cert,stats),ms=timed(lambda:ps.cone_search(p,xs,gs,hs,d))
        target=ps.sparse(p,xs);gg=[ps.sparse(g,xs) for g in gs];hh=[ps.sparse(h,xs) for h in hs]
        artifact=None;check_ms=0
        if cert is not None:
            ok,check_ms=timed(lambda:poly.verify_cone(target,gg,hh,cert,len(xs)));assert ok
            artifact={'n':len(xs),'target':poly.encode(target),'inequalities':list(map(poly.encode,gg)),
                      'equalities':list(map(poly.encode,hh)),'certificate':cert}
        record('cone',name,'proved' if cert is not None else 'unknown',ms,check_ms,artifact,**stats)
    for i in range(40):
        p=sp.Rational(1,rng.randrange(1,8))
        for _ in range(4):
            form=sum(rng.randrange(-4,5)*v for v in (sp.Integer(1),x,y,z))
            p+=sp.Rational(rng.randrange(1,8),rng.randrange(1,8))*form**2
        cert,ms=timed(lambda:ps.quadratic_search(p,(x,y,z)));assert cert is not None
        target=ps.sparse(p,(x,y,z))
        ok,cm=timed(lambda:poly.verify_cone(target,[],[],cert,3));assert ok
        record('quadratic',f'rational_{i:02}','proved',ms,cm,
               {'n':3,'target':poly.encode(target),'inequalities':[],'equalities':[],'certificate':cert},
               support=len(cert['nonnegative']))
    bc=[('near_zero',(x-sp.Rational(1,3))**2+sp.Rational(1,10000),(x,),[(0,1)],12),
        ('non_dyadic_zero',(x-sp.Rational(1,3))**2,(x,),[(0,1)],10),
        ('two_dimensions',(x-sp.Rational(1,3))**2+(y-sp.Rational(2,3))**2+sp.Rational(1,100),
            (x,y),[(0,1),(0,1)],12)]
    for i in range(10):
        center=sp.Rational(rng.randrange(1,16),17)
        eps=sp.Rational(1,10**rng.randrange(1,6))
        bc.append((f'positive_{i:02}',(x-center)**2+eps,(x,),[(0,1)],14))
    for name,p,xs,box,depth in bc:
        (cert,stats),ms=timed(lambda:ps.bernstein_search(p,xs,box,max_depth=depth))
        target=ps.sparse(p,xs);box=[(Q(a),Q(b)) for a,b in box];cm=0;artifact=None
        if cert is not None:
            ok,cm=timed(lambda:poly.verify_bernstein(target,box,cert,len(xs)));assert ok
            artifact={'n':len(xs),'target':poly.encode(target),
                      'box':[[str(a),str(b)] for a,b in box],'certificate':cert}
        record('bernstein',name,'proved' if cert is not None else 'unknown',ms,cm,artifact,**stats)
    (lemmas,recs),ms=timed(ind.synthesize_lemmas)
    ok,cm=timed(lambda:ind.verify_bundle(recs));assert ok
    for name,l,r in [('qrev_correct',ind.F('qrev',ind.x,ind.a),ind.F('app',ind.F('rev',ind.x),ind.a)),
                     ('rev_involution',ind.F('rev',ind.F('rev',ind.x)),ind.x)]:
        c,sm=timed(lambda:ind.prove(l,r,lemmas));assert c is not None
        item={'name':name,'lhs':ind.serial(l),'rhs':ind.serial(r),'status':'proved','certificate':c}
        ok,cm2=timed(lambda:ind.verify_bundle(recs+[item]));assert ok
        record('induction',name,'proved',sm,cm2,{'records':recs+[item]})
    record('lemma_synthesis','schema_candidates','proved',ms,cm,{'records':recs},
           candidates=len(recs),proved=sum(r['status']=='proved' for r in recs),
           rejected=sum(r['status']=='rejected_by_counterexample' for r in recs))
    for use_lemmas in (False,True):
        for generalize in (False,True):
            c,ms=timed(lambda:ind.prove(ind.F('qrev',ind.x,ind.a),ind.F('app',ind.F('rev',ind.x),ind.a),
                                      lemmas if use_lemmas else [],generalize=generalize))
            record('ablation',f'lemmas_{int(use_lemmas)}_generalize_{int(generalize)}',
                   'proved' if c is not None else 'unknown',ms,0)
    # 300 small problems, up to 6 Boolean/theory atoms: independent exhaustive oracle.
    for i in range(300):
        nodes=3;nv=rng.randrange(2,7)
        atoms={v:(rng.randrange(nodes),rng.randrange(nodes),rng.randrange(-4,5)) for v in range(1,nv+1)}
        cnf=[[rng.choice((-1,1))*rng.randrange(1,nv+1) for _ in range(rng.randrange(1,4))]
             for _ in range(rng.randrange(0,15))]
        r,ms=timed(lambda:sat.solve(cnf,atoms,nodes))
        expected=sat.exhaustive_oracle(cnf,atoms,nodes)
        assert (r['status']=='sat')==expected and r['status']!='unknown'
        checker=sat.verify_sat if expected else sat.verify_unsat
        ok,cm=timed(lambda:checker(cnf,atoms,nodes,r));assert ok
        record('cdclt_random',f'random_{i:03}',r['status'],ms,cm,
               {'cnf':cnf,'atoms':atoms,'nodes':nodes,'result':r},**r['stats'])
    for pigeons in range(2,7):
        cnf=sat.pigeonhole(pigeons,pigeons-1)
        r,ms=timed(lambda:sat.solve(cnf));ok,cm=timed(lambda:sat.verify_unsat(cnf,{},1,r));assert ok
        record('pigeonhole',f'{pigeons}_into_{pigeons-1}','unsat',ms,cm,
               {'cnf':cnf,'atoms':{},'nodes':1,'result':r},**r['stats'])
    for m in range(1,21):
        for aa in range(-3,6):
            for bb in range(6):
                c,ms=timed(lambda:wit.synthesize(aa,bb,m));artifact=None;cm=0
                if c is not None:
                    ok,cm=timed(lambda:wit.verify(aa,bb,m,c));assert ok
                    artifact={'a':aa,'b':bb,'m':m,'certificate':c}
                else:assert bb%gcd(aa,m)!=0
                record('witness',f'a{aa}_b{bb}_m{m}','proved' if c is not None else 'impossible',ms,cm,artifact)
    summary={}
    for fam in sorted({r['family'] for r in ROWS}):
        rr=[r for r in ROWS if r['family']==fam]
        summary[fam]={'total':len(rr),'status':dict(Counter(r['status'] for r in rr)),
                      'search_ms_total':round(sum(r['search_ms'] for r in rr),3),
                      'check_ms_total':round(sum(r['check_ms'] for r in rr),3),
                      'artifact_bytes_total':sum(r['certificate_bytes'] for r in rr)}
    env={'python':platform.python_version(),'platform':platform.platform(),
         'sympy':sp.__version__,'scipy':scipy.__version__,'numpy':numpy.__version__,
         'seed':20260914,'lean_executed':False,
         'benchmark_scope':'Synthetic algorithm experiments, NOT a Lean or grind comparison.',
         'timing_note':'One in-process pass; no repeated timing trials. Search includes internal acceptance check; replay is timed separately. Not robust comparative performance evidence.'}
    (ROOT/'results').mkdir(exist_ok=True)
    (ROOT/'results'/'experiments.json').write_text(json.dumps({'environment':env,'summary':summary,'rows':ROWS},indent=2)+'\n')
    (ROOT/'results'/'certificates.json').write_text(json.dumps(ARTIFACTS,indent=2)+'\n')
    keys=['family','id','status','search_ms','check_ms','certificate_bytes']
    with (ROOT/'results'/'experiments.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=keys,extrasaction='ignore');w.writeheader();w.writerows(ROWS)
    print(json.dumps({'environment':env,'summary':summary,'artifacts':len(ARTIFACTS)},indent=2))
if __name__=='__main__':main()
