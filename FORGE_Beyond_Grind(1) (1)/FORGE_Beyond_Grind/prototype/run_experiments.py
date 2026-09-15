#!/usr/bin/env python3
"""Reproduce deterministic component experiments; NOT a Lean/grind benchmark."""
from __future__ import annotations
import argparse,csv,json,platform,random,statistics,time
from fractions import Fraction as Q
from pathlib import Path
import scipy,numpy,sympy,pytest
from forge.poly import Poly
from forge.certificates import *
from forge.search import quadratic_sos,cone_search,bernstein_search
from forge.synthesis import *
from forge.univariate import *


def variables(n): return [Poly.var(n,i) for i in range(n)]


def cases():
    for seed in range(60):
        rng=random.Random(seed); n=1+seed%5; xs=variables(n); p=Poly.const(n,0)
        for _ in range(1+seed%7):
            q=Poly.const(n,Q(rng.randrange(-6,7),rng.randrange(1,5)))
            for x in xs: q+=Q(rng.randrange(-5,6),rng.randrange(1,5))*x
            p+=Q(rng.randrange(1,8),rng.randrange(1,4))*q*q
        yield {'id':f'quadratic_{seed:02}', 'family':'Quadratic SOS', 'p':p,
               'search':lambda p=p:quadratic_sos(p),
               'check':lambda c,p=p:check_cone(p,[],[],c), 'encode':cone_json,
               'ablation':lambda p=p:all(c>=0 and all(e%2==0 for e in ex) for ex,c in p.terms),
               'ablation_label':'expanded monomial squares only', 'input':{'p':p.json()}}
    x,y=variables(2); one=Poly.const(2,1)
    candidates=[ConeTerm(Q(1),q,()) for q in [one,x,y,x*y,x+y,x-y,x*x-y*y]]
    simple=candidates[:4]
    for seed in range(16):
        rng=random.Random(seed)
        p=sum((rng.randrange(1,6)*c.square**2 for c in candidates),Poly.const(2,0))
        yield {'id':f'cone_{seed:02}', 'family':'Finite cone LP', 'p':p,
               'search':lambda p=p:cone_search(p,[],candidates),
               'check':lambda c,p=p:check_cone(p,[],[],c),'encode':cone_json,
               'ablation':lambda p=p:cone_search(p,[],simple) is not None,
               'ablation_label':'monomial square candidates only',
               'input':{'p':p.json(),'squares':[c.square.json() for c in candidates]}}
    gs=[x,1-x,y,1-y]
    from itertools import product
    cs=[ConeTerm(Q(1),one,e) for e in product(range(3),repeat=4) if sum(e)<=2]
    p=2*x*(1-x)+3*y*(1-y)+x*y+Q(1,5)
    yield {'id':'cone_box_products','family':'Finite cone LP','p':p,
           'search':lambda:cone_search(p,gs,cs), 'check':lambda c:check_cone(p,gs,[],c),
           'encode':cone_json,'ablation':lambda:cone_search(p,[],simple) is not None,
           'ablation_label':'without hypothesis products',
           'input':{'p':p.json(),'inequalities':[g.json() for g in gs],'powers':[c.powers for c in cs]}}
    x=variables(1)[0]
    for center in [Q(-2,3),Q(-1,3),Q(0),Q(1,3),Q(2,3)]:
        for eps in [Q(1,4),Q(1,16),Q(1,64)]:
            p=(x-center)**2+eps;box=((Q(-1),Q(1)),)
            yield box_case(f'box_{center}_{eps}',p,box)
    x,y=variables(2); p=x**4*y**2+x**2*y**4-3*x*x*y*y+1+Q(1,16)
    for bound in [1,2,3]:
        yield box_case(f'motzkin_box_{bound}',p,((Q(-bound),Q(bound)),)*2)
    n=variables(1)[0]
    for power in range(9):
        yield recurrence_case(f'power_sum_{power}',n**power,Poly.const(1,0),power+1)
    for seed in range(24):
        rng=random.Random(seed); n,a=variables(2)
        step=sum((Q(rng.randrange(-4,5),rng.randrange(1,4))*n**j*a**(j%2)
                  for j in range(seed%4+1)),Poly.const(2,0))
        yield recurrence_case(f'parametric_recurrence_{seed:02}',step,a+seed,6)
    for seed in range(40):
        rng=random.Random(seed); k,p=1+seed%4,1+seed%3
        a=[[(1 if i==j else rng.randrange(-3,4) if i<j else 0) for j in range(k)] for i in range(k)]
        w=[[rng.randrange(-5,6) for _ in range(p)] for _ in range(k)]
        d=[rng.randrange(-5,6) for _ in range(k)]
        b=[[sum(a[i][j]*w[j][t] for j in range(k)) for t in range(p)] for i in range(k)]
        c=[sum(a[i][j]*d[j] for j in range(k)) for i in range(k)]
        yield {'id':f'affine_{seed:02}','family':'Integral affine witness',
               'search':lambda a=a,b=b,c=c:synthesize_affine_witness(a,b,c,True),
               'check':lambda cert,a=a,b=b,c=c:check_affine_witness(a,b,c,cert,True),
               'encode':lambda z:{'linear':[[str(v) for v in r] for r in z.linear],
                                  'offset':[str(v) for v in z.offset]},
               'input':{'A':a,'B':b,'c':c,'require_integral':True}}
    x=variables(1)[0]
    for seed in range(30):
        q=(x-Q(seed-15,21))**(1+seed%3)
        if seed%2:q*=x*x-2
        p=q*q*(x*x+Q(seed+1,7))*(x+2)*(2-x)
        yield {'id':f'univariate_zero_{seed:02}','family':'Univariate with zeros','p':p,
               'search':lambda p=p:univariate_search(p,Q(-2),Q(2)),
               'check':lambda c,p=p:check_univariate(p,Q(-2),Q(2),c),'encode':univariate_json,
               'ablation':lambda p=p:bernstein_search(p,((Q(-2),Q(2)),),max_depth=12) is not None,
               'ablation_label':'dyadic Bernstein depth 12, without factorization',
               'input':{'p':p.json(),'interval':['-2','2']}}


def box_case(name,p,box):
    return {'id':name,'family':'Bernstein box','p':p,
            'search':lambda:bernstein_search(p,box,max_depth=14),
            'check':lambda c:check_bernstein(p,box,c),'encode':tree_json,
            'ablation':lambda:bernstein_search(p,box,max_depth=0) is not None,
            'ablation_label':'no subdivision','input':{'p':p.json(),'box':[[str(l),str(u)] for l,u in box]}}


def recurrence_case(name,step,initial,bound):
    return {'id':name,'family':'Polynomial recurrence',
            'search':lambda:synthesize_recurrence(step,initial,max_degree=bound),
            'check':lambda c:check_recurrence(step,initial,c),'encode':lambda p:p.json(),
            'input':{'step':step.json(),'initial':initial.json(),'max_degree':bound}}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'results')
    parser.add_argument('--repeats',type=int,default=3)
    args=parser.parse_args()
    if args.repeats<1:parser.error('--repeats must be positive')
    args.output.mkdir(parents=True,exist_ok=True)
    # Warm up imported native numerical code, outside reported timings.
    scipy.optimize.linprog([1.],A_eq=[[1.]],b_eq=[1.],bounds=(0,None),method='highs')
    records=[]; certificates=[]
    # Avoid late-binding changes to generator locals: do not materialize the generator.
    # Each case is executed immediately while the generator is suspended.
    for case in cases():
        times=[];checks=[];cert=None
        for _ in range(args.repeats):
            start=time.perf_counter_ns();cert=case['search']();times.append((time.perf_counter_ns()-start)/1e6)
            if cert is not None:
                start=time.perf_counter_ns();ok=case['check'](cert);checks.append((time.perf_counter_ns()-start)/1e6)
                if not ok:raise AssertionError('invalid certificate: '+case['id'])
        row={'id':case['id'],'family':case['family'],'solved':cert is not None,
             'search_median_ms':statistics.median(times),
             'recheck_median_ms':statistics.median(checks) if checks else None,
             'ablation_solved':case['ablation']() if 'ablation' in case else None,
             'ablation':case.get('ablation_label','not run')}
        if case['family']=='Bernstein box' and cert is not None:
            row['leaves'],row['depth']=tree_size(cert)
        encoded=case['encode'](cert) if cert is not None else None
        row['certificate_json_bytes']=len(json.dumps(encoded,separators=(',',':')).encode())
        certificates.append({'id':case['id'],'family':case['family'],'input':case['input'],'certificate':encoded})
        records.append(row)
    families=[]
    for family in dict.fromkeys(r['family'] for r in records):
        rows=[r for r in records if r['family']==family]
        ablated=[r for r in rows if r['ablation_solved'] is not None]
        families.append({'family':family,'instances':len(rows),'solved':sum(r['solved'] for r in rows),
                         'ablation_solved':sum(r['ablation_solved'] for r in ablated) if ablated else None,
                         'search_median_ms':statistics.median(r['search_median_ms'] for r in rows),
                         'recheck_median_ms':statistics.median(r['recheck_median_ms'] for r in rows if r['recheck_median_ms'] is not None)})
    output={'notice':'Python mechanism tests on constructed instances; NO Lean/grind comparison.',
            'repeats':args.repeats,'families':families,'records':records,
            'environment':{'python':platform.python_version(),'platform':platform.platform(),
                           'numpy':numpy.__version__,'scipy':scipy.__version__,'sympy':sympy.__version__,
                           'pytest':pytest.__version__,'lean_executed':False}}
    (args.output/'experiments.json').write_text(json.dumps(output,indent=2)+'\n')
    (args.output/'certificates.json').write_text(json.dumps(certificates,indent=2)+'\n')
    keys=list(dict.fromkeys(k for r in records for k in r))
    with (args.output/'experiments.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=keys);w.writeheader();w.writerows(records)
    print(json.dumps({'families':families,'environment':output['environment']},indent=2))


if __name__=='__main__':main()
