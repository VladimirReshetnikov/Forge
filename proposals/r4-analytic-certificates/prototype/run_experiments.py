#!/usr/bin/env python3
"""Reproducible experiments. Writes to reproduced-results, never recorded results."""
import argparse, json, platform, sys, time
from pathlib import Path
from fractions import Fraction as Q
from random import Random
from itertools import permutations
from collections import Counter
from forge_analytic.core import *
from forge_analytic.search import *
from forge_analytic.check import verify, verify_goal


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--output',type=Path,default=Path('../reproduced-results'))
    args=ap.parse_args(); args.output.mkdir(parents=True,exist_ok=True)
    problems, receipts, rows, misses = {}, [], [], []
    def retain(name,a,goal,c,category):
        assert c is not None, name
        problem={'polynomial':encode(a),'goal':goal}
        assert verify_goal(problem,c),name
        problems[name]=problem
        receipts.append({'problem_id':name,'certificate':c})
        row={'id':name,'category':category,'kind':c['kind'],
             'steps':len(c.get('steps',[])),'bytes':len(json.dumps(c,separators=(',',':')))}
        if c['kind']=='tail-v1': row['cutoff']=c['cutoff']; row['sign']=c['sign']
        if c['kind']=='ladder-v1': row['anchor']=c['anchor']
        if c['kind']=='cover-v1':
            def leaves(t): return 1 if 'leaf' in t else leaves(t['left'])+leaves(t['right'])
            row['leaves']=leaves(c['tree'])
        rows.append(row)
    start=time.perf_counter()
    for n in range(25):
        a=taylor_remainder(n)
        retain('taylor_%02d'%n,a,{'kind':'positive_open_ray','anchor':'0'},ladder(a),'boundary-zero')
    named={
        'exp_tangent_negative_ray': reflect(taylor_remainder(1)),
        'cosh_quadratic':make((1,0,1),(-1,0,1),(0,0,-2),(0,2,-1)),
        'sinh_cubic':make((1,0,1),(-1,0,-1),(0,1,-2),(0,3,'-1/3')),
        'entropy_positive_chart':make((1,1,1),(1,0,-1),(0,0,1)),
        'entropy_negative_chart':reflect(make((1,1,1),(1,0,-1),(0,0,1))),
        'log_lower_rational_chart':make((1,1,1),(1,0,-2),(0,1,1),(0,0,2)),
        'log_sqrt_upper_chart':make(('1/2',0,1),('-1/2',0,-1),(0,1,-1)),
        'damped_positive_square':make((0,0,1),(-1,0,-2),(-2,0,1)),
    }
    for name,a in named.items():
        retain(name,a,{'kind':'positive_open_ray','anchor':'0'},ladder(a),'named')
    ghost_rows=[]
    for eps in [Q(1),Q(1,2),Q(1,4),Q(1,16)]:
        a=make((2,0,1),(1,0,-4),(0,0,4+eps))
        name='ghost_eps_'+str(eps).replace('/','_')
        assert ladder(a) is None
        c=ghost_search(a,max_extra=96)
        retain(name,a,{'kind':'positive_closed_ray','anchor':'0'},c,'auxiliary-factors')
        ghost_rows.append({'epsilon':str(eps),'native':'unknown','extra_factors':len(c['steps'])-3,
                           'beta':c['steps'][0]['rho'],'total_factors':len(c['steps'])})
        cc=compact_cover(a,0,2,max_depth=14)
        retain('cover_'+name,a,{'kind':'nonnegative_interval','domain':['0','2']},cc,'compact-cover')
    a=make((2,0,1),(1,0,-4),(0,0,4))
    assert ghost_search(a,max_extra=96) is None
    misses.append({'id':'interior_zero','outcome':'unknown','reason':'bounded ghost search; mathematical obstruction proved in article'})
    a=taylor_remainder(1)
    assert compact_cover(a,0,1,max_depth=14) is None
    misses.append({'id':'interval_at_boundary_zero','outcome':'unknown','max_depth':14})
    rng=Random(20260915)
    for i in range(240):
        a=make(*[(Q(rng.randrange(-9,10),3),rng.randrange(6),rng.randrange(-9,10)) for _ in range(8)])
        c=tail(a)
        retain('tail_%03d'%i,a,{'kind':'eventual_sign','sign':c['sign']},c,'random-eventual-sign')
    a=make((1,0,1),(0,5,-1000))
    retain('growth_tail',a,{'kind':'eventual_sign','sign':1},tail(a),'growth-witness')
    tried=[]
    for anchor in [0]+[2**k for k in range(25)]:
        c=ladder(a,anchor=anchor,bits=128,order=48)
        tried.append({'anchor':anchor,'accepted':c is not None})
        if c is not None: break
    retain('growth_sharp_anchor',a,{'kind':'positive_closed_ray','anchor':str(anchor)},c,'growth-witness')
    a=make((1,0,1),(0,0,-2))
    c=compact_cover(a,0,1)
    retain('false_exp_ge_two',a,{'kind':'counterexample_interval','domain':['0','1']},c,'counterexample')
    # Order completeness ablation: compare a canonical path against every order.
    ablation=[]
    for i in range(200):
        a=make(*[(r,k,rng.randrange(-5,6)) for r in [-2,1,3] for k in [0,1]])
        fs=spectrum(a); orders=set(permutations(fs))
        canonical=ladder(a) is not None
        accepted=sum(ladder(a,factors=p) is not None for p in orders)
        assert canonical==(accepted>0)
        ablation.append({'case':i,'distinct_orders':len(orders),
                         'accepted_orders':accepted,'canonical_accepted':canonical})
    result={'environment':{'python':sys.version,'platform':platform.platform(),
                           'site_packages_disabled':sys.flags.no_site==1},
            'seed':20260915,'recorded_certificates':len(receipts),
            'categories':dict(Counter(r['category'] for r in rows)),
            'all_replayed':True,'ghost_ablation':ghost_rows,'growth_anchor_attempts':tried,
            'order_ablation':{'cases':len(ablation),
                'distinct_orders_checked':sum(r['distinct_orders'] for r in ablation),
                'canonical_acceptances':sum(r['canonical_accepted'] for r in ablation),
                'mismatches':0},'unknown_controls':misses,
            'elapsed_seconds':time.perf_counter()-start,
            'lean_status':'NOT_RUN: no Lean executable installed in execution environment',
            'comparison_with_grind':'NOT_RUN'}
    for name,obj in [('problems.json',problems),('certificates.json',receipts),('experiment-summary.json',result),
                     ('certificate-index.json',rows),('order-ablation.json',ablation)]:
        (args.output/name).write_text(json.dumps(obj,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
