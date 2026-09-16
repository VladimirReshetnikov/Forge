#!/usr/bin/env python3
"""Deterministic research experiments. Writes NEW results, never recorded evidence.

No symbolic/numerical libraries are needed; oracle checks live in oracle_checks.py.
Every record names its unit. Timings are descriptive Python wall times only.
"""
from __future__ import annotations
import argparse, copy, csv, json, platform, random, sys, time
from pathlib import Path
from fractions import Fraction as Q
from math import factorial
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'prototype'))
from forge_analytic import algebra as A, jets as J, ladders as L, tails as T
from forge_analytic.checker import verify, loads


def analytic_cases():
    """48 scaling cases + 8 products + 6 high-order exponential remainders."""
    for a in (Q(1,4), Q(1,2), Q(1), Q(2)):
        for radius in (Q(1,4), Q(1,2), Q(3,4)):
            b = radius/a
            for name, expr in (
                ('exp', J.minus(J.atom('exp', a), J.P(1,a))),
                ('sin', J.minus(J.P(0,a), J.atom('sin', a))),
                ('log1p', J.minus(J.P(0,a), J.atom('log1p', a))),
                ('atan', J.minus(J.P(0,a), J.atom('atan', a))),
            ):
                yield f'{name}_a{a}_r{radius}', expr, b, 'scaled elementary gap'
    for k in range(8):
        a = Q(k+1,4)
        f = J.minus(J.atom('exp',a), J.P(1,a))
        g = J.minus(J.P(0,a), J.atom('sin',a))
        yield f'product_{k}', J.times(f,g), Q(1,4)/a, 'product of two elementary gaps'
    for r in range(2,8):
        p = J.P(*(Q(1,factorial(k)) for k in range(r)))
        yield f'exp_remainder_{r}', J.minus(J.atom('exp'),p), Q(1,2), 'higher-order exponential gap'


def ladder_cases(rng):
    yield 'exp_linear', {Q(1): A.poly([1]), Q(0): A.poly([-1,-1])}, 'hand example'
    for k in range(2,8):
        yield f'exp_taylor_{k}', {Q(1):A.poly([1]), Q(0):A.poly(-Q(1,factorial(i)) for i in range(k))}, 'hand Taylor family'
    for i in range(36):
        rates = (Q(-1), Q(0), Q(1), Q(2))
        g = {rng.choice(rates): A.poly([rng.randint(1,4),rng.randint(0,3),rng.randint(0,2)])}
        for _ in range(1+i%4):
            g = L.lift(g, rng.choice(rates), Q(rng.randint(0,3)))
        yield f'planted_{i}',g,'planted integrating-factor chain'


def tail_cases(rng):
    for i in range(120):
        na = rng.randint(0,4)
        d = (-2,-1,0,1,2,3,4,5)[i%8]
        nd = max(0,na+d)
        a = A.poly([rng.randint(-4,4) for _ in range(na)]+[rng.randint(1,4)])
        den = A.poly([rng.randint(-4,4) for _ in range(nd)]+[rng.randint(1,4)])
        yield f'rational_{i}', a, den


def run(out:Path):
    out.mkdir(parents=True,exist_ok=False)
    rng = random.Random(20260915)
    problems,certs,rows,mutations,controls = {},{},{},[],[]
    rows=[]
    counters = {'anchored':0,'unanchored_same_order':0,'ladder':0,'barrier':0,'divergence':0,
                'mutation_rejections':0,'finite_tail_comparisons':0,'modulus_checks':0,
                'harmonic_comparisons':0,'optimized_barriers':0}
    failures=[]
    def store(id,cert,description,elapsed):
        assert id not in problems
        assert verify(cert['subject'],cert), ('certificate rejected',id,cert)
        problems[id]={'subject':cert['subject'],'description':description,'expected_kind':cert['kind']}
        certs[id]=cert
        rows.append({'id':id,'kind':cert['kind'],'description':description,
                     'search_seconds':format(elapsed,'.9f'),'certificate_bytes':len(json.dumps(cert)),
                     'order_or_depth':cert.get('order',len(cert.get('rates',[]))),
                     'cutoff':cert.get('cutoff','')})
        counters[cert['kind']]+=1
    try:
        for id,expr,b,desc in analytic_cases():
            begin=time.perf_counter(); c=J.search(expr,b,max_order=24)
            assert c is not None, ('analytic search unknown',id)
            store('jet/'+id,c,desc,time.perf_counter()-begin)
            lower=J.unanchored_lower(expr,b,c['order'])
            rows[-1]['unanchored_lower']=A.text(lower)
            if lower>=0: counters['unanchored_same_order']+=1
        for id,f,desc in ladder_cases(rng):
            begin=time.perf_counter();c=L.search(f,max_depth=12,max_nodes=4000)
            assert c is not None, ('ladder search unknown',id)
            store('ladder/'+id,c,desc,time.perf_counter()-begin)
        for id,a,den in tail_cases(rng):
            begin=time.perf_counter();c=T.synthesize(a,den)
            store('tail/'+id,c,'unplanted positive-leading rational function',time.perf_counter()-begin)
            N=c['cutoff']
            if c['kind']=='barrier':
                C,sh,p=Q(c['constant']),c['shift'],c['power']
                total=Q(0)
                for j in range(80):
                    n=N+j;term=A.evaluate(a,n)/A.evaluate(den,n)
                    total+=term
                    assert 0<=total<=C/Q(N+sh)**p-C/Q(n+1+sh)**p
                    counters['finite_tail_comparisons']+=1
                for eps in (Q(1,10),Q(1,1000),Q(7,19),Q(9,2)):
                    k=T.modulus(c,eps)
                    assert k>=N and C/Q(k+sh)**p<eps
                    counters['modulus_checks']+=1
            else:
                for j in range(40):
                    n=N+j
                    assert A.evaluate(a,n)/A.evaluate(den,n)>=Q(c['minorant'])/n
                    counters['harmonic_comparisons']+=1
        for p in range(2,9):
            for N in (2,5,10):
                a,den=A.poly([1]),A.poly([0]*p+[1])
                begin=time.perf_counter();c=T.optimized_barrier(a,den,N)
                assert c is not None
                store(f'optimized/p{p}_N{N}',c,'exact one-variable coefficient optimization',time.perf_counter()-begin)
                counters['optimized_barriers']+=1
        # Deliberately false candidates or true statements outside these lanes.
        bads=[('false_exp',J.minus(J.P(1,1),J.atom('exp')),Q(1,2)),
              ('false_sin',J.minus(J.atom('sin'),J.P(0,1)),Q(1,2)),
              ('false_log',J.minus(J.atom('log1p'),J.P(0,1)),Q(1,2)),
              ('false_atan',J.minus(J.atom('atan'),J.P(0,1)),Q(1,2)),
              ('log_domain',J.atom('log1p',-1),Q(2)),
              ('true_trig_identity',J.minus(J.plus(J.times(J.atom('sin'),J.atom('sin')),J.times(J.atom('cos'),J.atom('cos'))),J.P(1)),Q(1,2))]
        for id,e,b in bads:
            c=J.search(e,b,max_order=14)
            assert c is None, ('control unexpectedly admitted',id)
            controls.append({'id':id,'outcome':'unknown','order_cap':14})
        square={Q(2):A.poly([1]),Q(1):A.poly([-4]),Q(0):A.poly([4])}
        assert L.search(square,max_depth=8,max_nodes=4000) is None
        controls.append({'id':'true_even_root_global_square','outcome':'unknown','depth_cap':8})
        # Mutations are all evidence-bearing fields, not harmless metadata.
        for id,cert in certs.items():
            s=problems[id]['subject']
            for change in range(3):
                m=copy.deepcopy(cert)
                kind=m['kind']
                if change==0:
                    m['subject']=dict(m['subject'],forged=True)
                elif change==1:
                    key={'anchored':'margin','ladder':'seeds','barrier':'tail_bound','divergence':'minorant'}[kind]
                    if kind=='ladder':m[key][0]=A.text(Q(m[key][0])+1)
                    elif kind=='divergence':m[key]='0/1'
                    else:m[key]=A.text(Q(m[key])+1)
                else:
                    key={'anchored':'polynomial','ladder':'stages','barrier':'shifted_residual','divergence':'shifted_residual'}[kind]
                    if kind=='ladder':
                        m['stages'][0]=[] if m['stages'][0] else [['0/1',['1/1']]]
                    else:
                        m[key][0]=A.text(Q(m[key][0])+1)
                accepted=verify(s,m)
                mutations.append({'id':id,'mutation':change,'accepted':accepted})
                assert not accepted, ('mutation admitted',id,change)
                counters['mutation_rejections']+=1
        for data in ('{"a":1,"a":2}','{"a":NaN}','{"a":0.1}','[]'):
            try:loads(data)
            except ValueError: pass
            else:raise AssertionError(('malformed JSON accepted',data))
        summary={'seed':20260915,'python':sys.version,'platform':platform.platform(),
                 'counters':counters,'controls':controls,'certificate_records':len(certs),
                 'lean_status':'NOT_RUN: no Lean executable available',
                 'scope':'Synthetic component experiments; no Lean tactic or LeanCert comparison',
                 'failures':failures}
        for name,obj in [('problems.json',problems),('certificates.json',certs),('mutations.json',mutations),('summary.json',summary)]:
            (out/name).write_text(json.dumps(obj,indent=2)+'\n')
        columns=['id','kind','description','search_seconds','certificate_bytes','order_or_depth','cutoff','unanchored_lower']
        with (out/'measurements.csv').open('w',newline='') as f:
            writer=csv.DictWriter(f,fieldnames=columns);writer.writeheader();writer.writerows(rows)
        print(json.dumps(summary,indent=2))
    except Exception as exc:
        import traceback
        failure={'exception':repr(exc),'traceback':traceback.format_exc(),'partial_counters':counters}
        (out/'FAILED-RUN.json').write_text(json.dumps(failure,indent=2)+'\n')
        raise

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,default=ROOT/'reproduced-results')
    run(p.parse_args().output)
