"""Reproducible differential, semantic-mutation, and artifact replay experiments.

Run from any directory: python -S prototype/run_tests.py --output reproduced-results
The finite-state oracles use explicit executions, not predecessor construction.
"""
from __future__ import annotations
import argparse
import copy
import itertools as it
import json
import math
import platform
import random
import subprocess
import sys
import time
from collections import deque
from pathlib import Path
import checker as ck
import search as pr

SEED = 941572603
ROOT = Path(__file__).resolve().parents[1]

def dump(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, sort_keys=True, indent=2) + '\n')

def S(q, *xs):
    return {'q': q, 'v': list(xs)}

def R(q, target, a, A, b):
    return {'source': q, 'target': target, 'consume': a, 'matrix': A, 'produce': b}

def C(q, target, op, letter='', channel=0):
    return {'source': q, 'target': target, 'op': op, 'channel': channel, 'symbol': letter}

def resource(d, controls, ts, bad):
    return dict(kind='resource', dimension=d, controls=controls, transitions=ts, bad=bad)

def lossy(k, controls, ts, bad):
    return dict(kind='lossy', channels=k, controls=controls, alphabet=['a','b'], transitions=ts, bad=bad)

def words(n):
    return [''.join(w) for k in range(n+1) for w in it.product('ab', repeat=k)]

def subv(w):
    """Enumerate actual deletion masks. No greedy or DP embedding algorithm."""
    return sorted({''.join(w[i] for i in range(len(w)) if (mask >> i) & 1)
                   for mask in range(1 << len(w))})

def succ_channel(p, q, v):
    result = set()
    for t in p['transitions']:
        if t['source'] != q:
            continue
        for before in it.product(*(subv(w) for w in v)):
            mid = list(before)
            c, a = t['channel'], t['symbol']
            if t['op'] == 'send':
                mid[c] += a
            elif t['op'] == 'recv':
                if not mid[c].startswith(a):
                    continue
                mid[c] = mid[c][1:]
            for after in it.product(*(subv(w) for w in mid)):
                result.add((t['target'], after))
    return result

def oracle_above(p, small, q, v):
    if q != small['q']:
        return False
    if p['kind'] == 'resource':
        return all(x >= y for x, y in zip(v, small['v']))
    return all(a in subv(b) for a,b in zip(small['v'],v))

def finite_oracle(p, initial, limit=200000):
    """Reachability to exhaustion. Limit never becomes a negative answer."""
    todo = deque([(initial['q'], tuple(initial['v']))]); seen = set(todo)
    while todo:
        q,v = todo.popleft()
        if any(oracle_above(p,b,q,v) for b in p['bad']):
            return 'unsafe', len(seen)
        if p['kind'] == 'resource':
            nxt = []
            for t in p['transitions']:
                if t['source'] != q or any(v[i]<t['consume'][i] for i in range(len(v))):
                    continue
                # Direct expanded arithmetic, separate from both worker routines.
                out = tuple(t['produce'][j]+sum(t['matrix'][j][i]*v[i]
                    -t['matrix'][j][i]*t['consume'][i] for i in range(len(v)))
                    for j in range(len(v)))
                nxt.append((t['target'],out))
        else:
            nxt = succ_channel(p,q,v)
        for x in nxt:
            if x not in seen:
                seen.add(x); todo.append(x)
                if len(seen)>limit:
                    raise RuntimeError('finite oracle budget exhausted; not a safety verdict')
    return 'safe',len(seen)

def named_examples():
    eye = [[1,0,0],[0,1,0],[0,0,1]]
    semaphore = resource(3,1,[R(0,0,[1,0,1],eye,[0,1,0]),
                             R(0,0,[0,1,0],eye,[1,0,1])],[S(0,0,2,0)])
    faulty = copy.deepcopy(semaphore); faulty['transitions'][0]['produce']=[0,1,1]
    merger = resource(2,2,[R(0,1,[0,0],[[1,1],[0,0]],[0,0])],[S(1,4,0)])
    accelerated = copy.deepcopy(merger)
    accelerated['transitions'].append(R(0,0,[1,0],[[2,0],[0,1]],[2,0]))
    doubling = resource(1,1,[R(0,0,[1],[[2]],[2])],[S(0,10**100)])
    blocked = resource(2,2,[R(0,1,[0,0],[[0,0],[0,0]],[0,0])],[S(1,1,0)])
    loss = lossy(1,2,[C(0,1,'recv','a')],[S(1,'')])
    fifo = lossy(1,3,[C(0,0,'send','b'), C(0,1,'recv','a'), C(1,2,'recv','b')],[S(2,'')])
    twoc = lossy(2,3,[C(0,1,'recv','a',0),C(1,2,'recv','b',1),C(0,0,'send','b',0)],[S(2,'','')])
    empt = resource(1,1,[R(0,0,[0],[[1]],[1])],[])
    return {
        'semaphore':(semaphore,[S(0,n,0,1) for n in [0,1,2,100,10**30]]+[S(0,2,0,2)]),
        'faulty_semaphore':(faulty,[S(0,n,0,1) for n in [0,1,2,7]]),
        'merger':(merger,[S(0,0,4),S(0,2,2),S(0,1,2),S(1,4,0)]),
        'guarded_doubling_merger':(accelerated,[S(0,1,0),S(0,0,3),S(0,0,4)]),
        'huge_threshold':(doubling,[S(0,0),S(0,1),S(0,2)]),
        'blocked_reset':(blocked,[S(0,100,100),S(1,1,0)]),
        'lossy_not_reliable':(loss,[S(0,'ba'),S(0,'bb'),S(0,'a')]),
        'fifo_send_loop':(fifo,[S(0,'a'),S(0,'b'),S(0,'ab'),S(0,'ba')]),
        'two_channels':(twoc,[S(0,'a','b'),S(0,'a','a'),S(0,'baa','bab')]),
        'empty_bad':(empt,[S(0,0),S(0,100)])
    }

def execute(out):
    rng = random.Random(SEED)
    summary = {'seed':SEED, 'python':sys.version, 'platform':platform.platform(),
               'lean':{'available':False,'compiled_files':0,'note':'No Lean executable found in this run.'},
               'units':'Counts are grouped by distinct experiment units; there is no grand total.'}
    corpus=[]; timings=[]; examples={}; traces=[]
    for name,(p,queries) in named_examples().items():
        ck.validate_problem(p)
        begin=time.perf_counter(); result=pr.solve(p); search_s=time.perf_counter()-begin
        assert result['status']=='complete',(name,result)
        c=result['certificate']; begin=time.perf_counter();info=ck.verify(p,c);check_s=time.perf_counter()-begin
        dump(out/'examples'/f'{name}.problem.json',p)
        dump(out/'examples'/f'{name}.certificate.json',c)
        reports=[]
        for i,x in enumerate(queries):
            verdict=ck.classify_checked(p,c,x)
            tr=pr.witness(p,c,x)
            if tr is not None:
                length=ck.verify_trace(p,tr,x)
                dump(out/'examples'/f'{name}.{i}.trace.json',tr)
                traces.append({'problem':p,'trace':tr})
            else:
                length=None
            reports.append({'initial':x,'verdict':verdict,'trace_steps':length})
        basis=[c['nodes'][i]['state'] for i in c['basis']]
        examples[name]={'basis':basis,'queries':reports,'search_stats':result['stats']}
        timings.append({'name':name,'search_seconds':search_s,'replay_seconds':check_s,
                        'certificate_bytes':len(pr.canonical(c).encode()),**info})
        corpus.append({'name':name,'problem':p,'certificate':c})
    assert examples['semaphore']['basis']==[S(0,0,2,0),S(0,1,1,1),S(0,2,0,2)]
    assert [x for x in examples['guarded_doubling_merger']['basis'] if x['q']==0]==[S(0,0,4),S(0,1,0)]
    assert examples['huge_threshold']['basis']==[S(0,1)]
    summary['named_examples']=examples
    summary['timings']=timings
    print('Named examples:',len(examples),'accepted',flush=True)
    # Local resource differential: includes non-diagonal, zero, reset, and copy matrices.
    local_models=0; local_queries=0
    for coeffs in it.product(range(3),repeat=4):
        A=[list(coeffs[:2]),list(coeffs[2:])]
        for u in it.product(range(4),repeat=2):
            a=[rng.randrange(3) for _ in range(2)];b=[rng.randrange(3) for _ in range(2)]
            t=R(0,1,a,A,b); p=resource(2,2,[t],[S(1,*u)])
            preds,rec=pr.resource_pre(t,u,pr.Budget())
            cp=ck.checked_predecessors(p,t,S(1,*u),rec)
            assert [x['v'] for x in cp]==[list(x) for x in preds]
            local_models+=1
            # z goes beyond every construction cap (maximum 3 in this family).
            for x in it.product(range(7),repeat=2):
                feasible=all(x[i]>=a[i] for i in range(2)) and all(
                    b[j]+sum(A[j][i]*(x[i]-a[i]) for i in range(2))>=u[j]
                    for j in range(2))
                represented=any(all(x[i]>=v[i] for i in range(2)) for v in preds)
                assert feasible==represented,(t,u,x,preds)
                local_queries+=1
    summary['local_resource']={'predecessor_problems':local_models,'point_comparisons':local_queries,'mismatches':0}
    print('Local resource comparisons:',local_queries,flush=True)
    # Direct deletion-mask semantics for FIFO, independent of predecessor formulas.
    lc=0
    for op,a in [('send','a'),('send','b'),('recv','a'),('recv','b'),('tau','')]:
        t=C(0,1,op,a); p=lossy(1,2,[t],[])
        for w in words(4):
            outputs=succ_channel(p,0,(w,))
            for u in words(3):
                preds,rec=pr.channel_pre(t,(u,),pr.Budget())
                ck.checked_predecessors(p,t,S(1,u),rec)
                actual=any(u in subv(outv[0]) for _,outv in outputs)
                represented=preds[0][0] in subv(w)
                assert actual==represented,(t,w,u,preds,outputs)
                lc+=1
    summary['local_fifo']={'action_rules':5,'word_pair_comparisons':lc,'mismatches':0}
    print('Local FIFO comparisons:',lc,flush=True)
    # Nonincreasing total-resource systems: every oracle state lies in a finite simplex.
    systems=queries=unsafe=max_states=0
    for model in range(100):
        ts=[]
        for _ in range(5):
            A=[[0]*3 for _ in range(3)]
            for i in range(3):
                dest=rng.randrange(4)
                if dest<3:A[dest][i]=1
            a=[rng.randrange(2) for _ in range(3)];b=[0]*3
            for _ in range(rng.randrange(sum(a)+1)):
                b[rng.randrange(3)]+=1
            ts.append(R(rng.randrange(2),rng.randrange(2),a,A,b))
        bad=[S(rng.randrange(2),*(rng.randrange(3) for _ in range(3)))]
        p=resource(3,2,ts,bad)
        result=pr.solve(p)
        assert result['status']=='complete',(model,result)
        c=result['certificate'];ck.verify(p,c);systems+=1
        corpus.append({'name':f'conservative_{model}','problem':p,'certificate':c})
        for q in range(2):
            for v in it.product(range(5),repeat=3):
                if sum(v)>4:continue
                initial=S(q,*v);answer,visited=finite_oracle(p,initial)
                got=pr.classify(p,c,initial)
                assert got==answer,(model,initial,got,answer)
                queries+=1;unsafe+=answer=='unsafe';max_states=max(max_states,visited)
                if answer=='unsafe':ck.verify_trace(p,pr.witness(p,c,initial),initial)
    summary['finite_resource_oracle']={'systems':systems,'initial_state_queries':queries,
        'unsafe_queries':unsafe,'safe_queries':queries-unsafe,'largest_visited_set':max_states,'mismatches':0,
        'finiteness_reason':'Total resource never increases; initial total <=4.'}
    print('Finite resource oracle:',systems,queries,flush=True)
    def channel_batch(count,acyclic):
        nqueries=nunsafe=largest=0
        for model in range(count):
            k=2 if acyclic else 1; qs=3 if acyclic else 2;ts=[]
            for _ in range(4):
                src=rng.randrange(qs-1) if acyclic else rng.randrange(qs)
                dst=rng.randrange(src+1,qs) if acyclic else rng.randrange(qs)
                op=rng.choice(['send','recv','tau'] if acyclic else ['recv','tau'])
                ts.append(C(src,dst,op,rng.choice('ab') if op!='tau' else '',rng.randrange(k)))
            bad=[S(rng.randrange(qs),*(rng.choice(words(2)) for _ in range(k)))]
            p=lossy(k,qs,ts,bad);result=pr.solve(p)
            assert result['status']=='complete',(model,result)
            c=result['certificate'];ck.verify(p,c)
            corpus.append({'name':f'fifo_{"acyclic" if acyclic else "decreasing"}_{model}',
                           'problem':p,'certificate':c})
            for q in range(qs):
                for v in it.product(words(2 if acyclic else 4),repeat=k):
                    if acyclic and sum(map(len,v))>2:continue
                    x=S(q,*v);answer,visited=finite_oracle(p,x)
                    assert pr.classify(p,c,x)==answer,(p,x,answer)
                    nqueries+=1;nunsafe+=answer=='unsafe';largest=max(largest,visited)
                    if answer=='unsafe':ck.verify_trace(p,pr.witness(p,c,x),x)
        return {'systems':count,'initial_state_queries':nqueries,'unsafe_queries':nunsafe,
                'safe_queries':nqueries-nunsafe,'largest_visited_set':largest,'mismatches':0,
                'finiteness_reason':'Acyclic controls bound sends.' if acyclic else 'No sends; lengths never increase.'}
    summary['finite_fifo_acyclic_oracle']=channel_batch(40,True)
    summary['finite_fifo_decreasing_oracle']=channel_batch(40,False)
    print('Finite FIFO oracles complete',flush=True)
    # Mutations target mathematical checks as well as subject binding and decoding.
    mutations=[]
    def rejects(name,p,c):
        try:ck.verify(p,c)
        except ck.Reject as ex:mutations.append({'name':name,'rejected':True,'diagnostic':str(ex)});return
        raise AssertionError('invalid mutation accepted: '+name)
    base=next(x for x in corpus if x['name']=='merger');p=base['problem'];c=base['certificate']
    d=copy.deepcopy(c);d['closure'].pop();rejects('missing_closure',p,d)
    d=copy.deepcopy(c);d['closure'].append(copy.deepcopy(d['closure'][0]));rejects('duplicate_closure',p,d)
    d=copy.deepcopy(c);d['target_cover']=[];rejects('missing_target_coverage',p,d)
    d=copy.deepcopy(c);d['nodes'][-1]['child']=len(d['nodes'])-1;rejects('cyclic_DAG',p,d)
    d=copy.deepcopy(c);d['nodes'][-1]['state']['v']=[0,0];rejects('false_lower_inclusion',p,d)
    d=copy.deepcopy(c);d['subject']='{}';rejects('wrong_subject',p,d)
    d=copy.deepcopy(c);d['basis'].append(d['basis'][0]);rejects('duplicate_basis',p,d)
    d=copy.deepcopy(c);d['closure'][0]['cover']=[];rejects('missing_predecessor_cover',p,d)
    boxindex=next(i for i,e in enumerate(c['closure']) if e['predecessor']['kind']=='box')
    d=copy.deepcopy(c);d['closure'][boxindex]['predecessor']['caps']=[0,0];rejects('invalid_clipping_bound',p,d)
    d=copy.deepcopy(c);d['closure'][boxindex]['predecessor']['tree']=['covered',0];rejects('false_covered_leaf',p,d)
    d=copy.deepcopy(c);d['closure'][boxindex]['predecessor']['tree']=['impossible',0];rejects('false_impossible_leaf',p,d)
    d=copy.deepcopy(c);d['closure'][boxindex]['predecessor']['tree']=['split',0,99,['covered',0],['covered',0]];rejects('invalid_partition',p,d)
    d=copy.deepcopy(c);d['closure'][boxindex]['predecessor']={'kind':'diagonal'};rejects('false_diagonal_dispatch',p,d)
    d=copy.deepcopy(c);d['closure'][boxindex]['predecessor']['minima'][0]=[0,0];rejects('infeasible_minimum',p,d)
    for name,value in [('boolean_is_not_nat',True),('negative_coefficient',-1),('float_coefficient',1.0)]:
        changed=copy.deepcopy(p);changed['transitions'][0]['matrix'][0][0]=value
        d=copy.deepcopy(c);d['subject']=pr.canonical(changed);rejects(name,changed,d)
    changed=copy.deepcopy(p);changed['transitions'][0]['produce']=[10,0]
    d=copy.deepcopy(c);d['subject']=pr.canonical(changed);rejects('semantic_change_rebound_subject',changed,d)
    changed=copy.deepcopy(p);changed['transitions'][0]['zero_test']=[0]
    d=copy.deepcopy(c);d['subject']=pr.canonical(changed);rejects('zero_test_not_silently_erased',changed,d)
    for number,case in enumerate(corpus[:8]):
        if not case['certificate']['closure']:continue
        d=copy.deepcopy(case['certificate']);d['closure']=[]
        rejects(f'all_closure_removed_{number}',case['problem'],d)
    # Concrete traces must reject invented losses and wrong queue head operations.
    tracebase=next(x for x in traces if x['problem']['kind']=='lossy' and x['trace']['steps'])
    for name,field in [('invented_pre_loss','before'),('invented_post_loss','after')]:
        tr=copy.deepcopy(tracebase['trace']);e=tr['steps'][0]
        if field=='before':e[field][0]+='abababab'
        else:e[field]['v'][0]+='abababab'
        try:ck.verify_trace(tracebase['problem'],tr)
        except ck.Reject as ex:mutations.append({'name':name,'rejected':True,'diagnostic':str(ex)})
        else:raise AssertionError(name)
    # Exercise strict JSON parser in genuine files.
    for i,text in enumerate(['{"a":1,"a":2}','{"a":1.0}','{"a":NaN}']):
        path=out/'parser-inputs'/f'bad-{i}.json';path.parent.mkdir(exist_ok=True);path.write_text(text)
        try:ck.load_json(str(path))
        except ck.Reject as ex:mutations.append({'name':f'json_{i}','rejected':True,'diagnostic':str(ex)})
        else:raise AssertionError(text)
    dump(out/'mutations.json',mutations)
    summary['mutations']={'attempts':len(mutations),'rejected':len(mutations),'accepted_invalid':0}
    unknowns=[]
    for name,budget in [('nodes',pr.Budget(max_nodes=0)),('expansions',pr.Budget(max_expansions=0)),
                        ('grid',pr.Budget(max_grid=1)),('box',pr.Budget(max_box_nodes=0))]:
        r=pr.solve(p,budget);assert r['status']=='unknown',r
        unknowns.append({'cutoff':name,**r})
    summary['cutoff_controls']=unknowns
    # Search module made unimportable during a complete independent replay.
    code='''import sys,json,importlib.abc\nclass NoSearch(importlib.abc.MetaPathFinder):\n def find_spec(self,fullname,path=None,target=None):\n  if fullname in ("search","numpy","sympy","scipy"):raise RuntimeError("forbidden import: "+fullname)\nsys.meta_path.insert(0,NoSearch())\nsys.path.insert(0,sys.argv[1])\nimport checker\nfor row in checker.load_json(sys.argv[2]):checker.verify(row["problem"],row["certificate"])\nprint("REPLAY_OK")\n'''
    dump(out/'corpus.json',corpus)
    replay=subprocess.run([sys.executable,'-S','-c',code,str(ROOT/'prototype'),str(out/'corpus.json')],
                          text=True,capture_output=True,check=False)
    assert replay.returncode==0 and 'REPLAY_OK' in replay.stdout,replay.stderr
    summary['independent_replay']={'certificates':len(corpus),'returncode':replay.returncode,
        'stdout':replay.stdout,'search_import_forbidden':True,'site_packages_disabled':True}
    dump(out/'trace-corpus.json',traces)
    dump(out/'summary.json',summary)
    print(json.dumps({k:v for k,v in summary.items() if k not in ('named_examples','timings')},indent=2))
    return summary

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,default=ROOT/'reproduced-results')
    args=ap.parse_args();args.output.mkdir(parents=True,exist_ok=True)
    try:execute(args.output.resolve())
    except Exception:
        import traceback
        text=traceback.format_exc();(args.output/'FAILED_RUN.txt').write_text(text)
        raise
if __name__=='__main__':main()
