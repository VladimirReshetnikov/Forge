#!/usr/bin/env python3
"""Run a matched synthetic comparison; default writes reproduced-results/.

Each case/mode runs in a disposable spawned process. A process timeout is
UNKNOWN, not a negative answer. The parent independently checks every positive
certificate and concrete counterexample before recording 'accepted'.
"""
from __future__ import annotations
import argparse
from collections import Counter,defaultdict
from dataclasses import asdict
from datetime import datetime,timezone
import csv,json,multiprocessing as mp,platform,sys,time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import sympy
from cases import corpus,SEED
from search import solve,Limits
from verify_stdlib import check_certificate,check_counterexample

LIMITS=Limits(degree=6,generators=40,pullbacks=200,coefficient_terms=1500,seconds=10)

def worker(case,mode,conn):
    try:
        conn.send(solve(case.system,mode,LIMITS))
    except Exception as e:
        conn.send({'status':'infrastructure-error','error':type(e).__name__+': '+str(e),'mode':mode,'stats':{}})
    finally:
        conn.close()

def run_one(case,mode,hard_timeout):
    ctx=mp.get_context('spawn')
    recv,send=ctx.Pipe(duplex=False)
    p=ctx.Process(target=worker,args=(case,mode,send))
    start=time.perf_counter();p.start();send.close()
    try:
        if recv.poll(hard_timeout):
            result=recv.recv()
        else:
            result={'status':'unknown','reason':'external process timeout','mode':mode,'stats':{}}
    except EOFError:
        result={'status':'infrastructure-error','error':'worker exited without a result','mode':mode,'stats':{}}
    finally:
        if p.is_alive():p.terminate()
        p.join(3)
        if p.is_alive():p.kill();p.join()
        recv.close()
    result['process_seconds']=time.perf_counter()-start
    return result

def dump(path,obj):
    path.write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path('reproduced-results'))
    parser.add_argument('--hard-timeout',type=float,default=30)
    parser.add_argument('--jobs',type=int,default=4)
    parser.add_argument('--resume',action='store_true',help='reuse exact existing run records; never change them')
    args=parser.parse_args()
    if args.output.exists() and any(args.output.iterdir()) and not args.resume:
        parser.error('output must be absent or empty; recorded evidence is not overwritten')
    args.output.mkdir(parents=True,exist_ok=True)
    (args.output/'problems').mkdir(exist_ok=True);(args.output/'evidence').mkdir(exist_ok=True);(args.output/'runs').mkdir(exist_ok=True)
    cases=corpus();rows=[]
    pool=ThreadPoolExecutor(max_workers=args.jobs)
    pending={}
    for c in cases:
        for m in ('linear','ideal'):
            rp=args.output/'runs'/f'{c.system.name}.{m}.json'
            if not rp.exists():
                pending[(c.system.name,m)]=pool.submit(run_one,c,m,args.hard_timeout)
    for case in cases:
        name=case.system.name;problem=case.system.json()
        problem_path=args.output/'problems'/f'{name}.json'
        if problem_path.exists():
            if json.loads(problem_path.read_text())!=problem:raise ValueError('resume problem mismatch')
        else: dump(problem_path,problem)
        for mode in ('linear','ideal'):
            run_path=args.output/'runs'/f'{name}.{mode}.json'
            reused=run_path.exists()
            result=json.loads(run_path.read_text()) if reused else pending[(name,mode)].result()
            row=dict(case=name,family=case.family,mode=mode,expected=case.expected,
                     status=result['status'],accepted=False,reason=result.get('reason',''))
            if result['status'] in ('proved','refuted'):
                t=time.perf_counter()
                check=check_certificate if result['status']=='proved' else check_counterexample
                receipt=check(problem,result['evidence'])
                row.update(check_seconds=time.perf_counter()-t,**receipt)
                if result['status']!=case.expected:
                    raise AssertionError(f'construction expectation disagrees: {name}/{mode}')
                ep=args.output/'evidence'/f'{name}.{mode}.json'
                if ep.exists():
                    if json.loads(ep.read_text())!=result['evidence']:raise ValueError('evidence mismatch')
                else:dump(ep,result['evidence'])
                result['replay']=receipt
            row.update(result['stats']);row['process_seconds']=result['process_seconds']
            rows.append(row)
            if not reused:dump(run_path,result)
            print(f'{name:30} {mode:6} {result["status"]}',flush=True)
    pool.shutdown()
    fields=list(dict.fromkeys(k for row in rows for k in row))
    with (args.output/'measurements.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=fields);w.writeheader();w.writerows(rows)
    summary=[]
    for fam in dict.fromkeys(c.family for c in cases):
        for mode in ('linear','ideal'):
            rs=[r for r in rows if r['family']==fam and r['mode']==mode]
            summary.append(dict(family=fam,mode=mode,cases=len(rs),counts=dict(Counter(r['status'] for r in rs)),
                discovery_seconds=sum(r.get('elapsed_seconds',0) for r in rs),
                process_seconds=sum(r['process_seconds'] for r in rs),
                check_seconds=sum(r.get('check_seconds',0) for r in rs)))
    dump(args.output/'summary.json',dict(problems=len(cases),runs=len(rows),groups=summary,
         accepted=sum(r['accepted'] for r in rows),unknown=sum(r['status']=='unknown' for r in rows)))
    dump(args.output/'manifest.json',dict(timestamp=datetime.now(timezone.utc).isoformat(),seed=SEED,
         python=sys.version,platform=platform.platform(),sympy=sympy.__version__,limits=asdict(LIMITS),
         hard_timeout=args.hard_timeout,jobs=args.jobs,resumed=args.resume,comparison='matched synthetic linear vs ideal, NOT Lean tactics',
         lean='NOT_RUN; no Lean compiler available',command=' '.join(sys.argv)))

if __name__=='__main__':main()
