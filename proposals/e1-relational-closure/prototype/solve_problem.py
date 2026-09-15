#!/usr/bin/env python3
"""Solve a canonical JSON problem and independently check its returned evidence.

Only data are deserialized; no expression strings are evaluated. The solver runs
in a disposable subprocess. A timeout returns UNKNOWN, never a refutation.
"""
import argparse,json,multiprocessing as mp
from pathlib import Path
import sympy as s
from search import System,Edge,Limits,solve
from verify_stdlib import read_json,parse_problem,check_certificate,check_counterexample

def expression(p,variables):
    return s.Add(*(s.Rational(c.numerator,c.denominator)*s.prod(v**k for v,k in zip(variables,m,strict=True))
                   for m,c in p.items()))

def decode(raw):
    p=parse_problem(raw)
    xs=s.symbols(f'x0:{p["n"]}');ts=s.symbols(f't0:{p["r"]}')
    edges=[]
    for j,(src,dst,k,F) in enumerate(p['edges']):
        us=tuple(s.Symbol(f'u{j}_{i}') for i in range(k))
        edges.append(Edge(src,dst,us,tuple(expression(f,xs+us) for f in F)))
    return System(raw['name'],xs,ts,p['L'],
        [(loc,tuple(expression(v,ts) for v in state)) for loc,state in p['initial']],
        edges,[(loc,expression(q,xs)) for loc,q in p['targets']])

def worker(P,mode,limits,conn):
    try:conn.send(solve(P,mode,limits))
    except Exception as e:conn.send(dict(status='infrastructure-error',error=type(e).__name__+': '+str(e)))
    finally:conn.close()

def main():
    a=argparse.ArgumentParser(description=__doc__)
    a.add_argument('problem',type=Path)
    a.add_argument('--mode',choices=('linear','ideal'),default='ideal')
    a.add_argument('--degree',type=int,default=12)
    a.add_argument('--timeout',type=float,default=30)
    a.add_argument('--evidence',type=Path,help='write checked evidence to a new path')
    args=a.parse_args()
    if args.degree<0 or args.timeout<=0:a.error('nonnegative degree and positive timeout required')
    if args.evidence and args.evidence.exists():a.error('evidence output already exists')
    original=read_json(args.problem);P=decode(original)
    ctx=mp.get_context('spawn');recv,send=ctx.Pipe(duplex=False)
    proc=ctx.Process(target=worker,args=(P,args.mode,Limits(degree=args.degree,seconds=args.timeout),send))
    proc.start();send.close()
    try:
        result=recv.recv() if recv.poll(args.timeout) else dict(status='unknown',reason='external process timeout')
    except EOFError:result=dict(status='infrastructure-error',reason='worker exited without result')
    finally:
        if proc.is_alive():proc.terminate()
        proc.join(3)
        if proc.is_alive():proc.kill();proc.join()
        recv.close()
    if result['status'] in ('proved','refuted'):
        checker=check_certificate if result['status']=='proved' else check_counterexample
        receipt=checker(original,result['evidence']);result['independent_replay']=receipt
        if args.evidence:args.evidence.write_text(json.dumps(result['evidence'],indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))
    return 0 if result['status'] in ('proved','refuted') else 2

if __name__=='__main__':raise SystemExit(main())
