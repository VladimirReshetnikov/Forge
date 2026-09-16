#!/usr/bin/env python3
"""Create and independently check a resource-frontier certificate.

Examples:
  python -S prototype/solve.py examples/mutex.json --out my-results/mutex.json
  python -S prototype/solve.py examples/broken_mutex.json --slope 1,0,0 --offset 0,1,0 --out my-results/threshold.json
  python -S prototype/solve.py examples/mutex.json --family examples/population-permits.json --out my-results/parameters.json
A .json output is one replay RECORD, not JSONL unless a newline file is used.
The replay tool accepts it as a one-record JSONL file (compact single-line JSON).
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import sys
from forge_resources import producer as P
from forge_resources.checker import load_json, check_record, InvalidCertificate, ResourceLimit


def naturals(text: str) -> list[int]:
    try: ns = [int(n.strip()) for n in text.split(',')]
    except ValueError as exc: raise argparse.ArgumentTypeError('use comma-separated nonnegative integers') from exc
    if any(n < 0 for n in ns): raise argparse.ArgumentTypeError('negative coordinate')
    return ns


def main() -> int:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('problem',type=Path)
    ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--accelerate',action='store_true',help='exact productive-transition power saturation')
    ap.add_argument('--max-candidates',type=int,default=100_000)
    ap.add_argument('--max-insertions',type=int,default=20_000)
    ap.add_argument('--max-box',type=int,default=100_000)
    ap.add_argument('--slope',type=naturals)
    ap.add_argument('--offset',type=naturals)
    ap.add_argument('--family',type=Path,help='JSON object with matrix and offset')
    args=ap.parse_args()
    if args.out.exists(): ap.error('output exists; choose a new file')
    if (args.slope is None)!=(args.offset is None): ap.error('--slope and --offset must occur together')
    if args.family is not None and args.slope is not None: ap.error('choose scalar OR multiparameter mode')
    if min(args.max_candidates,args.max_insertions,args.max_box)<0: ap.error('budgets must be nonnegative')
    try:
        p=load_json(args.problem.read_text())
        result=P.frontier(p,max_candidates=args.max_candidates,max_insertions=args.max_insertions,accelerate=args.accelerate)
        if result['status']=='UNKNOWN':
            print(json.dumps(result));return 2
        cert=result['certificate'];expected=p
        if args.slope is not None:
            cert=P.threshold(p,cert,args.slope,args.offset);expected=cert['query']
        elif args.family is not None:
            family=load_json(args.family.read_text())
            if type(family) is not dict or set(family)!={'matrix','offset'}: raise ValueError('family requires matrix and offset only')
            result=P.parameters(p,cert,family['matrix'],family['offset'],max_box=args.max_box)
            if result['status']=='UNKNOWN':print(json.dumps(result));return 2
            cert=result['certificate'];expected=cert['query']
        record={'name':args.problem.stem,'expected':expected,'certificate':cert}
        checked=check_record(record)
        args.out.parent.mkdir(parents=True,exist_ok=True)
        with args.out.open('x') as f:f.write(json.dumps(record,sort_keys=True)+'\n')
        print(json.dumps(checked,indent=2));return 0
    except ResourceLimit as exc:
        print(json.dumps({'status':'UNKNOWN_RESOURCE_LIMIT','reason':str(exc)}));return 2
    except (OSError,ValueError,KeyError,TypeError) as exc:
        print(json.dumps({'status':'INVALID_OR_UNREADABLE','reason':str(exc)}),file=sys.stderr);return 1

if __name__=='__main__':raise SystemExit(main())
