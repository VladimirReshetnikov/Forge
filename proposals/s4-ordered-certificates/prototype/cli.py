"""Search, independently check, and export an ordered-state region certificate.

Example:
  python -S prototype/cli.py results/examples/semaphore.problem.json --out /tmp/region.json
No Lean proof or tactic installation is performed.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import checker
import search

def natural(text: str) -> int:
    value=int(text)
    if value<0:raise argparse.ArgumentTypeError('budget must be nonnegative')
    return value

def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('problem',type=Path)
    parser.add_argument('--out',required=True,type=Path)
    parser.add_argument('--engine',choices=['separation','eager'],default='separation')
    parser.add_argument('--initial',type=Path,help='Optional JSON state to classify and trace')
    parser.add_argument('--max-nodes',type=natural,default=20000)
    parser.add_argument('--max-expansions',type=natural,default=50000)
    parser.add_argument('--max-grid',type=natural,default=200000)
    parser.add_argument('--max-box-nodes',type=natural,default=1000000)
    args=parser.parse_args()
    try:
        p=checker.load_json(str(args.problem));checker.validate_problem(p)
        budget=search.Budget(args.max_nodes,args.max_expansions,args.max_grid,args.max_box_nodes)
        solve=search.solve_separation if args.engine=='separation' else search.solve
        try:result=solve(p,budget)
        except (RecursionError,MemoryError) as ex:
            result={'status':'unknown','reason':type(ex).__name__}
        if result['status']!='complete':
            print(json.dumps(result,sort_keys=True));raise SystemExit(2)
        c=result['certificate'];checked=checker.verify(p,c)
        args.out.parent.mkdir(parents=True,exist_ok=True)
        # Refuse overwrite: a caller must deliberately choose a fresh output path.
        with args.out.open('x') as f:json.dump(c,f,sort_keys=True,indent=2);f.write('\n')
        response={'status':'accepted_by_python_checker','checked':checked,'search_stats':result['stats'],
                  'certificate':str(args.out),'lean_kernel_checked':False}
        if args.initial is not None:
            initial=checker.load_json(str(args.initial));checker.validate_state(p,initial)
            response['classification']=checker.classify_checked(p,c,initial)
            tr=search.witness(p,c,initial)
            if tr is not None:
                response['trace_steps']=checker.verify_trace(p,tr,initial)
                tracefile=args.out.with_suffix('.trace.json')
                with tracefile.open('x') as f:json.dump(tr,f,sort_keys=True,indent=2);f.write('\n')
                response['trace']=str(tracefile)
        print(json.dumps(response,sort_keys=True))
    except (checker.Reject, OSError, ValueError) as ex:
        parser.exit(1,f'NOT ACCEPTED: {ex}\n')
if __name__=='__main__':main()
