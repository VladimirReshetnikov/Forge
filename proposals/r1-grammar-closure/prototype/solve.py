"""Command-line access to the experimental worker (no Lean integration).

python -S solve.py problem.json --certificate output.json
python -S solve.py problem.json --quotient --certificate output.json

The separately supplied original problem is decoded before search. All produced
certificates are replayed before a positive/refuted/preservation result prints.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import sys
import checker
from search import Budget, saturate, minimize


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('problem',type=Path)
    parser.add_argument('--certificate',type=Path,required=True)
    parser.add_argument('--quotient',action='store_true')
    parser.add_argument('--max-candidates',type=int,default=100000)
    parser.add_argument('--max-bits',type=int,default=8192)
    parser.add_argument('--max-basis',type=int,default=4096)
    args=parser.parse_args()
    if min(args.max_candidates,args.max_bits,args.max_basis)<0:
        parser.error('limits must be nonnegative')
    try:
        problem=checker.load(args.problem)
        decoded=checker.decode_problem(problem)
        checker.audit_frontend(decoded)
        budget=Budget(args.max_candidates,args.max_bits,args.max_basis)
        result=minimize(problem,budget) if args.quotient else saturate(problem,budget)
        cert=result.get('certificate')
        if cert is not None:
            receipt=checker.verify(problem,cert)
            if not receipt['accepted']:
                print(json.dumps({'status':'REPLAY_REJECTED','replay':receipt}),file=sys.stderr)
                return 2
            # Refuse overwriting an existing artifact, including an input path.
            args.certificate.parent.mkdir(parents=True,exist_ok=True)
            with args.certificate.open('x') as f:
                json.dump(cert,f,indent=2,sort_keys=True);f.write('\n')
            result={'status':result['status'],'certificate_path':str(args.certificate),
                    'stats':result.get('stats',{}),'replay':receipt,
                    'lean_kernel_checked':False}
        print(json.dumps(result,indent=2,sort_keys=True))
        return 3 if result['status']=='UNKNOWN' else 0
    except (OSError,ValueError,KeyError,TypeError,IndexError,OverflowError) as exc:
        print(json.dumps({'status':'INVALID_OR_IO_ERROR','error':str(exc)}),file=sys.stderr)
        return 2

if __name__=='__main__':raise SystemExit(main())
