"""Command-line research workers; output is NOT a Lean proof.

Example: python -S prototype/forge_worker.py search vass examples/mutex.model.json
A nominal input is a JSON array [left_machine, right_machine].
"""
from __future__ import annotations
import argparse,json,sys
from pathlib import Path
import checker


def main() -> int:
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('action',choices=['search','check'])
    p.add_argument('engine',choices=['vass','nominal','mixed'])
    p.add_argument('model',type=Path)
    p.add_argument('--certificate',type=Path)
    p.add_argument('--output',type=Path)
    p.add_argument('--max-states',type=int,default=10000)
    p.add_argument('--max-admissions',type=int,default=20000)
    args=p.parse_args()
    try:
        model=checker.load_json(args.model.read_text(encoding='utf-8'))
        if args.engine=='vass':checker.validate_vass(model)
        elif args.engine=='mixed':checker.validate_register_net(model)
        else:
            checker.require(isinstance(model,list) and len(model)==2,'expected two machines')
            for m in model:checker.validate_machine(m)
        def check(cert):
            if args.engine=='vass':return checker.check_vass(model,cert)
            if args.engine=='mixed':return checker.check_mixed(model,cert)
            return checker.check_nominal(*model,cert)
        if args.action=='check':
            if args.certificate is None:raise checker.Invalid('--certificate is required')
            cert=checker.load_json(args.certificate.read_text(encoding='utf-8'))
            accepted=check(cert)
            print(json.dumps({'accepted':accepted,'evidence':'Python checker only'}))
            return 0 if accepted else 1
        checker.require(args.max_states>0 and args.max_admissions>0,'limits must be positive')
        if args.engine=='vass':
            import antichain
            cert=antichain.solve(model,max_admissions=args.max_admissions)
        elif args.engine=='nominal':
            import nominal
            cert=nominal.equivalence(*model,max_states=args.max_states)
        else:
            import mixed
            cert=mixed.solve(model,max_states=args.max_states,max_admissions=args.max_admissions)
        unknown=cert.get('kind')=='unknown'
        if not unknown and not check(cert):raise checker.Invalid('producer output rejected')
        text=json.dumps(cert,indent=2,sort_keys=True)+'\n'
        if args.output:args.output.write_text(text,encoding='utf-8')
        else:print(text,end='')
        return 2 if unknown else 0
    except (OSError,ValueError,KeyError,TypeError,IndexError,AttributeError,RecursionError) as exc:
        print(f'error: {exc}',file=sys.stderr)
        return 1

if __name__=='__main__':raise SystemExit(main())
