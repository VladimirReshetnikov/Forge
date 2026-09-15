#!/usr/bin/env python3
"""Record a local candidate-project build. Not run in the authoring environment."""
from __future__ import annotations
import argparse,datetime,json,shutil,subprocess,sys
from pathlib import Path


def main() -> int:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--timeout',type=float,default=1200,help='Build time limit in seconds, not a runtime prediction.')
    ap.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'results/user-lean-check.json')
    args=ap.parse_args()
    if args.timeout<=0:ap.error('--timeout must be positive')
    result={'timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'command':['lake','build'],'build_executed':False,'build_succeeded':False,
            'axiom_whitelist_audit_performed':False,
            'notice':'A local build result; not a measurement of a complete forge tactic.'}
    lake=shutil.which('lake')
    if lake is None:
        result['error']='lake is not available on PATH; no Lean build was performed.'
    else:
        result['build_executed']=True
        try:
            p=subprocess.run([lake,'build'],cwd=Path(__file__).resolve().parent,
                             text=True,capture_output=True,timeout=args.timeout)
            result.update(returncode=p.returncode,build_succeeded=p.returncode==0,
                          stdout=p.stdout,stderr=p.stderr)
        except subprocess.TimeoutExpired as exc:
            result['error']='Configured build time limit reached.'
            result['stdout']=(exc.stdout or b'').decode(errors='replace') if isinstance(exc.stdout,bytes) else exc.stdout
            result['stderr']=(exc.stderr or b'').decode(errors='replace') if isinstance(exc.stderr,bytes) else exc.stderr
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('stdout','stderr')},indent=2))
    print('Full log:',args.output)
    return 0 if result['build_succeeded'] else 2


if __name__=='__main__':sys.exit(main())
