#!/usr/bin/env python3
"""Compile authored/generated Lean files when the pinned Lake project is ready.

No success is inferred when a compiler is missing. This runner does not audit
transitive axioms; use an independent axiom audit as a separate acceptance gate.
"""
import argparse,json,shutil,subprocess
from pathlib import Path

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    root=Path(__file__).resolve().parents[1]/'lean';rows=[]
    lake=shutil.which('lake')
    for name in ('Core.lean','IntegrationSpecimens.lean','GeneratedIdentities.lean'):
        row=dict(file=name,status='NOT_RUN',reason='lake executable unavailable')
        if lake:
            try:
                r=subprocess.run([lake,'env','lean',name],cwd=root,text=True,capture_output=True,timeout=180)
                row.update(status='ELABORATED' if r.returncode==0 else 'FAILED',returncode=r.returncode,
                           stdout=r.stdout,stderr=r.stderr,reason='')
            except subprocess.TimeoutExpired:row.update(status='TIMEOUT',reason='180-second process limit')
        rows.append(row)
    a.output.write_text(json.dumps(dict(results=rows,axiom_audit='NOT_RUN'),indent=2)+'\n')
    print(json.dumps(rows))
    return 0 if all(r['status']=='ELABORATED' for r in rows) else 2

if __name__=='__main__':raise SystemExit(main())
