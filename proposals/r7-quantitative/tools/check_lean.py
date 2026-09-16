#!/usr/bin/env python3
"""Record actual elaboration attempts; missing compiler is NOT_RUN, not success.

Default: core-only candidate. --mathlib additionally attempts a Lake build;
it assumes the project's dependencies have been installed by the operator.
This script does not install dependencies, run remote code, or weaken proofs.
"""
from __future__ import annotations
import argparse, json, shutil, subprocess
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--mathlib',action='store_true')
p.add_argument('--out',type=Path,default=ROOT/'reproduced-results'/'lean-status.json')
a=p.parse_args();out=[]
commands=[('core','lean',['lean','ForgeQ/Monotone.lean'])]
if a.mathlib:commands.append(('mathlib','lake',['lake','build']))
for kind,exe,cmd in commands:
    if not shutil.which(exe):
        out.append({'lane':kind,'status':'NOT_RUN','reason':f'{exe} executable unavailable'})
        continue
    try:
        proc=subprocess.run(cmd,cwd=ROOT/'lean',capture_output=True,text=True,timeout=120)
        out.append({'lane':kind,'status':'ELABORATED' if proc.returncode==0 else 'FAILED',
                    'command':cmd,'returncode':proc.returncode,'stdout':proc.stdout,'stderr':proc.stderr})
    except subprocess.TimeoutExpired:
        out.append({'lane':kind,'status':'TIMEOUT','command':cmd})
a.out.parent.mkdir(parents=True,exist_ok=True)
a.out.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
