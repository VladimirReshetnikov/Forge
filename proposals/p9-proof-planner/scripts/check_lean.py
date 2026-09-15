#!/usr/bin/env python3
"""Compile the core reference file if a Lean executable is actually available.

No baseline conclusions follow from a skipped run. This does not install Lean,
Mathlib, SOS, Duper, or Forge, and does not test the complete proposed planner.
"""
from pathlib import Path
import json, shutil, subprocess
ROOT=Path(__file__).resolve().parents[1]
exe=shutil.which('lean')
if exe is None:
    result={'status':'NOT_RUN','reason':'Lean executable is not installed',
            'file':'lean/Structural.lean'}
else:
    try:
        ver=subprocess.run([exe,'--version'],capture_output=True,text=True,timeout=30)
        proc=subprocess.run([exe,str(ROOT/'lean/Structural.lean')],capture_output=True,text=True,timeout=120)
        result={'status':'PASSED' if proc.returncode==0 else 'FAILED',
                'version':ver.stdout.strip(),'exit_code':proc.returncode,
                'stdout':proc.stdout,'stderr':proc.stderr,'file':'lean/Structural.lean'}
    except subprocess.TimeoutExpired as e:
        result={'status':'TIMEOUT','reason':str(e)}
(ROOT/'results/lean_status.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
