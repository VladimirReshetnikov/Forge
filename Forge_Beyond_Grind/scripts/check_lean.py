"""Run supplied Lean examples when Lake is available; never fake a test result.

Requires dependencies already fetched in lean/ (see README). Writes a separate
report; does not overwrite the Python mechanism results or claim solver wins.
Compilation success is not a full transitive-axiom-policy audit.
"""
from __future__ import annotations
import json
import shutil
import subprocess
from pathlib import Path

root=Path(__file__).resolve().parents[1]
report={'comparison_to_grind':'NOT_PERFORMED','files':[]}
lake=shutil.which('lake')
if lake is None:
    report['status']='NOT_RUN'
    report['reason']='No Lake/Lean executable available'
else:
    try:
        report['version']=subprocess.run([lake,'env','lean','--version'],cwd=root/'lean',text=True,
                          capture_output=True,timeout=60).stdout.strip()
        for name in ('DesignAPI.lean','ConeExamples.lean','QuadraticExamples.lean','InductionExamples.lean'):
            try:
                p=subprocess.run([lake,'env','lean',name],cwd=root/'lean',text=True,capture_output=True,timeout=180)
                report['files'].append({'file':name,'status':'COMPILED' if p.returncode==0 else 'FAILED',
                                        'returncode':p.returncode,'stdout':p.stdout,'stderr':p.stderr})
            except subprocess.TimeoutExpired:
                report['files'].append({'file':name,'status':'TIMEOUT'})
        report['status']='COMPLETED'
    except (OSError,subprocess.TimeoutExpired) as ex:
        report['status']='NOT_RUN';report['reason']=str(ex)
(root/'results'/'lean_status.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
