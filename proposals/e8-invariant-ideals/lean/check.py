"""Elaborate the two optional specimens when the pinned Lean toolchain exists.
Always records actual results. Missing runtime is NOT_RUN, not a successful check.
"""
import json
from pathlib import Path
import shutil
import subprocess
import sys
root = Path(__file__).resolve().parent
lean = shutil.which('lean')
report = {'status': 'NOT_RUN', 'reason': 'Lean executable absent', 'files': []}
if lean:
    report = {'status': 'RUN', 'version': subprocess.run([lean, '--version'], cwd=root,
              text=True, capture_output=True).stdout.strip(), 'files': []}
    for name in ['CoreSoundness.lean', 'IndexingSketch.lean']:
        try:
            p = subprocess.run([lean, name], cwd=root, text=True, capture_output=True, timeout=120)
            report['files'].append({'file': name, 'returncode': p.returncode,
                                     'stdout': p.stdout, 'stderr': p.stderr})
        except subprocess.TimeoutExpired:
            report['files'].append({'file': name, 'status': 'TIMEOUT'})
(root/'status.json').write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps(report, indent=2))
sys.exit(0 if report['status'] == 'RUN' and all(x.get('returncode') == 0 for x in report['files']) else 1)
