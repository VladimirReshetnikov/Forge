"""Compile replay examples in an existing compatible Mathlib Lake project.

Usage: python run_checks.py --project /path/to/mathlib-project
This is a compilation harness, not a performance comparison against grind.
No package is installed and no project file is edited.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys
import time


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--project', type=Path, default=Path.cwd())
    ap.add_argument('--timeout', type=float, default=120)
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    lake = shutil.which('lake')
    result = {'purpose': 'Compile supplied replay scripts; not a grind benchmark',
              'project': str(args.project.resolve()), 'files': []}
    if not lake:
        result['status'] = 'not_run'
        result['reason'] = 'lake executable is not available on PATH'
        code = 2
    else:
        result['status'] = 'passed'
        for f in sorted(Path(__file__).resolve().parent.glob('*.lean')):
            start = time.perf_counter()
            try:
                p = subprocess.run([lake, 'env', 'lean', str(f)],
                    cwd=args.project, capture_output=True, text=True,
                    encoding='utf-8', errors='replace', timeout=args.timeout)
                row = {'file': f.name, 'returncode': p.returncode,
                       'stdout': p.stdout, 'stderr': p.stderr,
                       'elapsed_s': time.perf_counter()-start}
                if p.returncode: result['status'] = 'failed'
            except subprocess.TimeoutExpired:
                row = {'file': f.name, 'status': 'timeout', 'timeout_s': args.timeout}
                result['status'] = 'failed'
            result['files'].append(row)
        code = int(result['status'] != 'passed')
    text = json.dumps(result, indent=2)+'\n'
    if args.output: args.output.write_text(text, encoding='utf-8')
    print(text, end='')
    return code

if __name__ == '__main__': sys.exit(main())
