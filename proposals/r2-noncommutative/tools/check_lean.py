#!/usr/bin/env python3
"""Explicit compiler gate. Missing toolchains are NOT_RUN, never successful validation."""
import argparse,json,shutil,subprocess,sys
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('--project',type=Path,help='existing, built Mathlib project')
args=ap.parse_args();root=Path(__file__).resolve().parents[1]
lake=shutil.which('lake');lean=shutil.which('lean')
if args.project is None or lake is None:
    print(json.dumps({'status':'NOT_RUN','reason':'provide --project and an available lake executable',
                      'lean_found':lean,'lake_found':lake},indent=2));sys.exit(2)
file=root/'lean'/'CertificatePrinciples.lean'
r=subprocess.run([lake,'env','lean',str(file)],cwd=args.project,capture_output=True,text=True,timeout=180)
print(r.stdout,end='');print(r.stderr,end='',file=sys.stderr)
print(json.dumps({'status':'ELABORATED' if r.returncode==0 else 'FAILED','returncode':r.returncode}))
sys.exit(r.returncode)
