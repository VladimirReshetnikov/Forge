#!/usr/bin/env python3
"""Replay pinned certificates without importing search or third-party modules."""
from __future__ import annotations
import argparse, builtins, json, sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'prototype'))
original_import=builtins.__import__
def guarded_import(name,globals=None,locals=None,fromlist=(),level=0):
    forbidden=('sympy','numpy','scipy','mpmath','forge_analytic.algebra','forge_analytic.jets',
               'forge_analytic.ladders','forge_analytic.tails')
    if any(name==x or name.startswith(x+'.') for x in forbidden):
        raise RuntimeError('Search or optional library imported during replay: '+name)
    if level and name in ('algebra','jets','ladders','tails'):
        raise RuntimeError('Relative search import during replay')
    return original_import(name,globals,locals,fromlist,level)
builtins.__import__=guarded_import
from forge_analytic.checker import verify, loads

def main():
    p=argparse.ArgumentParser();p.add_argument('directory',nargs='?',type=Path,default=ROOT/'results/run-01')
    args=p.parse_args()
    problems=loads((args.directory/'problems.json').read_text())
    certificates=loads((args.directory/'certificates.json').read_text())
    if set(problems)!=set(certificates): raise SystemExit('Problem/certificate inventory mismatch')
    kinds={}
    for key,problem in problems.items():
        cert=certificates[key]
        if cert.get('kind')!=problem['expected_kind'] or not verify(problem['subject'],cert):
            raise SystemExit('Rejected: '+key)
        kinds[cert['kind']]=kinds.get(cert['kind'],0)+1
    print(json.dumps({'accepted_records':len(certificates),'kinds':kinds,
          'site_disabled':bool(sys.flags.no_site),'search_imports_blocked':True,
          'evidence':'Python certificate replay; not a Lean-kernel proof'},indent=2))
if __name__=='__main__':main()
