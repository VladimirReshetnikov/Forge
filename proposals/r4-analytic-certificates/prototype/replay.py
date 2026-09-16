#!/usr/bin/env python3
"""Check stored receipts without invoking or importing any proposer."""
import argparse, json, sys
from pathlib import Path
from forge_analytic.check import verify_goal

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--results',type=Path,default=Path('../results'))
    args=ap.parse_args()
    problems=json.loads((args.results/'problems.json').read_text())
    receipts=json.loads((args.results/'certificates.json').read_text())
    seen=set()
    for record in receipts:
        name=record['problem_id']
        if name in seen or name not in problems or not verify_goal(problems[name],record['certificate']):
            raise SystemExit('REJECT: '+name)
        seen.add(name)
    if seen!=set(problems): raise SystemExit('Missing certificate(s)')
    assert 'forge_analytic.search' not in sys.modules
    print(json.dumps({'accepted':len(seen),'search_imported':False,
        'site_packages_disabled':sys.flags.no_site==1,'kernel_checked':False},indent=2))

if __name__=='__main__':main()
