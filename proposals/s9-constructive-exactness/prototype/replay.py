#!/usr/bin/env python3
"""Replay receipts without the search dependency: python -S replay.py."""
from pathlib import Path
import argparse, json, sys
from exactness.checker import check, strict_loads

def main() -> int:
    ap=argparse.ArgumentParser(); ap.add_argument('path',nargs='?',default='../results/recorded/corpus.json')
    args=ap.parse_args(); path=Path(args.path)
    if path.stat().st_size>64*1024*1024: raise ValueError('receipt file too large')
    cases=strict_loads(path.read_text()); counts={}
    for case in cases:
        result=check(case['problem'],case['certificate'])
        if result['kind']!=case['expected']: raise ValueError(f"wrong outcome: {case['name']}")
        counts[result['kind']]=counts.get(result['kind'],0)+1
    if 'sympy' in sys.modules: raise RuntimeError('replay imported SymPy')
    print(json.dumps(dict(accepted=len(cases),outcomes=counts,search_imported=False),indent=2))
    return 0
if __name__=='__main__': raise SystemExit(main())
