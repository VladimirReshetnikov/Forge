#!/usr/bin/env python3
"""Replay stored evidence, with no SymPy or other site packages required."""
from __future__ import annotations
import argparse,json,sys
from collections import Counter
from pathlib import Path
from forge_delta.checker import load_json,verify_positive,verify_negative
from forge_delta.kripke import verify_countermodel


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('corpus',nargs='?',type=Path,default=Path(__file__).parent/'results'/'corpus.json')
    args=ap.parse_args();items=load_json(args.corpus);counts=Counter()
    for item in items:
        p=item['problem'];r=item['result'];c=r.get('certificate');status=r['status']
        if status=='proved':ok=verify_positive(p,c)
        elif status=='refuted':ok=verify_negative(p,c)
        elif status=='ipc_countermodel':ok=verify_countermodel(p,c)
        elif status=='unknown':
            if c is not None:raise ValueError('unknown must not carry accepted certificate')
            counts['unknown_no_claim']+=1;continue
        else:raise ValueError('unsupported result status')
        if not ok:raise ValueError('replay rejected: '+item['name'])
        counts[status]+=1
    print(json.dumps({'replayed':dict(counts),'site_packages_loaded':
                     any(n in sys.modules for n in ['sympy','numpy','scipy','z3'])},indent=2))

if __name__=='__main__':main()
