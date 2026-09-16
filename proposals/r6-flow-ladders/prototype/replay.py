#!/usr/bin/env python3
"""Replay saved certificates with python -S. Does not import discovery modules."""
import argparse,json,sys
from collections import Counter
from forge_flow.check import check_ladder,check_system,check_obstruction,check_minimality
from forge_flow.enclosure import check_refutation,check_root

def main():
    ap=argparse.ArgumentParser();ap.add_argument('path',nargs='?',default='../results/accepted/certificates.json')
    args=ap.parse_args();rows=json.load(open(args.path));counts=Counter()
    for row in rows:
        lane=row['lane'];c=row['certificate']
        if lane=='positive':ok=check_ladder(row['problem'],c) and check_minimality(row['problem'],c,row['minimality'])
        elif lane=='system':ok=check_system(row['problems'],c)
        elif lane=='negative_point':ok=check_refutation(row['problem'],c) and check_obstruction(row['problem'],row['grammar_obstruction'])
        elif lane=='grammar_obstruction':ok=check_obstruction(row['problem'],c)
        elif lane=='root':ok=check_root(row['problem'],c)
        else:raise ValueError('unknown lane')
        if not ok:raise AssertionError(row['id'])
        counts[lane]+=1
    assert 'forge_flow.search' not in sys.modules and 'forge_flow.witness_search' not in sys.modules
    print(json.dumps({'replayed':dict(counts),'discovery_modules_loaded':False},indent=2))

if __name__=='__main__':main()
