#!/usr/bin/env python3
"""Replay saved certificates under `python -S`; imports no search engines."""
import argparse, sys
from pathlib import Path
from collections import Counter
from forge_horizon.codec import loads,unpack_model
from forge_horizon.models import PDS,Game,Chain
from forge_horizon.checkers import check_pds,check_game,check_chain

def main():
    ap=argparse.ArgumentParser();ap.add_argument('path',nargs='?',type=Path,
        default=Path(__file__).resolve().parents[1]/'results'/'certificates.json')
    args=ap.parse_args();counts=Counter()
    forbidden_names={'forge_horizon.pushdown','forge_horizon.games','forge_horizon.markov'}
    if forbidden_names.intersection(sys.modules):
        raise RuntimeError('search module imported before replay')
    records=loads(args.path.read_text())
    for rec in records:
        m=unpack_model(rec['problem']);cert=rec['certificate']
        if isinstance(m,PDS):ans=check_pds(m,cert)
        elif isinstance(m,Game):ans=check_game(m,cert,rec['start'])
        elif isinstance(m,Chain):ans=check_chain(m,cert)
        else:raise TypeError(type(m))
        if ans!=rec['expected']:raise ValueError('changed certificate interpretation')
        counts[ans['outcome']]+=1
    forbidden=[x for x in sys.modules if x in {'forge_horizon.pushdown','forge_horizon.games','forge_horizon.markov'}]
    if forbidden:raise RuntimeError('search module imported during replay')
    print(f'Replayed {len(records)} records; no search modules imported.')
    print(dict(counts))
if __name__=='__main__':main()
