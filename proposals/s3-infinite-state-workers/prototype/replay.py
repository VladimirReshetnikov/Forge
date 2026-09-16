"""Replay the stored corpus with ONLY checker.py, without loading search modules."""
from pathlib import Path
import argparse,sys
import checker

ap=argparse.ArgumentParser()
ap.add_argument('corpus',nargs='?',type=Path,default=Path(__file__).resolve().parents[1]/'results/corpus.json')
args=ap.parse_args()
corpus=checker.load_json(args.corpus.read_text())
counts={}
for entry in corpus:
    engine,p,c=entry['engine'],entry['problem'],entry['certificate']
    ok=checker.check_vass(p,c) if engine=='vass' else (checker.check_mixed(p,c) if engine=='mixed' else checker.check_nominal(*p,c))
    if not ok:raise SystemExit('REJECTED: '+entry['name'])
    counts[engine]=counts.get(engine,0)+1
assert not any(m in sys.modules for m in ['antichain','nominal','mixed','fixtures','oracles'])
print('ACCEPTED',len(corpus),'stored objects:',counts)
print('Producer and oracle modules were not imported. This is Python checking, not Lean checking.')
