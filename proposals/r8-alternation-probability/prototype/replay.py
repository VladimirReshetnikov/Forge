#!/usr/bin/env python3
"""Replay a stored corpus while actively forbidding proposer imports.
Usage: python -S replay.py ../results/corpus.json
"""
import argparse, importlib.abc, json, sys, time
from pathlib import Path
from collections import Counter
class NoSearch(importlib.abc.MetaPathFinder):
    def find_spec(self, fullname, path=None, target=None):
        if fullname=='forge_ap.search' or fullname.startswith('tests'):
            raise ImportError('Search and oracle imports forbidden in replay')
        return None
sys.meta_path.insert(0,NoSearch())
from forge_ap.models import load_json
from forge_ap.check import check_record

def main():
    ap=argparse.ArgumentParser();ap.add_argument('corpus');ap.add_argument('--receipt');args=ap.parse_args()
    start=time.perf_counter();records=load_json(Path(args.corpus).read_text());counts=Counter()
    for rec in records:
        check_record(rec);counts[rec['problem']['kind']]+=1
    assert 'forge_ap.search' not in sys.modules
    receipt={'status':'PASS','records_by_kind':dict(counts),'search_imports':'FORBIDDEN',
             'site_packages_enabled':not bool(sys.flags.no_site),'elapsed_seconds':time.perf_counter()-start,
             'lean_kernel_checked':False}
    text=json.dumps(receipt,indent=2)+'\n';print(text,end='')
    if args.receipt:Path(args.receipt).write_text(text)
if __name__=='__main__':main()
