#!/usr/bin/env python3
"""Replay stored positive/refutation certificates with all search imports blocked."""
import argparse,importlib.abc,json,sys
from pathlib import Path
class NoSearch(importlib.abc.MetaPathFinder):
    def find_spec(self,fullname,path=None,target=None):
        if fullname in {'forge_delta.poly_search','forge_delta.nc_search','forge_delta.analytic_search','forge_delta.poly_witness'}:
            raise ImportError('Search or witness-proposal code is forbidden in replay')
sys.meta_path.insert(0,NoSearch())
from forge_delta.poly_check import check as poly
from forge_delta.nc_check import check as nc
from forge_delta.analytic_check import check as analytic

def no_duplicates(pairs):
    out={}
    for k,v in pairs:
        if k in out: raise ValueError('Duplicate JSON key: '+k)
        out[k]=v
    return out

def verify(path):
    records=json.loads(path.read_text(),object_pairs_hook=no_duplicates)
    if isinstance(records,dict) and 'results' in records:
        records=[dict(r,lane='analytic') for r in records['results']]
    counts={}
    for r in records:
        c=r['certificate'];lane=r['lane']
        expected=c['kind']!='unknown'
        actual={'poly':poly,'nc':nc,'analytic':analytic}[lane](r['problem'],c)
        if actual!=expected: raise AssertionError((lane,r['name'],actual,expected))
        kind='accepted' if actual else 'unknown-not-accepted'
        counts.setdefault(lane,{});counts[lane][kind]=counts[lane].get(kind,0)+1
    return counts
if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('path',nargs='?',type=Path,default=Path(__file__).resolve().parent.parent/'results/certificates.json')
    a=parser.parse_args();print(json.dumps(verify(a.path),indent=2))
