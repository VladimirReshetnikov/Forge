#!/usr/bin/env python3
"""Replay saved artifacts with the checker alone; forbid producer imports."""
from __future__ import annotations
import argparse, importlib.abc, json, sys
from pathlib import Path

class DenySearch(importlib.abc.MetaPathFinder):
    def find_spec(self,fullname,path=None,target=None):
        if fullname in {'forgeq.search','oracles'} or fullname.split('.')[0] in {'numpy','scipy','sympy'}:
            raise ImportError('replay must not import search or oracle: '+fullname)
        return None
sys.meta_path.insert(0,DenySearch())
from forgeq.checker import audit, loads

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--results',type=Path,default=Path('../results'))
    a=p.parse_args()
    records=loads((a.results/'certificates.json').read_text())
    byid={r['id']:r for r in records}
    accepted=0
    for r in records:
        result=audit(r['worker'],r['problem'],r['certificate'])
        if not result['accepted'] or result!=r['audit']:
            raise RuntimeError(('certificate replay mismatch',r['id'],result))
        accepted+=1
    rejected=0
    for m in loads((a.results/'mutations.json').read_text()):
        original=byid[m['source']]
        result=audit(m['worker'],original['problem'],m['certificate'])
        if result['accepted']:raise RuntimeError(('mutation accepted',m['source']))
        rejected+=1
    print(json.dumps({'accepted_certificates':accepted,'rejected_mutations':rejected,
        'producer_and_oracle_imports':'forbidden','site_packages':not sys.flags.no_site,
        'kernel_proof_claim':False},indent=2))
if __name__=='__main__':main()
