#!/usr/bin/env python3
"""Replay saved successful artifacts without importing search/numerical libraries.

The JSON statement is the statement being checked, not a trusted original Lean
statement. A Lean adapter must bind these records to the actual elaborated goal.
"""
from fractions import Fraction as Q
from pathlib import Path
import json,sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'prototype'))
from forge_cert.poly import decode,verify_cone,verify_bernstein
from forge_cert.induction import verify_bundle
from forge_cert.cdclt import verify_sat,verify_unsat
from forge_cert.witness import verify as verify_witness

def main():
    records=json.loads((ROOT/'results'/'certificates.json').read_text())
    for r in records:
        family=r['family']
        if family in ('cone','quadratic'):
            n=r['n'];ok=verify_cone(decode(r['target'],n),[decode(x,n) for x in r['inequalities']],
                [decode(x,n) for x in r['equalities']],r['certificate'],n)
        elif family=='bernstein':
            n=r['n'];ok=verify_bernstein(decode(r['target'],n),[(Q(a),Q(b)) for a,b in r['box']],r['certificate'],n)
        elif family in ('induction','lemma_synthesis'):
            required=[r['id']] if family=='induction' else ['app_right_id','app_assoc','rev_app']
            ok=verify_bundle(r['records'],required=required)
        elif family in ('cdclt_random','pigeonhole'):
            atoms={int(k):v for k,v in r['atoms'].items()}
            check=verify_sat if r['result']['status']=='sat' else verify_unsat
            ok=check(r['cnf'],atoms,r['nodes'],r['result'])
        elif family=='witness':ok=verify_witness(r['a'],r['b'],r['m'],r['certificate'])
        else:raise ValueError('unrecognized artifact family')
        if not ok:raise AssertionError(f'Replay rejected {family}/{r["id"]}')
    print(f'{len(records)} saved artifacts replayed successfully using standard-library-only checkers.')
    print('This is object-level/exact Python replay, not Lean kernel verification.')
if __name__=='__main__':main()
