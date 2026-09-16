#!/usr/bin/env python3
"""Check least-index witnesses against exact inequalities, not the root search."""
import argparse,json,sys
from pathlib import Path
from fractions import Fraction as Q
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'prototype'))
from forge_analytic.tails import modulus,minimal_modulus
from forge_analytic.checker import verify
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,default=ROOT/'reproduced-moduli.json');args=p.parse_args()
certs=json.loads((ROOT/'results/run-01/certificates.json').read_text());receipts=[]
for id,c in certs.items():
    if c['kind']!='barrier':continue
    assert verify(c['subject'],c)
    for eps in (Q(1,10),Q(1,1000),Q(7,19),Q(9,2)):
        k=minimal_modulus(c,eps);K=modulus(c,eps)
        C,sh,power=Q(c['constant']),c['shift'],c['power']
        assert c['cutoff']<=k<=K and C<eps*(k+sh)**power
        assert k==c['cutoff'] or C>=eps*(k-1+sh)**power
        receipts.append({'id':id,'epsilon':str(eps),'least_index':k,'coarse_index':K})
result={'checked_witnesses':len(receipts),'strictly_improved':sum(r['least_index']<r['coarse_index'] for r in receipts),
        'receipts':receipts,'evidence':'Exact rational witness checks; not Lean replay'}
args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='receipts'},indent=2))
