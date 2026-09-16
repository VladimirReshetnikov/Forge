#!/usr/bin/env python3
"""Small mechanism ablations, not comparisons with Lean tactics."""
from fractions import Fraction as Q
import argparse, json
from pathlib import Path
from forge_unbounded.model import PPS, Term, encq, subject
from forge_unbounded.search import pps_enclosure, critical_extinction, evaluate, floor_dyadic
from forge_unbounded.verify import verify


def main():
    import sys
    if sys.flags.optimize:
        raise SystemExit('Run without -O: experiment assertions must remain enabled.')
    ap=argparse.ArgumentParser()
    ap.add_argument('--out', required=True, type=Path)
    args=ap.parse_args()
    args.out.mkdir(parents=True, exist_ok=False)
    critical=PPS(((Term(Q(1,2),(0,)),Term(Q(1,2),(2,))),))
    lo=Q(0); ledger=[]
    for _ in range(256):
        lo=floor_dyadic(evaluate(critical,[lo])[0],40)
        ledger.append({'kind':'kleene','next':[encq(lo)]})
    k={'kind':'enclosure','subject':subject(critical),'ledger':ledger,
       'lower':[encq(lo)],'upper':[[1,1]],'requested_bits':20,
       'target_met':1-lo<=Q(1,1<<20)}
    n=pps_enclosure(critical,target_bits=20,rounding_bits=40)
    s=critical_extinction(critical)
    assert verify(critical,k) and verify(critical,n) and verify(critical,s)
    assert not k['target_met'] and n['target_met'] and len(n['ledger'])==20
    assert 'contraction' not in n
    cubic=PPS(((Term(Q(1,4),(0,)),Term(Q(3,4),(3,))),))
    c=pps_enclosure(cubic,target_bits=24,rounding_bits=44)
    assert verify(cubic,c) and 'contraction' in c
    records=[{'name':name,'problem':p.data(),'certificate':cert}
             for name,p,cert in [('critical-kleene256',critical,k),
              ('critical-newton20',critical,n),('critical-spectral',critical,s),
              ('cubic-local-contraction',cubic,c)]]
    (args.out/'certificates.jsonl').write_text(''.join(json.dumps(x,sort_keys=True)+'\n' for x in records))
    (args.out/'rejections.jsonl').write_text('')
    result={'status':'PASSED','comparison':'restricted internal mechanisms, not Lean tactics',
      'critical':{'kleene_steps':256,'kleene_error':encq(1-lo),
         'kleene_20_bits_met':False,'newton_steps':len(n['ledger']),
         'newton_error':encq(Q(1)-Q(*n['lower'][0])),
         'newton_20_bits_met':True,'strict_contraction_available':False,
         'spectral_answer':'q=1'},
      'cubic':{'global_derivative_at_one':[9,4], 'local_contraction_checked':True,
         'newton_steps':len(c['ledger']),'lower':c['lower'],'upper':c['upper'],
         'rho':c['contraction']['rho']},
      'accepted_receipts':len(records)}
    (args.out/'summary.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()
