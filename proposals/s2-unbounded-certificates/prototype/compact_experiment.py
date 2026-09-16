#!/usr/bin/env python3
"""Replay-preserving inverse-free certificate conversion and negative controls."""
from copy import deepcopy
from pathlib import Path
from fractions import Fraction as Q
import argparse,json
from forge_unbounded.model import parse_problem,encq
from forge_unbounded.compact import compact_enclosure
from forge_unbounded.verify import verify


def size(x): return len(json.dumps(x,sort_keys=True,separators=(',',':')).encode())

def main():
    import sys
    if sys.flags.optimize:
        raise SystemExit('Run without -O: experiment assertions must remain enabled.')
    ap=argparse.ArgumentParser();ap.add_argument('source',type=Path)
    ap.add_argument('--out',required=True,type=Path);a=ap.parse_args()
    a.out.mkdir(parents=True,exist_ok=False)
    records=[];rejects=[];sizes=[];steps=0
    for line in (a.source/'certificates.jsonl').read_text().splitlines():
        r=json.loads(line);c=r['certificate']
        if c['kind']!='enclosure' or not any(s['kind']=='newton' for s in c['ledger']): continue
        p=parse_problem(r['problem']);d=compact_enclosure(p,c)
        assert verify(p,d)
        records.append({'name':r['name']+'-compact','problem':p.data(),'certificate':d})
        sizes.append({'name':r['name'],'dimension':p.d,'original_bytes':size(c),'compact_bytes':size(d)})
        steps+=sum(s['kind']=='weighted_newton' for s in d['ledger'])
        for field in ['weight','direction']:
            bad=deepcopy(d)
            step=next(s for s in bad['ledger'] if s['kind']=='weighted_newton')
            if field=='weight':step[field][0]=[0,1]
            else:step[field][0]=[-1,1]
            assert not verify(p,bad)
            rejects.append({'name':r['name']+'-invalid-'+field,'problem':p.data(),'certificate':bad})
    # Critical P=x: equality Jw=w is not a valid strict weighted-Newton step.
    from forge_unbounded.model import PPS,Term,subject
    p=PPS(((Term(Q(1),(1,)),),))
    bad={'kind':'enclosure','subject':subject(p),
        'ledger':[{'kind':'weighted_newton','weight':[[1,1]],'direction':[[1,1]],'next':[[1,1]]}],
        'lower':[[1,1]],'upper':[[1,1]],'requested_bits':20,'target_met':True}
    assert not verify(p,bad)
    rejects.append({'name':'nonstrict-weight-is-unsound','problem':p.data(),'certificate':bad})
    for name,xs in [('certificates.jsonl',records),('rejections.jsonl',rejects)]:
        (a.out/name).write_text(''.join(json.dumps(x,sort_keys=True)+'\n' for x in xs))
    (a.out/'sizes.json').write_text(json.dumps(sizes,indent=2)+'\n')
    result={'status':'PASSED','converted_enclosures':len(records),'weighted_steps':steps,
        'negative_controls':len(rejects),
        'new_unique_source_problems':False,
        'original_total_bytes':sum(s['original_bytes'] for s in sizes),
        'compact_total_bytes':sum(s['compact_bytes'] for s in sizes),
        'dimensions':{str(d):{'original':sum(s['original_bytes'] for s in sizes if s['dimension']==d),
            'compact':sum(s['compact_bytes'] for s in sizes if s['dimension']==d)} for d in sorted(set(s['dimension'] for s in sizes))}}
    (a.out/'summary.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
