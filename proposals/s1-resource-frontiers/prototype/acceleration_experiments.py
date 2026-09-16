#!/usr/bin/env python3
"""Ablate exact productive-transition acceleration, not a Lean tactic benchmark."""
import argparse,json,random
from pathlib import Path
from forge_resources.examples import problem
from forge_resources.producer import frontier
from forge_resources.checker import check_frontier


def main(out):
    out.mkdir(parents=True,exist_ok=True);rng=random.Random(41027)
    records=[];rows=[]
    for i in range(24):
        d=1+i%3;ts=[]
        for j in range(3):
            c=[rng.randrange(3) for _ in range(d)];p=[ci+rng.randrange(4) for ci in c]
            ts.append((f't{j}',c,p))
        p=problem(d,ts,[[rng.randrange(13) for _ in range(d)]])
        ordinary=frontier(p);fast=frontier(p,accelerate=True)
        assert ordinary['status']==fast['status']=='CERTIFICATE'
        a=check_frontier(p,ordinary['certificate']);b=check_frontier(p,fast['certificate'])
        assert a['basis']==b['basis']
        records.append({'name':f'productive_{i:02}','expected':p,'certificate':fast['certificate']})
        rows.append({'case':f'productive_{i:02}','primitive':ordinary['stats'],'accelerated':fast['stats']})
    stress=[]
    for power in (4,6,100):
        target=10**power;p=problem(1,[('add_one',[0],[1])],[[target]])
        ordinary=frontier(p,max_candidates=100,max_insertions=200)
        fast=frontier(p,max_candidates=100,max_insertions=200,accelerate=True)
        assert ordinary['status']=='UNKNOWN' and fast['status']=='CERTIFICATE'
        checked=check_frontier(p,fast['certificate']);assert checked['basis']==[[0]]
        records.append({'name':f'power_threshold_10_to_{power}','expected':p,'certificate':fast['certificate']})
        stress.append({'target':str(target),'candidate_budget':100,'primitive_status':ordinary['status'],
                       'primitive_candidates':ordinary['stats']['candidates'],'accelerated_status':fast['status'],
                       'accelerated_candidates':fast['stats']['candidates'],'certificate_nodes':checked['run_nodes']})
    (out/'accelerated-frontiers.jsonl').write_text(''.join(json.dumps(r,sort_keys=True)+'\n' for r in records))
    (out/'acceleration-costs.json').write_text(json.dumps(rows,indent=2)+'\n')
    summary={'seed':41027,'small_productive_cases':24,'frontier_disagreements':0,
             'primitive_small_candidates':sum(r['primitive']['candidates'] for r in rows),
             'accelerated_small_candidates':sum(r['accelerated']['candidates'] for r in rows),
             'stress':stress,'records':len(records),'meaning':'same checker and original net; exact power acceleration'}
    (out/'acceleration-summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,default=Path('reproduced-results'))
    main(p.parse_args().out)
