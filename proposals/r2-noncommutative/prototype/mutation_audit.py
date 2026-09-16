#!/usr/bin/env python3
"""Targeted falsifying mutations, with unchanged external problem where possible.
Not arbitrary fuzz: every listed mutation is intended to destroy the receipt.
"""
import copy,json
from pathlib import Path
from ncforge.checker import load_json,verify
entries=load_json('../results/certificates.json'); attempts=[]
for e in entries:
    p=e['problem']; c=e['certificate']; name=e['name']
    if c['kind']=='matrix_countermodel':
        z=copy.deepcopy(c);z['vector']=[[0,1] for _ in z['vector']]
        attempts.append((name,'zero_separating_vector',p,z))
    else:
        # A valid certificate for p cannot also certify p+1. For operator/trace,
        # p+1 may be true, but this exact unmodified certificate does not prove it.
        p2=copy.deepcopy(p);ts=p2['target']
        if ts and ts[0][0]==[]:
            a,b=ts[0][1:];a+=b
            if a: ts[0]=[[],a,b]
            else: ts.pop(0)
        else: ts.insert(0,[[],1,1])
        attempts.append((name,'different_original_target',p2,c))
    if c.get('ideal'):
        z=copy.deepcopy(c);z['ideal'][0]['weight']=[0,1]
        attempts.append((name,'delete_nonzero_ideal_contribution',p,z))
    if c.get('squares'):
        z=copy.deepcopy(c);z['squares'][0]['weight']=[-1,1]
        attempts.append((name,'negative_square_weight',p,z))
accepted=[]; details=[]
for name,mutation,p,c in attempts:
    ans=verify(p,c);details.append({'name':name,'mutation':mutation,'accepted':ans['accepted']})
    if ans['accepted']:accepted.append((name,mutation))
result={'mutation_attempts':len(attempts),'incorrectly_accepted':accepted,'details':details}
Path('../results/mutations.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='details'},indent=2))
raise SystemExit(bool(accepted))
