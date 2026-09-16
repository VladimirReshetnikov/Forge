#!/usr/bin/env python3
"""Replay every stored object without third-party or producer imports.

  python -S prototype/bin/replay.py results/run-02

Outputs distinct evidence categories, never a combined 'number of proofs'.
"""
from pathlib import Path
import sys,builtins,json,argparse,time
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
original_import=builtins.__import__
def guarded_import(name,*args,**kwargs):
    if name.split('.')[0] in ('sympy','numpy','flint') or name.split('.')[-1]=='producer':
        raise ImportError('Replay attempted a forbidden search import: '+name)
    return original_import(name,*args,**kwargs)
builtins.__import__=guarded_import
from fractions import Fraction as Q
from itertools import product
from real_fibers.checker import verify,check_charpoly
from real_fibers.outer import verify_outer
from real_fibers.witness import verify_witness
from real_fibers.logic import indicator,eval_formula
from real_fibers.exact import P,Reject,rat,poly,sgn,signature_from_signs

def unique_keys(pairs):
    d={}
    for k,v in pairs:
        if k in d:raise Reject('duplicate JSON key')
        d[k]=v
    return d

def read(path):return json.loads(path.read_text(),object_pairs_hook=unique_keys)

def main():
    pa=argparse.ArgumentParser();pa.add_argument('run',type=Path);args=pa.parse_args();run=args.run
    start=time.perf_counter();counts={'valid_bundles':0,'specialization_evaluations':0,'invalid_mutations_rejected':0,
                                   'boolean_formulas':0,'boolean_truth_assignments':0,'signature_matrices':0}
    for path in sorted((run/'certificates').glob('*.json')):
        b=read(path);kind=b['kind'];p,c=b['problem'],b['certificate']
        if kind=='outer':
            v=verify_outer(p,c);assert v.value==b['expected'];assert v.cells==b['cells']
            cf=verify(p['fiber'],c['fiber_certificate'])
        elif kind=='fiber':cf=verify(p,c)
        elif kind=='witness':
            v=verify_witness(p,c);assert v['atom_signs']==b['expected_signs'];cf=None
        else:raise Reject('unknown bundle type')
        for row in b.get('specializations',[]):
            assert cf.count([rat(a) for a in row['parameters']])==row['count'];counts['specialization_evaluations']+=1
        counts['valid_bundles']+=1
    for b in read(run/'mutations.json'):
        try:{'outer':verify_outer,'fiber':verify,'witness':verify_witness}[b['kind']](b['problem'],b['certificate'])
        except Reject:counts['invalid_mutations_rejected']+=1
        else:raise AssertionError('Invalid mutation accepted: '+b['name']+' '+b['mutation'])
    for b in read(run/'boolean-fixtures.json'):
        p=poly(b['indicator'],b['m']);assert p==indicator(b['formula'],b['m'])
        for signs in product((-1,0,1),repeat=b['m']):
            assert p.eval(signs)==int(eval_formula(b['formula'],signs));counts['boolean_truth_assignments']+=1
        counts['boolean_formulas']+=1
    for b in read(run/'signature-fixtures.json'):
        ds=b['diagonal'];T=b['unit_lower_triangular'];H=b['hermite'];cs=b['charpoly'];d=len(ds)
        assert all(T[i][i]==1 for i in range(d))
        assert all(T[i][j]==0 for i in range(d) for j in range(i+1,d))
        assert H==[[sum(T[k][i]*ds[k]*T[k][j] for k in range(d)) for j in range(d)] for i in range(d)]
        check_charpoly([[P.const(0,a) for a in row] for row in H],[P.const(0,a) for a in cs])
        assert signature_from_signs([sgn(a) for a in cs])==sum(sgn(a) for a in ds)==b['expected_signature']
        counts['signature_matrices']+=1
    print(json.dumps({'status':'PASS','site_packages_enabled':bool(sys.flags.no_site==0),
                     'forbidden_imports':'sympy,numpy,flint,producer','counts':counts,
                     'elapsed_seconds':time.perf_counter()-start},indent=2))
if __name__=='__main__':main()
