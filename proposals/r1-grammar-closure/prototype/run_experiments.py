"""Reproduce and persist certificates, differential evidence and isolated replay.

Default output is ../reproduced-results, never the archived ../results.
Run: python -S run_experiments.py
"""
from __future__ import annotations
import argparse
from collections import Counter
import copy
import json
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import tempfile
import time
import unittest

import compilers as c
import search as s
import checker
from tests import random_acyclic, finite_truth, finite_paired_observations, mutation_cases


def write(path,obj):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parent.parent/'reproduced-results')
    args=parser.parse_args();out=args.output.resolve();out.mkdir(parents=True,exist_ok=True)
    root=Path(__file__).resolve().parent
    records=[]
    fixtures=[('tree_identity',c.leaf_count(),False),('balanced_dyck',c.dyck(),False),
              ('bad_return',c.dyck(True),False),('noncommuting_order',c.noncommuting_control(),False),
              ('exponential_60',c.exponential_word(60),False),
              ('noisy_tree_quotient',c.leaf_count(True),True),
              ('zero_observation_quotient',c.leaf_count(),True)]
    unrestricted=c.cfg('unrestricted_letters',['S'],
        {'a':[[1,1],[0,1]],'b':[[1,-1],[0,1]]},
        [{'lhs':'S','rhs':[]},{'lhs':'S','rhs':['n:S','t:a']},
         {'lhs':'S','rhs':['n:S','t:b']}],[{'sort':'S','q':['0','1','0','0']}])
    fixtures.append(('drop_language_restriction',unrestricted,False))
    for label,p,minimize in fixtures:
        t=time.perf_counter();r=s.minimize(p) if minimize else s.saturate(p)
        producer_seconds=time.perf_counter()-t
        t=time.perf_counter();receipt=checker.verify(p,r['certificate']);replay_seconds=time.perf_counter()-t
        if not receipt['accepted']:raise AssertionError(receipt)
        write(out/'fixtures'/f'{label}.problem.json',p)
        write(out/'fixtures'/f'{label}.certificate.json',r['certificate'])
        record={'name':label,'producer_status':r['status'],'producer_stats':r['stats'],
                'replay':receipt,'producer_seconds_single_run':producer_seconds,
                'replay_seconds_single_run':replay_seconds,
                'certificate_bytes':len(json.dumps(r['certificate'],sort_keys=True).encode())}
        records.append(record)
    write(out/'fixtures.json',records)

    differential=[];counts=Counter()
    for seed in range(10000,10240):
        p=random_acyclic(seed);truth,size=finite_truth(p);r=s.saturate(p)
        receipt=checker.verify(p,r['certificate'])
        assert receipt['accepted'] and (r['status']=='PROVED')==truth
        counts[r['status']]+=1
        differential.append({'seed':seed,'exhaustive_valid':truth,'enumerated_distinct_values':size,
            'status':r['status'],'replay':receipt,'problem':p,'certificate':r['certificate']})
    write(out/'differential-cases.json',differential)

    quotient_records=[]
    for seed in range(20000,20040):
        p=random_acyclic(seed);r=s.minimize(p);receipt=checker.verify(p,r['certificate'])
        assert receipt['accepted']
        exact, pairs=finite_paired_observations(p,r['certificate']['model'])
        assert exact
        quotient_records.append({'seed':seed,'stats':r['stats'],'replay':receipt,
                                 'exhaustive_paired_observations_equal':exact,'observation_pairs_checked':pairs,
                                 'problem':p,'certificate':r['certificate']})
    write(out/'quotient-cases.json',quotient_records)

    mutations=[]
    for label,p,cert in mutation_cases():
        receipt=checker.verify(p,cert);assert not receipt['accepted']
        mutations.append({'name':label,'replay':receipt,'problem':p,'certificate':cert})
    write(out/'mutation-cases.json',mutations)

    quotas=[]
    for label,budget in [('candidate',s.Budget(max_candidates=0)),('basis',s.Budget(max_basis=0))]:
        r=s.saturate(c.leaf_count(),budget);assert r['status']=='UNKNOWN'
        quotas.append({'name':label,'result':r})
    p=c.exponential_word(10);p['source']['matrices']['a']=[['2']]
    p['operations'][0]['terms'][0]['q']='2'
    r=s.saturate(p,s.Budget(max_bits=64));assert r['status']=='UNKNOWN'
    quotas.append({'name':'exponential_coefficient_bits','result':r})
    write(out/'cutoffs.json',quotas)

    # Physically omit compilers.py, search.py, site packages, and current-dir
    # dependencies. The only executable source copied here is checker.py.
    isolated=[]
    with tempfile.TemporaryDirectory() as d:
        tmp=Path(d);shutil.copy2(root/'checker.py',tmp/'checker.py')
        for record in records:
            label=record['name']
            pp=out/'fixtures'/f'{label}.problem.json'
            cp=out/'fixtures'/f'{label}.certificate.json'
            proc=subprocess.run([sys.executable,'-I','-S',str(tmp/'checker.py'),str(pp),str(cp)],
                                 cwd=tmp,capture_output=True,text=True,timeout=30)
            assert proc.returncode==0,(proc.stdout,proc.stderr)
            isolated.append({'fixture':label,'returncode':proc.returncode,
                             'replay':json.loads(proc.stdout)})
    write(out/'isolated-replay.json',isolated)

    with (out/'unit-tests.log').open('w') as log:
        suite=unittest.defaultTestLoader.loadTestsFromName('tests')
        test_result=unittest.TextTestRunner(stream=log,verbosity=2).run(suite)
    assert test_result.wasSuccessful()
    env={'python':sys.version,'platform':platform.platform(),'implementation':platform.python_implementation(),
         'third_party_dependencies':[],
         'lean_executable':shutil.which('lean'),'lake_executable':shutil.which('lake'),
         'lean_status':'NOT_RUN: no Lean/lake executable in this environment',
         'no_comparison_against_lean_tactics':True}
    write(out/'environment.json',env)
    summary={'fixture_certificates':len(records),'isolated_replays_accepted':len(isolated),
             'unit_test_methods':test_result.testsRun,'unit_test_failures':len(test_result.failures),
             'unit_test_errors':len(test_result.errors),'differential_cases':len(differential),
             'differential_outcomes':dict(counts),'quotient_certificate_cases':len(quotient_records),
             'designed_invalid_objects_rejected':len(mutations),'quota_cases_unknown':len(quotas),
             'seed_ranges':{'differential':[10000,10239],'quotients':[20000,20039]},
             'units_are_distinct_do_not_sum':True}
    write(out/'summary.json',summary)
    print(json.dumps(summary,indent=2))

if __name__=='__main__':main()
