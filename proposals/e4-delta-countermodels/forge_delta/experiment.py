"""Reproduce the self-contained synthetic experiment without overwriting evidence."""
from __future__ import annotations
import argparse
from collections import Counter
from dataclasses import asdict
from datetime import datetime,timezone
import csv,json,platform,shutil,sys
from pathlib import Path
from statistics import median
from time import perf_counter
import sympy
from .cases import machine_cases,logical_cases,SEED
from .search import solve,conserved_target_only
from .checker import verify_positive,verify_negative
from .kripke import find_countermodel,verify_countermodel


def run(output:Path,repeats:int=3):
    if repeats<1:raise ValueError('repeats must be positive')
    if output.exists() and any(output.iterdir()):raise FileExistsError(f'refusing to overwrite nonempty {output}')
    output.mkdir(parents=True,exist_ok=True)
    rows=[];corpus=[];trials=[];machines=machine_cases()
    start=perf_counter()
    for family,cases in [('machine',machines),('IPC',logical_cases())]:
        for c in cases:
            samples=[];checks=[];result=None
            for trial in range(repeats):
                if family=='machine':r=solve(c['problem'],c['limits'])
                else:r=find_countermodel(c['problem'])
                assert r['status']==c['expected'],c['name']
                samples.append(r['stats']['elapsed_seconds'])
                t=perf_counter()
                if r['status']=='proved':valid=verify_positive(c['problem'],r['certificate'])
                elif r['status']=='refuted':valid=verify_negative(c['problem'],r['certificate'])
                elif r['status']=='ipc_countermodel':valid=verify_countermodel(c['problem'],r['certificate'])
                else:valid=None
                checks.append(perf_counter()-t if valid is not None else None)
                assert valid is not False
                if result is not None:
                    assert result.get('certificate')==r.get('certificate'),'nondeterministic certificate'
                result=r
            certificate=result.get('certificate')
            row={'family':family,'case':c['name'],'generator_family':c.get('family','logical'),
                 'status':result['status'],'median_search_seconds':median(samples),
                 'median_replay_seconds':median(v for v in checks if v is not None) if certificate else '',
                 'certificate_bytes':len(json.dumps(certificate,sort_keys=True,separators=(',',':')).encode()) if certificate else 0,
                 'basis_dimension':sum(result['stats'].get('basis_dimensions',[])),
                 'worlds':certificate.get('worlds','') if certificate else '',
                 'trace_length':len(certificate['steps']) if certificate and 'steps' in certificate else '',
                 'conserved_target_only':conserved_target_only(c['problem']) if family=='machine' else '',
                 'coefficient_obligations':result['stats'].get('coefficient_obligations',''),
                 'models':result['stats'].get('models','')}
            rows.append(row)
            item={'name':c['name'],'family':family,'problem':c['problem'],'expected':c['expected'],
                  'result':{k:v for k,v in result.items() if k != 'stats'}}
            trials.append({'name':c['name'],'stats':result['stats'],
                           'search_seconds':samples,'replay_seconds':checks})
            if family=='machine':item['limits']=asdict(c['limits'])
            else:item['limits']={'max_worlds':3,'max_models':200000}
            corpus.append(item)
    write=lambda name,obj:(output/name).write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')
    write('corpus.json',corpus)
    write('trials.json',trials)
    with (output/'measurements.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
    counts={f:dict(Counter(r['status'] for r in rows if r['family']==f)) for f in ['machine','IPC']}
    summary={'schema_version':1,'seed':SEED,'repeats':repeats,'case_counts':counts,
             'conserved_target_only_proved':sum(r['conserved_target_only'] is True for r in rows),
             'machine_positive_count':counts['machine'].get('proved',0),
             'certificates':sum('certificate' in c['result'] for c in corpus),
             'median_of_case_medians_seconds':{
                 f:median(r['median_search_seconds'] for r in rows if r['family']==f) for f in ['machine','IPC']},
             'maximum_certificate_bytes':max(r['certificate_bytes'] for r in rows),
             'total_experiment_seconds':perf_counter()-start,
             'claims':{'Lean_compiled':False,'installed_forge_tactic':False,'comparison_with_grind':False,
                       'synthetic_cases_only':True,'checker_formally_verified':False}}
    write('summary.json',summary)
    environment={'recorded_at_utc':datetime.now(timezone.utc).isoformat(),
                 'python':sys.version,'sympy':sympy.__version__,'platform':platform.platform(),
                 'lean_executable':shutil.which('lean'),'lake_executable':shutil.which('lake'),
                 'elan_executable':shutil.which('elan'),
                 'command':'python -m forge_delta.experiment --output '+str(output)+' --repeats '+str(repeats)}
    write('environment.json',environment)
    print(json.dumps(summary,indent=2))

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,default=Path('reproduced-results'))
    ap.add_argument('--repeats',type=int,default=3)
    args=ap.parse_args();run(args.output,args.repeats)
