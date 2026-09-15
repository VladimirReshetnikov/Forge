#!/usr/bin/env python3
"""Run a small, fresh-process Lean smoke comparison when Lake is installed.

This does NOT compare a completed Forge tactic against grind. There is no Forge
tactic implementation. It tests the 9 exported inequality contexts with existing
tactics, and separately checks the replay library. Compilation time is included.
Setup first: cd lean; lake update; lake exe cache get
"""
from __future__ import annotations
import argparse,json,shutil,subprocess,time
from pathlib import Path


def invoke(cmd,cwd,timeout):
    start=time.perf_counter()
    try:
        p=subprocess.run(cmd,cwd=cwd,timeout=timeout,text=True,capture_output=True)
        out=(p.stdout or '')+(p.stderr or '')
        # A nonzero exit includes elaboration/API errors, not only tactic failures.
        status='accepted' if p.returncode==0 else 'nonzero_exit'
        if 'declaration uses' in out and 'sorry' in out:
            status='rejected_admitted_proof'
        return {'status':status,'returncode':p.returncode,'seconds':time.perf_counter()-start,'output':out}
    except subprocess.TimeoutExpired as e:
        return {'status':'timeout','seconds':time.perf_counter()-start,
                'output':str(e.stdout or '')+str(e.stderr or '')}


def main():
    root=Path(__file__).resolve().parents[1]
    ap=argparse.ArgumentParser();ap.add_argument('--timeout',type=float,default=30.0)
    ap.add_argument('--heartbeats',type=int,default=2_000_000)
    ap.add_argument('--output',type=Path,default=root/'results/lean_comparisons.json')
    a=ap.parse_args();a.output.parent.mkdir(parents=True,exist_ok=True)
    lake=shutil.which('lake')
    result={'scope':'9 synthetic inequality contexts; not a Forge-vs-grind benchmark',
            'lean_toolchain':(root/'lean/lean-toolchain').read_text().strip(),
            'heartbeats':a.heartbeats,'timeout_seconds':a.timeout,'cases':[]}
    if not lake:
        result['status']='not_run';result['reason']='Lake executable not installed'
    else:
        result['status']='executed'
        result['build']=invoke([lake,'build'],root/'lean',max(120,a.timeout))
        temp=root/'lean/.forge-comparison';temp.mkdir(exist_ok=True)
        for case in json.loads((root/'lean/comparison_cases.json').read_text()):
            for tac in ['grind','nlinarith','positivity','aesop']:
                content=case['prefix'].replace('import Mathlib\n','import Mathlib\nset_option maxHeartbeats '+str(a.heartbeats)+'\n')
                file=temp/(case['name']+'_'+tac+'.lean');file.write_text(content+'  '+tac+'\n')
                r=invoke([lake,'env','lean',str(file)],root/'lean',a.timeout)
                r.update({'case':case['name'],'tactic':tac});result['cases'].append(r)
    a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='cases'},indent=2))

if __name__=='__main__':main()
