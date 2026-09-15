#!/usr/bin/env python3
"""Run candidate separating problems in the user's already-built mathlib project.

Not run in the authoring session. Records rejection/timeouts without interpreting
them as mathematical refutations. Setup failure is reported separately. This is
an initial harness, not the large controlled evaluation proposed in the article.
"""
from __future__ import annotations
import argparse,json,shutil,subprocess,tempfile,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--project',type=Path,required=True,help='Existing built mathlib/Lake project')
    p.add_argument('--timeout',type=float,default=30.0)
    p.add_argument('--heartbeats',type=int,default=1000000)
    p.add_argument('--strategy',action='append',default=[],metavar='NAME=TACTIC',
                   help='Additional tactic; e.g. experimental=forge after Forge is actually installed')
    p.add_argument('--import-module',action='append',default=[],help='Optional already-built module to import')
    p.add_argument('--output',type=Path,default=ROOT/'results'/'lean-benchmark.json')
    a=p.parse_args();project=a.project.resolve()
    if not project.is_dir() or not shutil.which('lake'):
        p.error('A valid project directory and a lake executable on PATH are required.')
    if a.timeout<=0 or a.heartbeats<1:p.error('Timeout and heartbeats must be positive.')
    strategies={'grind':'grind','aesop':'aesop','nlinarith':'nlinarith','omega':'omega'}
    for item in a.strategy:
        if '=' not in item:p.error('--strategy requires NAME=TACTIC')
        name,tactic=item.split('=',1)
        if not name or not tactic:p.error('Empty strategy name/tactic')
        strategies[name]=tactic
    imports='import Mathlib\n'+''.join('import '+s+'\n' for s in a.import_module)
    def run(path):
        start=time.perf_counter()
        try:
            r=subprocess.run(['lake','env','lean',str(path)],cwd=project,capture_output=True,
                             text=True,timeout=a.timeout,check=False)
            return {'status':'accepted' if r.returncode==0 else 'lean_rejected',
                    'exit_code':r.returncode,'seconds':time.perf_counter()-start,
                    'stdout':r.stdout,'stderr':r.stderr}
        except subprocess.TimeoutExpired as e:
            return {'status':'timeout','seconds':time.perf_counter()-start,
                    'stdout':str(e.stdout or ''),'stderr':str(e.stderr or '')}
    version=subprocess.run(['lake','env','lean','--version'],cwd=project,capture_output=True,text=True,check=False)
    result={'lean_version':version.stdout.strip(),'heartbeats':a.heartbeats,'timeout':a.timeout,
            'imports':imports,'note':'Fresh process timings include import/startup cost; not kernel-only timings.',
            'rows':[]}
    with tempfile.TemporaryDirectory(prefix='forge-bench-',dir=project) as td:
        td=Path(td);setup=td/'Setup.lean';setup.write_text(imports+'example : True := by trivial\n')
        result['setup']=run(setup)
        if result['setup']['status']=='accepted':
            cases=json.loads((ROOT/'lean'/'benchmarks.json').read_text())
            for i,c in enumerate(cases):
                for j,(name,tactic) in enumerate(strategies.items()):
                    path=td/f'Case{i}_{j}.lean'
                    text=(imports+f'\nset_option maxHeartbeats {a.heartbeats}\nnamespace ForgeBench\n'+
                          c['prelude']+'\ntheorem bench '+c['statement']+' := by\n'+
                          '\n'.join('  '+line for line in tactic.splitlines())+
                          '\n#print axioms bench\nend ForgeBench\n')
                    path.write_text(text)
                    result['rows'].append({'case':c['id'],'strategy':name,'source':text,**run(path)})
    a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(a.output)
    if result['setup']['status']!='accepted':raise SystemExit('Setup failed; no tactic comparison was performed.')
if __name__=='__main__':main()
