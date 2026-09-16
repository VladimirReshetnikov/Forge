#!/usr/bin/env python3
"""Fresh, portable validation of all delivered mechanisms. Uses no packages."""
from pathlib import Path
from datetime import datetime,timezone
import argparse,json,subprocess,sys

if sys.flags.optimize:
    raise SystemExit('Run without -O: experiment assertions must remain enabled.')
root=Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser()
p.add_argument('--out',type=Path,default=root/'reproduced'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'))
a=p.parse_args();out=a.out.resolve();out.mkdir(parents=True,exist_ok=False)
commands=[['run_experiments.py','--out',str(out/'main')],
 ['replay.py',str(out/'main')],
 ['ablations.py','--out',str(out/'ablations')],
 ['replay.py',str(out/'ablations')],
 ['compact_experiment.py',str(out/'main'),'--out',str(out/'compact')],
 ['replay.py',str(out/'compact')]]
records=[]
for i,args in enumerate(commands):
    command=[sys.executable,'-S',*args]
    result=subprocess.run(command,cwd=root/'prototype',text=True,
                          stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (out/f'command-{i+1}.txt').write_text(result.stdout,encoding='utf-8')
    records.append({'command':args,'returncode':result.returncode})
    print(args[0],result.returncode)
    if result.returncode:
        (out/'validation.json').write_text(json.dumps({'status':'FAILED','commands':records},indent=2))
        print(result.stdout);raise SystemExit(result.returncode)
comparison={f:(root/'results/run-01'/f).read_bytes()==(out/'main'/f).read_bytes()
            for f in ['certificates.jsonl','rejections.jsonl']}
status='PASSED' if all(comparison.values()) else 'CORPUS_DIFFERENCE'
report={'status':status,'python':sys.version,'commands':records,
        'byte_identical_to_recorded_main':comparison,
        'lean_compilation':'NOT_RUN','source_bridge':'NOT_IMPLEMENTED'}
(out/'validation.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps(report,indent=2))
if status!='PASSED':raise SystemExit(1)
