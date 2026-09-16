"""Reproduce experiments from any working directory. Stops on the first failure."""
from pathlib import Path
import subprocess,sys
ROOT=Path(__file__).resolve().parent
commands=[
 ('examples',['run_examples.py']),
 ('replay-no-site',['-S','verify_corpus.py']),
 ('differential',['differential.py']),
 ('mutations',['mutation_tests.py']),
 ('metamorphic',['metamorphic.py']),
 ('metamorphic-replay-no-site',['-S','verify_corpus.py','../metamorphic-corpus']),
 ('strategy-probes',['strategy_probes.py']),
 ('pytest',['-m','pytest','-q']),
]
for name,args in commands:
    print('Running',name,flush=True)
    with (ROOT/'results'/('rerun-'+name+'.log')).open('w',encoding='utf-8') as log:
        subprocess.run([sys.executable,*args],cwd=ROOT/'prototype',stdout=log,
                       stderr=subprocess.STDOUT,check=True)
print('All experiment commands completed successfully.')
