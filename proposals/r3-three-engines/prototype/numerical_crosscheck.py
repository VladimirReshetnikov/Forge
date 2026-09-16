#!/usr/bin/env python3
"""Optional 80-digit numerical sanity checks. NOT part of certificate acceptance."""
import argparse,json,random
from fractions import Fraction as F
from pathlib import Path
import mpmath as mp
from forge_delta.analytic_search import enclose,X,op

def main(out):
    mp.mp.dps=80;rng=random.Random(20260915);rows=[]
    def convert(x): return mp.mpf(x.numerator)/x.denominator
    for k in ('exp','log','sin','cos'):
        for i in range(80):
            x=F(rng.randint(1,60),20) if k=='log' else F(rng.randint(-40,40),20)
            lo,hi=enclose(op(k,X),(x,x),32)
            v=getattr(mp,k)(convert(x))
            # Diagnostic tolerances only cover conversion at an exact endpoint.
            ok=convert(lo)-mp.mpf('1e-70')<=v<=convert(hi)+mp.mpf('1e-70')
            assert ok,(k,x,lo,hi,v)
            rows.append({'function':k,'x':str(x),'within_enclosure':True})
    data={'status':'NUMERICAL_SANITY_ONLY','mpmath':mp.__version__,'decimal_digits':80,'cases':len(rows),'records':rows}
    out.write_text(json.dumps(data,indent=2)+'\n');print(f'{len(rows)} numerical sanity checks passed; not proof evidence')
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,default=Path('numerical-crosscheck.json'));a=p.parse_args();main(a.out)
