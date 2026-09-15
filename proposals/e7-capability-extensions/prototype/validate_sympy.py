"""Optional differential test of the proposer against SymPy (NOT a dependency).

Compares grlex polynomial remainders and independently replays every traced
Groebner-basis expression in its original generators. Fixed small random corpus.
"""
from pathlib import Path
import argparse,json,random,time
import sympy as sp
from exact import Q,add,mul,encode,monomials
from ideal_closure import groebner_traced,divide
from replay import poly,plus,times


def main(out):
    rng=random.Random(20260916);x,y=sp.symbols('x y');xs=[x,y]
    def gen(degree):
        return {m:Q(c) for m in monomials(2,degree) if (c:=rng.randint(-2,2))}
    def expr(p):
        return sum(sp.Rational(c.numerator,c.denominator)*x**m[0]*y**m[1] for m,c in p.items())
    def parse(v):
        return {tuple(m):Q(int(c.p),int(c.q)) for m,c in sp.Poly(v,*xs,domain=sp.QQ).terms() if c}
    start=time.perf_counter();queries=0;traces=0
    for i in range(32):
        originals=[gen(2) for _ in range(2+i%2)]
        gb,rs,pairs=groebner_traced(originals,2)
        reference=sp.groebner([expr(g) for g in originals],*xs,order='grlex',domain=sp.QQ)
        for g,row in zip(gb,rs):
            got={}
            for c,h in zip(row,originals):got=plus(got,times(poly(encode(c),2),poly(encode(h),2)))
            assert got==poly(encode(g),2)
            traces+=1
        for q in originals+[mul(originals[0],gen(1))]+[gen(3) for _ in range(8)]:
            _,r=divide(q,gb,2);_,want=reference.reduce(expr(q))
            assert r==parse(want),(i,expr(q),expr(r),want)
            queries+=1
    result=dict(seed=20260916,systems=32,remainder_comparisons=queries,
       traced_basis_identities=traces,all_agree=True,sympy_version=sp.__version__,
       seconds=time.perf_counter()-start,role='optional independent differential oracle; never used for acceptance')
    out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out',type=Path,default=Path(__file__).resolve().parents[1]/'reproduced-results'/'sympy-validation.json')
    main(ap.parse_args().out)
