#!/usr/bin/env python3
"""Independent-computation diagnostics, NOT substitutes for analytic proofs.

1. Exhaustive permutations vs the exchange theorem on small random inputs.
2. SymPy differentiation vs search/checker polynomials (optional dependency).
3. Decimal exponentiation vs rational enclosures (finite numerical sanity only).
"""
import argparse,itertools,json,random,time
from fractions import Fraction as F
from decimal import Decimal,localcontext
from pathlib import Path
from forge_flow.model import ExpPoly as E
from forge_flow.search import make_ladder,canonical_search,optimal_ladder,ladder_search
from forge_flow.check import decode,derivative,check_minimality
from forge_flow.enclosure import exp_bound


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',default='oracle-results.json');args=ap.parse_args()
    p=Path(args.out)
    if p.exists():raise FileExistsError(p)
    rng=random.Random(20260915);t=time.perf_counter();counts={}
    sample=[]
    for _ in range(200):
        f=E.make({r:[rng.randint(-3,3) for _ in range(rng.randint(1,2))] for r in (-1,0,1)})
        roots=[r for r,cs in f.terms for _ in cs]
        feasible=any(make_ladder(f,list(order),False) is not None for order in set(itertools.permutations(roots)))
        canonical=canonical_search(f)['status']=='certificate'
        assert feasible==canonical
        b=ladder_search(f);o=optimal_ladder(f)
        assert (b['status']=='certificate')==(o['status']=='certificate')
        if o['status']=='certificate':
            assert len(b['certificate']['cofactors'])==o['steps']
            assert check_minimality(f.problem(),o['certificate'],o['minimality'])
        sample.append(f)
    counts['exhaustive_permutation_cases']=len(sample)
    counts['bfs_optimality_cases']=len(sample)
    try:
        import sympy as sp
    except ImportError:
        counts['sympy']='NOT_RUN'
    else:
        x=sp.Symbol('x')
        def expr(f):
            return sum(sum(sp.Rational(c.numerator,c.denominator)*x**j for j,c in enumerate(cs))*sp.exp(sp.Rational(r.numerator,r.denominator)*x) for r,cs in f.terms)
        for f in sample:
            assert sp.expand(sp.diff(expr(f),x)-expr(f.deriv()))==0
            assert decode(f.deriv().payload())==derivative(decode(f.payload()))
        counts['symbolic_derivative_cases']=len(sample);counts['sympy_version']=sp.__version__
    with localcontext() as ctx:
        ctx.prec=100
        for k in range(-80,81):
            x=F(k,8);lo,hi=exp_bound(x,10)
            v=(Decimal(x.numerator)/Decimal(x.denominator)).exp()
            a=Decimal(lo.numerator)/Decimal(lo.denominator);b=Decimal(hi.numerator)/Decimal(hi.denominator)
            assert a<=v<=b
    counts['decimal_enclosure_points']=161
    result={'counts':counts,'elapsed_seconds':time.perf_counter()-t,'seed':20260915,
            'claim':'finite cross-checks only; no Lean execution'}
    p.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
