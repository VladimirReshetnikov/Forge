#!/usr/bin/env python3
"""Reproduce experiments; writes JSON/CSV certificates and measurements.

Usage: python prototype/run_tests.py --out results
Randomness is fixed. Timing is illustrative and machine-dependent. No comparison
against Lean grind is performed: the only measured baseline is this package's DPLL.
"""
from __future__ import annotations
import argparse, copy, csv, itertools, json, platform, random, sys, time
from dataclasses import asdict
from pathlib import Path
from fractions import Fraction as Q
from cdcl_idl import Solver, DiffAtom, replay, floyd_consistent, dpll, check_cycle
from polynomial import Poly, variables, search, check_certificate
from induction import synthesize, check_invariant, encode, n as sn, a as sa
import sympy as sp
import scipy, numpy

SEED = 20260914


def dump(path, obj):
    path.write_text(json.dumps(obj, indent=2, sort_keys=True)+'\n',encoding='utf-8')


def truth(n, cs, atoms):
    return any(all(any(bits[abs(l)-1] == (l > 0) for l in c) for c in cs)
               and floyd_consistent(atoms,bits)
               for bits in itertools.product([False,True],repeat=n))


def sat_tests():
    rng=random.Random(SEED)
    counts={'cnf_cases':1000,'idl_cases':500,'sat':0,'unsat':0,
            'unsat_certificates_replayed':0,'truncated_certificates_rejected':0}
    for mode, count in [('cnf',1000),('idl',500)]:
        for case in range(count):
            n=rng.randrange(3,9)
            m=rng.randrange(1,6*n+1)
            cs=[[v*rng.choice([-1,1]) for v in rng.sample(range(1,n+1),3)] for _ in range(m)]
            atoms={}
            if mode=='idl':
                for k in range(1,n):
                    x,y=rng.sample(range(4),2)
                    atoms[k]=DiffAtom(x,y,rng.randrange(-3,4))
            expected=truth(n,cs,atoms)
            s=Solver(n,cs,atoms)
            got=s.solve()
            assert got==expected,(mode,case,'differential mismatch')
            counts['sat' if got else 'unsat']+=1
            if got:
                bits=[v==1 for v in s.a[1:]]
                assert all(any(bits[abs(l)-1]==(l>0) for l in c) for c in cs)
                assert floyd_consistent(atoms,bits)
            else:
                assert replay(n,cs,atoms,s.proof)
                counts['unsat_certificates_replayed']+=1
                assert not replay(n,cs,atoms,s.proof[:-1])
                counts['truncated_certificates_rejected']+=1
    # Edge cases include empty CNF, empty clause, tautology, and opposing units.
    edge_cases=[(0,[],True),(0,[[]],False),(1,[[1,-1]],True),
                (1,[[1],[-1]],False),(2,[[1,1],[2]],True)]
    for n,cs,want in edge_cases:
        s=Solver(n,cs);assert s.solve()==want
        if not want:assert replay(n,cs,{},s.proof)
    counts['edge_cases']=len(edge_cases)
    atoms={1:DiffAtom(0,1,0),2:DiffAtom(1,2,0),3:DiffAtom(2,0,-1)}
    s=Solver(3,[[1],[2],[3]],atoms);assert s.solve() is False
    assert replay(3,s.original,atoms,s.proof)
    bad=copy.deepcopy(s.proof);bad[0]['cycle'][0]*=-1
    assert not replay(3,s.original,atoms,bad)
    bad2=copy.deepcopy(s.proof);bad2[0]['clause']=bad2[0]['clause'][:-1]
    assert not replay(3,s.original,atoms,bad2)
    counts['theory_mutations_rejected']=2
    # Exact infinity handling in the independent oracle, beyond machine integers.
    huge=10**60
    assert floyd_consistent({1:DiffAtom(0,1,huge)},[True])
    assert not floyd_consistent({1:DiffAtom(0,1,huge),2:DiffAtom(1,0,-huge-1)},[True,True])
    counts['large_integer_oracle_regressions']=2
    # A false difference atom is complemented with -c-1, not -c.
    assert not floyd_consistent({1:DiffAtom(0,0,0)},[False])
    return counts,{'n':3,'clauses':s.original,
                   'atoms':{str(k):asdict(v) for k,v in atoms.items()},'proof':s.proof}


def pigeonhole(p,h):
    def v(i,j):return 1+i*h+j
    cs=[[v(i,j) for j in range(h)] for i in range(p)]
    cs += [[-v(i,j),-v(k,j)] for i in range(p) for k in range(i+1,p) for j in range(h)]
    return p*h,cs


def benchmarks(out):
    cases=[]
    for k in [0,4,8,12]:
        a,b=k+1,k+2
        cs=[[a,b],[a,-b],[-a,b],[-a,-b]]
        cases.append((f'padded-core-{k}',k+2,cs))
    for h in [3,4,5]:
        n,cs=pigeonhole(h+1,h)
        cases.append((f'pigeonhole-{h+1}-{h}',n,cs))
    rows=[]
    for name,n,cs in cases:
        t=time.perf_counter();b,bstats=dpll(n,cs);bt=time.perf_counter()-t
        s=Solver(n,cs)
        t=time.perf_counter();got=s.solve();st=time.perf_counter()-t
        t=time.perf_counter();valid=(got is False and replay(n,cs,{},s.proof));rt=time.perf_counter()-t
        assert b is False and got is False and valid
        row={'name':name,'variables':n,'clauses':len(cs),
             'dpll_decisions':bstats['decisions'],'cdcl_decisions':s.stats.decisions,
             'dpll_conflicts':bstats['conflicts'],'cdcl_conflicts':s.stats.conflicts,
             'learned':s.stats.learned,'nonchronological_backjumps':s.stats.nonchronological_backjumps,
             'dpll_seconds':bt,'cdcl_seconds':st,'replay_seconds':rt,
             'proof_additions':len(s.proof)}
        rows.append(row)
        dump(out/(name+'.json'),{'n':n,'clauses':cs,'atoms':{},'proof':s.proof,'stats':row})
        print('BENCH',name,row['dpll_decisions'],row['cdcl_decisions'],flush=True)
    with (out/'benchmarks.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=rows[0]);writer.writeheader();writer.writerows(rows)
    return rows


def sympy_expr(p):
    vs=sp.symbols(f'x0:{p.n}')
    return sp.expand(sum(sp.Rational(c.numerator,c.denominator)*sp.prod(v**e for v,e in zip(vs,m))
                         for m,c in p.terms.items()))


def polynomial_tests(out):
    x,y=variables(2)
    a,b,c,d=variables(4)
    cases=[
       ('quartic-square',x**4+y**4-2*x*x*y*y,[],[],4,True),
       ('three-squares-quartic',x**4+y**4+1-x*x*y*y-x*x-y*y,[],[],4,True),
       ('cauchy-schwarz-2', (a*a+b*b)*(c*c+d*d)-(a*c+b*d)**2,[],[],4,True),
       ('box-bilinear',x+y-2*x*y,[x,y,1-x,1-y],[],2,True),
       ('interval-product',1-x*x,[1-x,1+x],[],2,True),
       ('equality-constrained',x*x+y*y-Q(1,2),[],[x+y-1],2,True),
       ('positive-slack',x*x+y*y+1-Q(1,2),[],[],2,True),
       ('false-polynomial',x*x-1,[],[],2,False),
       ('motzkin-bounded-search',x**4*y*y+x*x*y**4+1-3*x*x*y*y,[],[],6,False),
       ('dictionary-ratio-gap',(2*x+y)**2,[],[],2,False)]
    rows=[]
    for name,p,gs,hs,D,expected in cases:
        t=time.perf_counter();cert,diag=search(p,gs,hs,degree=D);elapsed=time.perf_counter()-t
        assert (cert is not None)==expected,(name,diag)
        mutations=0
        if cert is not None:
            assert check_certificate(p,gs,hs,cert)
            assert not check_certificate(p+1,gs,hs,cert)
            mutations+=1
            if cert['cone']:
                bad=copy.deepcopy(cert);bad['cone'][0]['weight']='-1'
                assert not check_certificate(p,gs,hs,bad)
                mutations+=1
        row={'name':name,**diag,'seconds':elapsed,'mutation_rejections':mutations}
        rows.append(row)
        dump(out/(name+'.json'),{'target':p.encode(),'nonnegative_assumptions':[g.encode() for g in gs],
                                'equality_assumptions':[h.encode() for h in hs],
                                'certificate':cert,'diagnostics':row})
        print('POLY',name,diag['status'],flush=True)
    # Oracle-independent checker tests for arbitrary rational squares.
    rng=random.Random(SEED+1)
    for k in range(100):
        q=sum((Q(rng.randrange(-5,6),rng.randrange(1,5))*v for v in [x,y,Poly.constant(2,1)]),Poly.constant(2,0))
        weight=Q(rng.randrange(1,6),rng.randrange(1,5))
        p=weight*q*q
        cert={'cone':[{'weight':str(weight),'square':q.encode(),'factors':[]}],'ideal':[]}
        assert check_certificate(p,[],[],cert)
        assert sp.expand(sympy_expr(p)-sp.Rational(weight.numerator,weight.denominator)*sympy_expr(q)**2)==0
    # A certificate the small dictionary oracle need not discover.
    h=a*d*d+b*d+c
    p=b*b-4*a*c
    q=2*a*d+b
    cert={'cone':[{'weight':'1','square':q.encode(),'factors':[]}],
          'ideal':[{'hypothesis':0,'multiplier':(-4*a).encode()}]}
    assert check_certificate(p,[],[h],cert)
    dump(out/'discriminant-manual-certificate.json',{'target':p.encode(),
         'nonnegative_assumptions':[],'equality_assumptions':[h.encode()],
         'certificate':cert,'origin':'manually supplied identity; checker test, not oracle discovery'})
    return {'search_cases':rows,'planted_checker_crosschecks':100,'manual_certificates':1}


def induction_tests(out):
    rows=[]
    for p in range(6):
        t=time.perf_counter();q,diag=synthesize(p);elapsed=time.perf_counter()-t
        assert q is not None
        assert check_invariant(p,q)[0]
        assert not check_invariant(p,q+1)[0]
        assert not check_invariant(p,q+sn)[0]
        # Independent expansion using sparse rational Poly substitution via sampling
        # is NOT used to claim kernel checking; symbolic base/step are the oracle.
        row={'power':p,'polynomial':str(q),'degree':diag['degree'],
             'sample_count':diag['sample_count'],'candidates':len(diag['history']),
             'seconds':elapsed,'base_residual':diag['base_residual'],
             'step_residual':diag['step_residual']}
        rows.append(row)
        dump(out/f'induction-power-{p}.json',{'invariant_coefficients':encode(q),'result':row,'trace':diag})
        print('INDUCT',p,str(q),flush=True)
    return {'synthesized':rows,'mutations_rejected':12}


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',default='results');args=ap.parse_args()
    out=Path(args.out);out.mkdir(parents=True,exist_ok=True)
    start=time.perf_counter()
    counts,cert=sat_tests();print('SAT TESTS',counts,flush=True)
    dump(out/'idl-negative-cycle.json',cert)
    rows=benchmarks(out)
    polys=polynomial_tests(out)
    induct=induction_tests(out)
    result={'seed':SEED,'environment':{'python':sys.version,'platform':platform.platform(),
             'sympy':sp.__version__,'scipy':scipy.__version__,'numpy':numpy.__version__,
             'lean':'not installed; no Lean execution or grind comparison was performed'},
            'sat_tests':counts,'benchmarks':rows,'polynomials':polys,'induction':induct,
            'total_seconds':time.perf_counter()-start,'all_assertions_passed':True}
    dump(out/'summary.json',result)
    print('ALL ASSERTIONS PASSED; results in',out,flush=True)

if __name__=='__main__':main()
