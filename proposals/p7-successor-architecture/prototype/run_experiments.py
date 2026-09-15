#!/usr/bin/env python3
"""Deterministic component experiments. Not a benchmark of Lean or grind."""
from __future__ import annotations
import json, csv, random, time, sys, platform, statistics
from pathlib import Path
from fractions import Fraction as Q
from itertools import product
from dataclasses import replace
from math import gcd
from polynomial import Poly
import sos, lattice, induction, horn

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT/'results'
CERTS = OUT/'certificates'
OUT.mkdir(exist_ok=True); CERTS.mkdir(exist_ok=True)


def dump(name, data):
    (CERTS/(name+'.json')).write_text(json.dumps(data, indent=2)+'\n')


def problem_json(p):
    return {'target': p.target.json(), 'ge': [g.json() for g in p.ge],
            'eq': [h.json() for h in p.eq]}


def variables(n): return tuple(Poly.var(n, i) for i in range(n))


def sos_experiments(rng):
    rows = []; checks = 0; negative = 0
    x,y,z = variables(3)
    cases = [
        ('quadratic_dispersion', sos.Problem(x*x+y*y+z*z-x*y-y*z-z*x), 2),
        ('quartic_dispersion', sos.Problem((x*x+y*y+z*z)**2-
            3*(x*x*y*y+y*y*z*z+z*z*x*x)), 2),
        ('positive_triple_product', sos.Problem(x*y*z, (x,y,z)), 3),
    ]
    a,b,c,d = variables(4)
    cases.append(('lagrange_identity', sos.Problem((a*a+b*b)*(c*c+d*d)-(a*c+b*d)**2), 2))
    x,y = variables(2)
    cases += [
        ('box_quadratic', sos.Problem(x*(1-x), (x,1-x)), 2),
        ('box_cubic', sos.Problem(x-x**3, (x,1-x)), 2),
        ('inverse_pair_bound', sos.Problem(x*x+y*y-2, (), (x*y-1,)), 2),
        ('equality_transport', sos.Problem(x*x-y*y, (), (x-y,)), 2),
        ('weighted_quartic', sos.Problem(Q(2,3)*(x*x-y*y)**2+Q(5,7)*(x-y)**2), 2)
    ]
    for name, p, products in cases:
        times = []; cert = None
        # One warmup anywhere does not justify subtracting Python import time.
        for _ in range(3):
            t = time.perf_counter(); cert, stats = sos.discover(p, products=products)
            times.append((time.perf_counter()-t)*1000)
        assert cert is not None and sos.check(p, cert), name
        checks += 1
        for delta in [Q(1,17), Q(-1,19)]:
            assert not sos.check(replace(p, target=p.target+delta), cert)
            negative += 1
        if cert.positive:
            c0, atom = cert.positive[0]
            bad = replace(cert, positive=((-abs(c0)-1, atom),)+cert.positive[1:])
            assert not sos.check(p, bad); negative += 1
            bad = replace(cert, positive=((c0, replace(atom, assumptions=(999,))),)+cert.positive[1:])
            assert not sos.check(p, bad); negative += 1
        if cert.ideal:
            i, q = cert.ideal[0]
            assert not sos.check(p, replace(cert, ideal=((999,q),)+cert.ideal[1:])); negative += 1
        rows.append({'case': name, 'verified': True, 'median_ms': statistics.median(times), **stats})
        dump('sos_'+name, {'kind': 'sos', 'problem': problem_json(p), 'certificate': cert.json()})
    # Generated from the tested dictionary: useful property tests, not held-out benchmarks.
    generated = 24
    for j in range(generated):
        x,y = variables(2); qs = [x,y,x-y,x+y,x*x-y*y,x*y-1,x*x+y*y]
        p = sum((Q(rng.randint(1,9), rng.randint(1,7))*rng.choice(qs)**2
                 for _ in range(3)), Poly.const(2))
        cert, _ = sos.discover(sos.Problem(p))
        assert cert is not None and sos.check(sos.Problem(p), cert)
        checks += 1
    # Expected misses. UNKNOWN is the only inference from search failure.
    misses = []
    x,y = variables(2)
    for name,p,opts in [
        ('box_without_products', sos.Problem(x*(1-x),(x,1-x)), {'products':1}),
        ('cross_square_without_binomials', sos.Problem((x-y)**2), {'binomials':False}),
        ('unequal_coefficient_square', sos.Problem((2*x-3*y)**2), {}),
        ('false_polynomial', sos.Problem(x*x-1), {}),
        ('motzkin_dictionary_miss', sos.Problem(x**4*y*y+x*x*y**4+1-3*x*x*y*y), {})
    ]:
        cert, stats = sos.discover(p, **opts)
        assert cert is None, name
        misses.append({'case': name, 'status': 'unknown', **stats})
    return {'curated': rows, 'generated_successes': generated, 'positive_checks': checks,
            'corruption_rejections': negative, 'expected_misses': misses}


def lattice_experiments(rng):
    checked = 0; feasible = 0; infeasible = 0; mutations = 0
    start = time.perf_counter()
    # Complete one-row grid, expected status independently from math.gcd.
    for a,b,rhs in product(range(-3,4), range(-3,4), range(-5,6)):
        A = [[a,b]]; bs = [rhs]; cert = lattice.solve(A, bs)
        g = gcd(a,b); expected = rhs == 0 if not g else rhs % g == 0
        assert cert.feasible == expected and lattice.check(A, bs, cert)
        checked += 1; feasible += expected; infeasible += not expected
    random_successes = 120
    for j in range(random_successes):
        m,n = rng.randint(1,5),rng.randint(1,6)
        A = [[rng.randint(-9,9) for _ in range(n)] for _ in range(m)]
        hidden = [rng.randint(-20,20) for _ in range(n)]
        bs = lattice.matvec(A, hidden); cert = lattice.solve(A, bs)
        assert cert.feasible and lattice.check(A, bs, cert)
        # Several free-lattice samples must still satisfy every input row.
        B = cert.basis; d = len(B[0]) if B else 0
        for _ in range(4):
            z = [rng.randint(-5,5) for _ in range(d)]
            x = [u+lattice.dot(row,z) for u,row in zip(cert.witness,B)]
            assert lattice.matvec(A,x) == bs
        bad = replace(cert, witness=(cert.witness[0]+1,)+cert.witness[1:])
        assert not lattice.check(A,bs,bad); mutations += 1
        first = cert.steps[0]
        bad = replace(cert, steps=(replace(first,residual=first.residual+1),)+cert.steps[1:])
        assert not lattice.check(A,bs,bad); mutations += 1
        checked += 1; feasible += 1
    # Inconsistency arising only after processing a consistent prefix.
    prefix_failures = 0
    for j in range(30):
        A = [[1,1,0],[2,2,0]]; bs=[j,2*j+1]
        cert = lattice.solve(A,bs)
        assert not cert.feasible and lattice.check(A,bs,cert)
        checked += 1; infeasible += 1; prefix_failures += 1
    for name,A,b in [
        ('bezout_6_10',[[6,10]],[2]),
        ('coupled_system',[[6,10,15],[2,-4,3]],[7,-1]),
        ('parity_obstruction',[[6,10]],[1]),
        ('prefix_obstruction',[[1,1],[2,2]],[3,7]),
        ('empty_unknowns',[[]],[0])
    ]:
        cert = lattice.solve(A,b); assert lattice.check(A,b,cert)
        dump('lattice_'+name,{'kind':'lattice','matrix':A,'rhs':b,'certificate':cert.json()})
    return {'one_row_grid':539,'random_feasible':random_successes,
            'prefix_obstructions':prefix_failures,'positive_checks':checked,
            'feasible':feasible,'infeasible':infeasible,'corruption_rejections':mutations,
            'elapsed_ms':(time.perf_counter()-start)*1000}


def induction_experiments(rng):
    rows=[]; count=0; negative=0; sampled=0
    n,a = variables(2)
    cases=[(f'power_{k}',n**k) for k in range(9)]
    cases += [('quadratic_increment',2*n+1),('signed_cubic',3*n**3-5*n+7)]
    for j in range(12):
        degree = rng.randint(0,5)
        r=sum((Q(rng.randint(-5,5),rng.randint(1,5))*n**k
               for k in range(degree+1)),Poly.const(2))
        cases.append((f'random_{j}',r))
    for name,r in cases:
        t=time.perf_counter(); cert,stats=induction.synthesize(r,max_degree=10)
        elapsed=(time.perf_counter()-t)*1000
        assert cert is not None and induction.check(r,cert),name
        count += 1
        assert not induction.check(r,replace(cert,invariant=cert.invariant+1));negative+=1
        assert not induction.check(r,replace(cert,invariant=cert.invariant+n));negative+=1
        for i in range(13):
            for av in [-3,0,4]:
                assert induction.execute(r,i,av)==cert.invariant.evaluate([i,av]);sampled+=1
        rows.append({'case':name,'elapsed_ms':elapsed,**stats,
                     'invariant':cert.invariant.text(['n','a'])})
        if not name.startswith('random'):
            dump('induction_'+name,{'kind':'induction','increment':r.json(),'certificate':cert.json()})
    weak,_=induction.synthesize(n, max_degree=4,generalize=False)
    assert weak is None
    too_low,_=induction.synthesize(n**4,max_degree=4)
    assert too_low is None
    return {'cases':rows,'positive_checks':count,'corruption_rejections':negative,
            'execution_crosschecks':sampled,'ablations':{'no_accumulator_term':'unknown',
            'degree_too_low':'unknown'}}


def horn_experiments(rng):
    rows=[]; checks=0; corrupt=0; verified=0
    for chains in [0,10,100,1000]:
        length=24; rules=[]
        # Distractors deliberately come first; this is a stress microbenchmark.
        for i in range(chains):
            rules.append(horn.Rule((),f'd{i}_0'))
            rules.extend(horn.Rule((f'd{i}_{k}',),f'd{i}_{k+1}') for k in range(length))
        rules.append(horn.Rule((),'goal_0'))
        rules.extend(horn.Rule((f'goal_{k}',),f'goal_{k+1}') for k in range(length))
        for mode in [False,True]:
            t=time.perf_counter();proof,stats=horn.derive(rules,'goal_24',demand=mode)
            elapsed=(time.perf_counter()-t)*1000
            assert proof is not None and horn.check(rules,'goal_24',proof);checks+=1;verified+=1
            assert not horn.check(rules,'goal_24',proof[:-1]);corrupt+=1
            rows.append({'distractor_chains':chains,'mode':'demand' if mode else 'forward',
                         'elapsed_ms':elapsed,**stats})
            if chains==10 and mode:
                dump('horn_slice',{'kind':'horn','rules':[{'premises':list(r.premises),
                    'conclusion':r.conclusion} for r in rules],'target':'goal_24',
                    'proof':[{'rule':s.rule,'conclusion':s.conclusion} for s in proof]})
    # Cyclic Horn programs: demand closure plus forward fixpoint is not unsound DFS.
    for j in range(80):
        atoms=[f'p{i}' for i in range(12)]
        rules=[horn.Rule((),x) for x in rng.sample(atoms,3)]
        for _ in range(40):
            rules.append(horn.Rule(tuple(rng.sample(atoms,rng.randint(1,3))),rng.choice(atoms)))
        target=rng.choice(atoms)
        p0,_=horn.derive(rules,target,False);p1,_=horn.derive(rules,target,True)
        assert (p0 is not None)==(p1 is not None)
        for proof in [p0,p1]:
            if proof is not None:
                assert horn.check(rules,target,proof)
                verified+=1
        checks+=1
    return {'scaling':rows,'random_cyclic_programs':80,'positive_checks':checks,
            'verified_derivations':verified,
            'corruption_rejections':corrupt}


def polynomial_crosschecks(rng):
    import sympy as sp
    xs=sp.symbols('x y')
    def sym(p):
        return sum(sp.Rational(c.numerator,c.denominator)*
                   xs[0]**m[0]*xs[1]**m[1] for m,c in p.terms)
    x,y=variables(2)
    for _ in range(50):
        ps=[]
        for j in range(2):
            ps.append(sum((Q(rng.randint(-4,4),rng.randint(1,7))*x**rng.randint(0,3)*
                           y**rng.randint(0,3) for k in range(4)),Poly.const(2)))
        p,q=ps
        assert sp.expand(sym(p*q)-sym(p)*sym(q))==0
        assert sp.expand(sym(p+q)-sym(p)-sym(q))==0
        assert sp.expand(sym(p.substitute([x+1,y-2]))-
                         sym(p).subs({xs[0]:xs[0]+1,xs[1]:xs[1]-2},simultaneous=True))==0
    return {'random_pairs':50,'exact_identity_crosschecks':150}


def main():
    import scipy,numpy,sympy
    rng=random.Random(20260914)
    result={'scope':'Component microbenchmarks only. Lean/grind were not executed.',
        'seed':20260914,'environment':{'python':sys.version,'platform':platform.platform(),
        'scipy':scipy.__version__,'numpy':numpy.__version__,'sympy':sympy.__version__}}
    for name,fn in [('polynomial',polynomial_crosschecks),('sos',sos_experiments),
                    ('lattice',lattice_experiments),('induction',induction_experiments),
                    ('horn',horn_experiments)]:
        print('Running',name,flush=True);result[name]=fn(rng)
        (OUT/'experiments.json').write_text(json.dumps(result,indent=2)+'\n')
    summary={'component_test_cases':sum(result[x]['positive_checks'] for x in ['sos','lattice','induction','horn']),
        'valid_certificate_checks':sum(result[x]['positive_checks'] for x in ['sos','lattice','induction'])+result['horn']['verified_derivations'],
        'corruption_rejections':sum(result[x]['corruption_rejections'] for x in ['sos','lattice','induction','horn']),
        'polynomial_crosschecks':150,'induction_execution_crosschecks':result['induction']['execution_crosschecks']}
    result['summary']=summary
    (OUT/'experiments.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(summary,indent=2),flush=True)

if __name__=='__main__':main()
