"""Reproduce the article's experiment ledger, with no third-party dependencies.

Run from prototype/: python -S run_experiments.py --output ../reproduced-results
Recorded results are not overwritten by default.
"""
import argparse
import itertools
import json
import math
import os
from pathlib import Path
import platform
import random
import shutil
import sys
import time
import exact as ex
import invariant_space as inv
import ideal_space as ideal
import finite_cover as fc
import presburger as pb
from test_prototypes import (cycle_case, sum_squares_case, random_integer_problem,
                             brute_feasible, direct_closure)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('../reproduced-results'))
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    certificates, rows = [], []

    def retain(name, lane, cert, stats):
        problem = cert['problem']
        checker = {'invariant': inv.check, 'ideal': ideal.check, 'finite': fc.check, 'integer': pb.check}[lane]
        if not checker(problem, cert):
            raise AssertionError('certificate failed: ' + name)
        certificates.append({'name': name, 'lane': lane, 'problem': problem,
                             'certificate': cert})
        rows.append({'name': name, 'lane': lane, **stats})

    start = time.perf_counter()
    cert, stats = cycle_case()
    basis = [ex.decode_poly(p, 3) for p in cert['invariants']]
    x, y, z = [ex.var(3, i) for i in range(3)]
    conservation_dimension = len(ex.nullspace(ex.coefficient_rows([
        ex.sub(ex.compose(p, [y, z, x]), p) for p in basis]), len(basis)))
    retain('cyclic-differences', 'invariant', cert,
           {**stats, 'conserved_subspace_dimension': conservation_dimension,
            'basis': [ex.format_poly(p, ['x', 'y', 'z']) for p in basis]})
    cert, stats = sum_squares_case()
    retain('sum-of-squares', 'invariant', cert,
           {**stats, 'basis': [ex.format_poly(ex.decode_poly(p, 2), ['n', 's'])
                               for p in cert['invariants']]})
    rng = random.Random(41027)
    for case in range(48):
        n, degree = 3, 1 + (case % 2)
        xs = [ex.var(n, i) for i in range(n)]
        transitions = []
        for _ in range(1 + case % 3):
            common_sum, c = rng.randint(-3, 3), rng.randint(-3, 3)
            transition = []
            for i in range(n):
                a, b = rng.randint(-4, 4), rng.randint(-4, 4)
                transition.append(ex.add(ex.const(n, c), ex.linear_combination(
                    [a, b, common_sum-a-b], xs)))
            transitions.append(transition)
        cert, stats = inv.synthesize(n, degree, [[xs[0]]*n], transitions)
        assert stats['invariant_dimension'] == (2 if degree == 1 else 7)
        retain('affine-diagonal-%02d' % case, 'invariant', cert, stats)
    x, y = [ex.var(2, i) for i in range(2)]
    cert, stats = inv.synthesize(2, 1, [[x, x]], [[ex.mul(x, x), ex.mul(y, y)]])
    assert stats['invariant_dimension'] == 0
    retain('nonlinear-template-miss', 'invariant', cert,
           {**stats, 'known_true_relation': 'x = y', 'expected_incompleteness': True})
    invariant_time = time.perf_counter() - start
    start = time.perf_counter()
    x, y = ex.var(2, 0), ex.var(2, 1)
    transition = [ex.mul(x, x), ex.mul(y, y)]
    for name, degree, md, initial, expected in [
        ('squaring-diagonal-e0', 1, 0, [[x, x]], 0),
        ('squaring-diagonal-e1', 1, 1, [[x, x]], 1),
        ('union-axes-e1', 2, 1, [[x, {}], [{}, y]], 0),
        ('union-axes-e2', 2, 2, [[x, {}], [{}, y]], 1),
        ('parabola-e2', 2, 2, [[x, ex.mul(x, x)]], 1),
        ('false-line-control', 1, 1, [[x, ex.scale(2, x)]], 0)]:
        cert, stats = ideal.synthesize(2, degree, md, initial, [transition])
        assert stats['invariant_dimension'] == expected
        retain(name, 'ideal', cert, {**stats, 'basis': [ex.format_poly(ex.decode_poly(p, 2), ['x', 'y']) for p in cert['invariants']]})
    # Parameterized powers preserve x=y but require degree-k-1 multipliers.
    for k in range(2, 10):
        cert, stats = ideal.synthesize(2, 1, k-1, [[x, x]],
                                      [[ex.power(x, k, 2), ex.power(y, k, 2)]])
        assert stats['invariant_dimension'] == 1
        retain('diagonal-power-%d' % k, 'ideal', cert, stats)
    ideal_time = time.perf_counter() - start


    start = time.perf_counter()
    for m in range(1, 13):
        cert, stats = fc.synthesize(fc.binary_tree_counts(m))
        assert cert['kind'] == 'cover' and stats['states_reached'] == m
        retain('tree-counts-mod-%02d' % m, 'finite', cert, stats)
    rng = random.Random(85031)
    for case in range(24):
        k = 2 + case % 4
        op = [[rng.randrange(k) for j in range(k)] for i in range(k)]
        if case % 2 == 0:
            for i in range(k):
                for j in range(i):
                    op[i][j] = op[j][i]
        else:
            op[0][1], op[1][0] = 0, 1
        problem = fc.mirror_problem(op)
        cert, stats = fc.synthesize(problem)
        assert cert['kind'] == ('cover' if case % 2 == 0 else 'counterexample')
        retain('mirror-magma-%02d' % case, 'finite', cert,
               {**stats, 'kind': cert['kind'], 'magma_size': k})
    rng = random.Random(73041)
    random_cover_count = random_counterexample_count = 0
    for case in range(100):
        n = rng.randint(1, 10)
        problem = {'states': n, 'constructors': [
            {'name': 'z', 'arity': 0, 'table': [rng.randrange(n)]},
            {'name': 'f', 'arity': 1, 'table': [rng.randrange(n) for _ in range(n)]},
            {'name': 'g', 'arity': 2, 'table': [rng.randrange(n) for _ in range(n*n)]}],
            'good': [i for i in range(n) if rng.randrange(4)]}
        cert, stats = fc.synthesize(problem)
        oracle = direct_closure(problem)
        assert (cert['kind'] == 'cover') == (oracle <= set(problem['good']))
        if cert['kind'] == 'cover': random_cover_count += 1
        else: random_counterexample_count += 1
        retain('random-algebra-%03d' % case, 'finite', cert,
               {**stats, 'kind': cert['kind'], 'oracle_reached': len(oracle)})
    finite_time = time.perf_counter() - start

    start = time.perf_counter()
    rng = random.Random(95041)
    valuations = feasible_valuations = 0
    for case in range(220):
        problem = random_integer_problem(rng)
        cert = pb.synthesize(problem)
        yes = no = 0
        for xs in itertools.product([-4, -1, 0, 2, 5], repeat=problem['parameters']):
            feasible, witness = pb.evaluate_program(cert['program'], xs)
            assert feasible == brute_feasible(problem, xs), (case, xs)
            if feasible:
                assert pb.holds(problem, xs, witness)
                yes += 1
            else: no += 1
        valuations += yes + no
        feasible_valuations += yes
        retain('integer-projection-%03d' % case, 'integer', cert,
               {'valuations': yes+no, 'feasible': yes, 'infeasible': no,
                'nodes': len(cert['program']['nodes']), 'period': cert['program']['period']})
    m1, m2 = 1000000007, 1000000009
    period = m1*m2
    problem = {'parameters': 1, 'inequalities': [
        {'a': -1, 'rhs': [0, -1]}, {'a': 1, 'rhs': [period-1, 1]}],
        'congruences': [{'a': 1, 'rhs': [1, 2], 'm': m1},
                        {'a': 1, 'rhs': [-3, 5], 'm': m2}]}
    cert = pb.synthesize(problem)
    demonstrations = []
    for x in [0, 1, -1, 10**100, -10**100]:
        feasible, witness = pb.evaluate_program(cert['program'], [x])
        assert feasible and pb.holds(problem, [x], witness)
        demonstrations.append({'input': x, 'witness': witness})
    retain('large-symbolic-CRT', 'integer', cert,
           {'nodes': len(cert['program']['nodes']), 'period': period,
            'period_bits': period.bit_length(), 'demonstrations': demonstrations})
    integer_time = time.perf_counter() - start
    totals = {lane: sum(c['lane'] == lane for c in certificates)
              for lane in ['invariant', 'ideal', 'finite', 'integer']}
    ledger = {
        'run': 'forge-extensions-2026-09-15',
        'status': 'PYTHON_CHECKED_NOT_LEAN_CHECKED',
        'python': sys.version, 'platform': platform.platform(),
        'standard_library_only': True,
        'lean_executable': shutil.which('lean'), 'lake_executable': shutil.which('lake'),
        'seeds': {'affine': 41027, 'magma': 85031, 'finite': 73041, 'integer': 95041},
        'certificate_counts_by_lane': totals,
        'finite_random_outcomes': {'cover': random_cover_count,
                                   'counterexample': random_counterexample_count},
        'integer_differential': {'systems': 220, 'valuations': valuations,
                                 'feasible': feasible_valuations,
                                 'infeasible': valuations-feasible_valuations},
        'seconds_one_run_including_check_and_oracle': {
            'invariant': invariant_time, 'ideal': ideal_time, 'finite': finite_time, 'integer': integer_time},
        'rows': rows}
    (args.output/'certificates.json').write_text(json.dumps(certificates, indent=2)+'\n')
    (args.output/'experiments.json').write_text(json.dumps(ledger, indent=2)+'\n')
    print(json.dumps({k: v for k, v in ledger.items() if k != 'rows'}, indent=2))
    for name in ['cyclic-differences', 'sum-of-squares', 'nonlinear-template-miss',
                 'tree-counts-mod-12', 'large-symbolic-CRT']:
        print(json.dumps(next(r for r in rows if r['name'] == name), indent=2))


if __name__ == '__main__':
    main()
