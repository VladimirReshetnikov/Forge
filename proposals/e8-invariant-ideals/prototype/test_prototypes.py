"""Deterministic correctness, differential, and certificate-mutation tests.
Run: python -S -m unittest -v test_prototypes
"""
import copy
import itertools
import math
import random
import unittest
from fractions import Fraction as Q
import exact as ex
import invariant_space as inv
import ideal_space as ideal
import finite_cover as fc
import presburger as pb


def cycle_case():
    x, y, z = [ex.var(3, i) for i in range(3)]
    return inv.synthesize(3, 1, [[x, x, x]], [[y, z, x]])


def sum_squares_case():
    n, s = [ex.var(2, i) for i in range(2)]
    return inv.synthesize(2, 3, [[{}, {}]],
                          [[ex.add(n, ex.const(2, 1)), ex.add(s, ex.mul(n, n))]])


def direct_closure(problem):
    """Independent saturation oracle: no production transition() call."""
    reached = set()
    while True:
        old = set(reached)
        for c in problem['constructors']:
            for args in itertools.product(old, repeat=c['arity']):
                index = 0
                for a in args:
                    index = index*problem['states'] + a
                reached.add(c['table'][index])
        if old == reached:
            return reached


def random_integer_problem(rng):
    n = rng.choice([1, 2])
    inequalities = [{'a': rng.randint(-4, 4),
                     'rhs': [rng.randint(-6, 6) for _ in range(n+1)]}
                    for _ in range(rng.randint(0, 4))]
    congruences = [{'a': rng.randint(-4, 4), 'm': rng.randint(1, 8),
                    'rhs': [rng.randint(-6, 6) for _ in range(n+1)]}
                   for _ in range(rng.randint(0, 3))]
    return {'parameters': n, 'inequalities': inequalities, 'congruences': congruences}


def brute_feasible(problem, xs):
    """Finite complete oracle for one concrete valuation in this test fragment.

    Nonzero-coefficient bound endpoints lie in [-B,B]. The periodic part has
    period dividing P, so any satisfiable unbounded side has a witness no more
    than P beyond those endpoints. Zero-coefficient constraints do not bound y.
    """
    all_rows = problem['inequalities'] + problem['congruences']
    B = 1 + max([abs(r['rhs'][0] + sum(a*x for a, x in zip(r['rhs'][1:], xs)))
                 for r in all_rows] + [0])
    P = math.lcm(*([r['m'] for r in problem['congruences']] or [1]))
    return any(pb.holds(problem, xs, y) for y in range(-B-P, B+P+1))


class ExactTests(unittest.TestCase):
    def test_rref_and_coordinates(self):
        self.assertEqual(ex.nullspace([[1, 2, 3], [2, 4, 6]], 3),
                         [[Q(-2), Q(1), Q(0)], [Q(-3), Q(0), Q(1)]])
        x, y = ex.var(2, 0), ex.var(2, 1)
        self.assertEqual(ex.coordinates(ex.add(x, y), [x, y]), [1, 1])
        self.assertIsNone(ex.coordinates(ex.const(2, 1), [x, y]))
        self.assertEqual(ex.coordinates({}, []), [])

    def test_polynomial_identities(self):
        rng = random.Random(715)
        for _ in range(100):
            n = 2
            p = ex.clean({m: Q(rng.randint(-3, 3)) for m in ex.monomials(n, 3)})
            q = ex.clean({m: Q(rng.randint(-3, 3)) for m in ex.monomials(n, 2)})
            xs = [rng.randint(-5, 5) for _ in range(n)]
            self.assertEqual(ex.evaluate(ex.mul(p, q), xs),
                             ex.evaluate(p, xs)*ex.evaluate(q, xs))
            substitution = [ex.add(ex.var(n, 0), ex.var(n, 1)), ex.const(n, 2)]
            self.assertEqual(ex.evaluate(ex.compose(p, substitution), xs),
                             ex.evaluate(p, [ex.evaluate(s, xs) for s in substitution]))
            self.assertEqual(ex.decode_poly(ex.encode_poly(p), n), p)

    def test_noncanonical_coefficients_rejected(self):
        for bad in [[[[1], 1, 0]], [[[1], 2, 4]], [[[True], 1, 1]],
                    [[[1], 1.0, 1]], [[[1], 0, 1]], [[[1], 1, 1], [[1], 2, 1]]]:
            with self.assertRaises(ValueError):
                ex.decode_poly(bad, 1)


class InvariantTests(unittest.TestCase):
    def test_cycle_packet_not_conservation(self):
        cert, stats = cycle_case()
        self.assertTrue(inv.check(cert['problem'], cert))
        self.assertEqual(stats['invariant_dimension'], 2)
        basis = [ex.decode_poly(p, 3) for p in cert['invariants']]
        x, y, z = [ex.var(3, i) for i in range(3)]
        self.assertIsNotNone(ex.coordinates(ex.sub(x, y), basis))
        self.assertIsNotNone(ex.coordinates(ex.sub(y, z), basis))
        residuals = [ex.sub(ex.compose(p, [y, z, x]), p) for p in basis]
        self.assertEqual(len(ex.nullspace(ex.coefficient_rows(residuals), len(basis))), 0)

    def test_sum_squares_packet(self):
        cert, stats = sum_squares_case()
        self.assertTrue(inv.check(cert['problem'], cert))
        n, s = ex.var(2, 0), ex.var(2, 1)
        target = ex.sub(ex.scale(6, s), ex.mul(ex.mul(n, ex.sub(n, ex.const(2, 1))),
                                             ex.sub(ex.scale(2, n), ex.const(2, 1))))
        basis = [ex.decode_poly(p, 2) for p in cert['invariants']]
        self.assertIsNotNone(ex.coordinates(target, basis))
        for start in [[0, 0]]:
            state = start
            for _ in range(30):
                self.assertTrue(all(ex.evaluate(p, state) == 0 for p in basis))
                state = [state[0]+1, state[1]+state[0]**2]

    def test_nonlinear_incompleteness_control(self):
        x, y = ex.var(2, 0), ex.var(2, 1)
        cert, stats = inv.synthesize(2, 1, [[x, x]], [[ex.mul(x, x), ex.mul(y, y)]])
        self.assertTrue(inv.check(cert['problem'], cert))
        self.assertEqual(stats['invariant_dimension'], 0)
        # x=y remains true, but its degree-one pullback is not degree one.
        self.assertNotEqual(ex.compose(ex.sub(x, y), [ex.mul(x, x), ex.mul(y, y)]), {})

    def test_multiple_transitions_and_initial_maps(self):
        x, y = ex.var(2, 0), ex.var(2, 1)
        cert, stats = inv.synthesize(2, 2, [[x, x], [{}, {}]],
                                     [[y, x], [ex.add(x, y), ex.scale(2, y)]])
        self.assertTrue(inv.check(cert['problem'], cert))
        self.assertGreater(stats['invariant_dimension'], 0)
        cert2, stats2 = inv.synthesize(2, 1, [[x, x], [ex.const(2, 1), {}]], [[y, x]])
        self.assertTrue(inv.check(cert2['problem'], cert2))
        self.assertEqual(stats2['invariant_dimension'], 0)

    def test_mutated_invariant_certificates(self):
        cert, _ = cycle_case()
        bad = copy.deepcopy(cert)
        bad['matrices'][0][0][0][0] += bad['matrices'][0][0][0][1]
        self.assertFalse(inv.check(cert['problem'], bad))
        bad = copy.deepcopy(cert)
        bad['invariants'][0].append([[0, 0, 0], 1, 1])
        self.assertFalse(inv.check(cert['problem'], bad))
        bad = copy.deepcopy(cert)
        bad['invariants'][0][0][2] = 0
        self.assertFalse(inv.check(cert['problem'], bad))
        problem = copy.deepcopy(cert['problem'])
        problem['transitions'][0][0] = []
        self.assertFalse(inv.check(problem, cert))
        bad = copy.deepcopy(cert)
        bad['matrices'][0][0][0] = [True, 1]
        self.assertFalse(inv.check(cert['problem'], bad))


class IdealSpaceTests(unittest.TestCase):
    def test_squaring_and_union(self):
        x, y = ex.var(2, 0), ex.var(2, 1)
        transition = [ex.mul(x, x), ex.mul(y, y)]
        for degree, md, initial, expected in [
            (1, 0, [[x, x]], 0),
            (1, 1, [[x, x]], 1),
            (2, 1, [[x, {}], [{}, y]], 0),
            (2, 2, [[x, {}], [{}, y]], 1),
            (2, 2, [[x, ex.mul(x, x)]], 1),
            (1, 1, [[x, ex.scale(2, x)]], 0)]:
            cert, stats = ideal.synthesize(2, degree, md, initial, [transition])
            self.assertTrue(ideal.check(cert['problem'], cert))
            self.assertEqual(stats['invariant_dimension'], expected)

    def test_constant_multiplier_agreement(self):
        x, y, z = [ex.var(3, i) for i in range(3)]
        for degree in [1, 2]:
            c1, _ = inv.synthesize(3, degree, [[x, x, x]], [[y, z, x]])
            c2, _ = ideal.synthesize(3, degree, 0, [[x, x, x]], [[y, z, x]])
            self.assertEqual(c1['invariants'], c2['invariants'])
            self.assertTrue(ideal.check(c2['problem'], c2))

    def test_polynomial_multiplier_mutations(self):
        x, y = ex.var(2, 0), ex.var(2, 1)
        cert, _ = ideal.synthesize(2, 1, 1, [[x, x]], [[ex.mul(x, x), ex.mul(y, y)]])
        bad = copy.deepcopy(cert)
        bad['matrices'][0][0][0] = []
        self.assertFalse(ideal.check(cert['problem'], bad))
        bad = copy.deepcopy(cert)
        bad['invariants'][0].append([[0, 0], 1, 1])
        self.assertFalse(ideal.check(cert['problem'], bad))
        problem = copy.deepcopy(cert['problem'])
        problem['multiplier_degree'] = 0
        bad = copy.deepcopy(cert)
        bad['problem'] = problem
        self.assertFalse(ideal.check(problem, bad))


class FiniteCoverTests(unittest.TestCase):
    def test_tree_count_covers(self):
        for m in range(1, 13):
            problem = fc.binary_tree_counts(m)
            cert, stats = fc.synthesize(problem)
            self.assertEqual(cert['kind'], 'cover')
            self.assertTrue(fc.check(problem, cert))
            self.assertEqual(stats['states_reached'], m)

    def test_mirror_positive_and_negative(self):
        for op, kind in [([[0, 1], [1, 0]], 'cover'),
                         ([[0, 0], [1, 1]], 'counterexample')]:
            problem = fc.mirror_problem(op)
            cert, _ = fc.synthesize(problem)
            self.assertEqual(cert['kind'], kind)
            self.assertTrue(fc.check(problem, cert))

    def test_differential_finite_reachability(self):
        rng = random.Random(601)
        for _ in range(100):
            n = rng.randint(1, 9)
            problem = {'states': n, 'constructors': [
                {'name': 'z', 'arity': 0, 'table': [rng.randrange(n)]},
                {'name': 'f', 'arity': 1, 'table': [rng.randrange(n) for _ in range(n)]},
                {'name': 'g', 'arity': 2, 'table': [rng.randrange(n) for _ in range(n*n)]}],
                'good': [i for i in range(n) if rng.randrange(3)]}
            cert, _ = fc.synthesize(problem)
            self.assertTrue(fc.check(problem, cert))
            oracle = direct_closure(problem)
            self.assertEqual(cert['kind'] == 'cover', oracle <= set(problem['good']))

    def test_budget_is_unknown(self):
        problem = fc.binary_tree_counts(2)
        cert, _ = fc.synthesize(problem, budget=0)
        self.assertEqual(cert['kind'], 'unknown')
        self.assertFalse(fc.check(problem, cert))

    def test_mutated_cover_and_tree(self):
        problem = fc.binary_tree_counts(3)
        cert, _ = fc.synthesize(problem)
        bad = copy.deepcopy(cert)
        bad['cover'] = []
        self.assertFalse(fc.check(problem, bad))
        bad = copy.deepcopy(cert)
        bad['cover'][0] = 0  # not good
        self.assertFalse(fc.check(problem, bad))
        problem = fc.mirror_problem([[0, 0], [1, 1]])
        cert, _ = fc.synthesize(problem)
        bad = copy.deepcopy(cert)
        bad['nodes'][-1]['children'][0] = len(bad['nodes'])-1
        self.assertFalse(fc.check(problem, bad))
        bad = copy.deepcopy(cert)
        bad['root'] = 0
        self.assertFalse(fc.check(problem, bad))
        bad = copy.deepcopy(cert)
        bad['nodes'][0]['constructor'] = True
        self.assertFalse(fc.check(problem, bad))


class IntegerProjectionTests(unittest.TestCase):
    def test_bezout_all_signs(self):
        for a in range(-20, 21):
            for b in range(1, 21):
                receipt = pb.bezout(a, b)
                self.assertTrue(pb.valid_bezout(a, b, receipt))
                self.assertEqual(receipt[0], math.gcd(a, b))

    def test_special_semantics(self):
        cases = [
            {'parameters': 1, 'inequalities': [], 'congruences': []},
            {'parameters': 1, 'inequalities': [{'a': -3, 'rhs': [0, 1]}], 'congruences': []},
            {'parameters': 1, 'inequalities': [{'a': 3, 'rhs': [0, 1]}], 'congruences': []},
            {'parameters': 1, 'inequalities': [{'a': 0, 'rhs': [0, 1]}], 'congruences': []},
            {'parameters': 1, 'inequalities': [], 'congruences': [{'a': 0, 'm': 3, 'rhs': [0, 1]}]},
            {'parameters': 1, 'inequalities': [], 'congruences': [{'a': 6, 'm': 10, 'rhs': [1, 0]}]},
            {'parameters': 1, 'inequalities': [], 'congruences': [
                {'a': 1, 'm': 4, 'rhs': [0, 1]}, {'a': 1, 'm': 6, 'rhs': [1, 1]}]},
        ]
        for problem in cases:
            cert = pb.synthesize(problem)
            self.assertTrue(pb.check(problem, cert))
            for x in range(-12, 13):
                feasible, witness = pb.evaluate_program(cert['program'], [x])
                self.assertEqual(feasible, brute_feasible(problem, [x]))
                if feasible:
                    self.assertTrue(pb.holds(problem, [x], witness))

    def test_differential_projection(self):
        rng = random.Random(9152026)
        for _ in range(180):
            problem = random_integer_problem(rng)
            cert = pb.synthesize(problem)
            self.assertTrue(pb.check(problem, cert))
            for xs in itertools.product([-4, -1, 0, 2, 5], repeat=problem['parameters']):
                feasible, witness = pb.evaluate_program(cert['program'], xs)
                self.assertEqual(feasible, brute_feasible(problem, xs), (problem, xs, witness))
                if feasible:
                    self.assertTrue(pb.holds(problem, xs, witness))

    def test_huge_modulus_and_inputs(self):
        m1, m2 = 1000000007, 1000000009
        period = m1*m2
        problem = {'parameters': 1, 'inequalities': [
            {'a': -1, 'rhs': [0, -1]}, {'a': 1, 'rhs': [period-1, 1]}],
            'congruences': [{'a': 1, 'rhs': [1, 2], 'm': m1},
                            {'a': 1, 'rhs': [-3, 5], 'm': m2}]}
        cert = pb.synthesize(problem)
        self.assertTrue(pb.check(problem, cert))
        self.assertEqual(cert['program']['period'], period)
        self.assertLess(len(cert['program']['nodes']), 100)
        for x in [0, -1, 1, -10**100, 10**100]:
            feasible, witness = pb.evaluate_program(cert['program'], [x])
            self.assertTrue(feasible)
            self.assertTrue(pb.holds(problem, [x], witness))

    def test_mutated_projection_receipts(self):
        problem = {'parameters': 1, 'inequalities': [
            {'a': -1, 'rhs': [0, 1]}, {'a': 1, 'rhs': [10, 1]}],
            'congruences': [{'a': 2, 'rhs': [0, 1], 'm': 6}]}
        cert = pb.synthesize(problem)
        for mutate in [lambda c: c['bezout'][0].__setitem__(1, 111),
                       lambda c: c['program'].__setitem__('guards', []),
                       lambda c: c['program'].__setitem__('witness', 0),
                       lambda c: c['program'].__setitem__('period', 0),
                       lambda c: c['bezout'][0].__setitem__(0, True),
                       lambda c: c['program']['nodes'][0].__setitem__(1, 0.0)]:
            bad = copy.deepcopy(cert)
            mutate(bad)
            self.assertFalse(pb.check(problem, bad))


if __name__ == '__main__':
    unittest.main()
