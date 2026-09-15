from __future__ import annotations
import copy
from dataclasses import replace as dc_replace
from fractions import Fraction as Q
from itertools import product
from math import comb
import random
import unittest

from forge_proto.poly import Poly, bernstein_coefficients
from forge_proto.linear import solve_exact, exact_feasible
from forge_proto.recurrence import check_recurrence, synthesize_recurrence
from forge_proto.positivity import (search_sos, check_sos, square_dictionary, SOSCertificate,
    WeightedSquare, search_bernstein, check_bernstein)
from forge_proto.witness import (Affine, WitnessProblem, WitnessCertificate,
    synthesize_witness, check_witness)
from forge_proto.induction import *


class PolynomialTests(unittest.TestCase):
    def test_sparse_arithmetic_random_evaluation(self):
        rng = random.Random(401)
        for _ in range(80):
            n = rng.randrange(1, 4)
            p = Poly.make(n, [(tuple(rng.randrange(3) for _ in range(n)), rng.randrange(-5, 6)) for _ in range(5)])
            q = Poly.make(n, [(tuple(rng.randrange(3) for _ in range(n)), rng.randrange(-5, 6)) for _ in range(5)])
            at = [Q(rng.randrange(-4, 5), 3) for _ in range(n)]
            self.assertEqual((p + q).evaluate(at), p.evaluate(at) + q.evaluate(at))
            self.assertEqual((p * q).evaluate(at), p.evaluate(at) * q.evaluate(at))
            self.assertEqual(Poly.from_json(p.to_json()), p)

    def test_bernstein_identity_random_exact(self):
        rng = random.Random(402)
        for _ in range(40):
            n = rng.randrange(1, 3)
            p = Poly.make(n, [(tuple(rng.randrange(4) for _ in range(n)), rng.randrange(-5, 6)) for _ in range(5)])
            box = [(Q(-1), Q(2))] * n
            t = [Q(rng.randrange(1, 5), 5) for _ in range(n)]
            cs, ds = bernstein_coefficients(p, box), p.degrees()
            total = Q(0)
            for alpha, c in zip(product(*(range(d + 1) for d in ds)), cs):
                b = c
                for a, d, x in zip(alpha, ds, t):
                    b *= comb(d, a) * x ** a * (1 - x) ** (d - a)
                total += b
            self.assertEqual(total, p.evaluate([-1 + 3 * v for v in t]))

    def test_invalid_polynomial(self):
        with self.assertRaises(ValueError): Poly.make(2, [((1,), 1)])
        with self.assertRaises(ValueError): Poly.make(1, [((-1,), 1)])
        with self.assertRaises(TypeError): Poly.make(1, [((0,), 0.1)])
        with self.assertRaises(ValueError): Poly(1, (((0,), Q(1)), ((0,), Q(2))))

    def test_exact_linear_solver(self):
        self.assertEqual(solve_exact([[1, 1], [1, -1]], [3, 1]), [Q(2), Q(1)])
        self.assertIsNone(solve_exact([[0]], [1]))
        self.assertEqual(solve_exact([[1, 2]], [3]), [Q(3), Q(0)])
        self.assertEqual(exact_feasible([[1]], [Q(3, 7)], [True]), [Q(3, 7)])
        self.assertIsNone(exact_feasible([[Q(10) ** 10000]], [1], [True]))
        with self.assertRaises(ValueError):
            exact_feasible([[1, 2]], [1], [True])


class RecurrenceTests(unittest.TestCase):
    def test_triangular_closed_form(self):
        x = Poly.variable(1, 0)
        r = synthesize_recurrence(x + 1)
        self.assertEqual(r.polynomial, Q(1, 2) * x * (x + 1))
        self.assertTrue(check_recurrence(x + 1, 0, r.polynomial))
        self.assertGreater(len(r.counterexamples), 0)

    def test_random_additive_recurrences(self):
        rng = random.Random(410)
        for degree in range(7):
            for _ in range(8):
                f = Poly.make(1, [((k,), Q(rng.randrange(-5, 6), rng.randrange(1, 5))) for k in range(degree + 1)])
                initial = Q(rng.randrange(-5, 6), 3)
                r = synthesize_recurrence(f, initial, degree + 1)
                self.assertIsNotNone(r.polynomial)
                self.assertTrue(check_recurrence(f, initial, r.polynomial))
                for n in range(12):
                    self.assertEqual(r.polynomial.evaluate([n]), initial + sum(f.evaluate([k]) for k in range(n)))

    def test_interpolation_is_not_a_certificate(self):
        x = Poly.variable(1, 0)
        true = Q(1, 2) * x * (x + 1)
        false = true + x * (x - 1) * (x - 2) * (x - 3)
        self.assertTrue(all(true.evaluate([n]) == false.evaluate([n]) for n in range(4)))
        self.assertFalse(check_recurrence(x + 1, 0, false))
        self.assertFalse(check_recurrence(x + 1, 1, true))

    def test_degree_exhaustion_is_no_proof(self):
        x = Poly.variable(1, 0)
        self.assertIsNone(synthesize_recurrence(x ** 3, max_degree=3).polynomial)


class InductionTests(unittest.TestCase):
    def test_seed_theorems_have_replayable_proofs(self):
        t = demonstration_theory()
        replay = Theory()
        for name, cert in t.certificates.items():
            self.assertTrue(replay.install(name, cert))

    def test_automatic_accumulator_generalization(self):
        t = demonstration_theory()
        goal = Equation(RA(V("xs"), N()), R(V("xs")))
        self.assertIsNone(t.search(goal, "xs"))
        d = discover_accumulator_lemma(t, goal)
        self.assertEqual(d.changed_arguments, (1,))
        self.assertEqual(d.equation, Equation(RA(V("xs"), V("acc1")), A(R(V("xs")), V("acc1"))))
        self.assertTrue(t.install("revacc_spec", d.certificate))
        self.assertIsNotNone(t.search(goal, "xs"))
        self.assertEqual((d.enumerated, d.sample_survivors), (32, 1))

    def test_small_grammar_limit_returns_no_proof(self):
        t = demonstration_theory()
        goal = Equation(RA(V("xs"), N()), R(V("xs")))
        self.assertIsNone(discover_accumulator_lemma(t, goal, max_size=3).certificate)

    def test_rigid_induction_tail(self):
        # The IH at tail must NOT be rewritten as a universally applicable theorem.
        eq = Equation(RA(V("xs"), N()), R(V("xs")))
        _, _, ih = induction_obligations(eq, "xs")
        self.assertIsNone(match(ih.eq.left, RA(F("different-tail"), N())))
        self.assertIsNone(match(ih.eq.left, RA(C(F("h", "E"), F("induction:tail")), N())))

    def test_false_reverse_identity_not_proved(self):
        t = demonstration_theory()
        self.assertIsNone(t.search(Equation(R(V("xs")), V("xs")), "xs"))

    def test_unknown_or_cyclic_rule_rejected(self):
        t = demonstration_theory()
        cert = t.certificates["reverse_involution"]
        forged = dc_replace(cert, step=EqualityTrace((RewriteStep("unproved-self", ()),), ()))
        self.assertFalse(Theory().install("unproved-self", forged))

    def test_trace_corruption_and_dependency_loss(self):
        t = demonstration_theory()
        cert = t.certificates["reverse_involution"]
        self.assertFalse(Theory().check(cert))  # reverse_append is unavailable
        forged = dc_replace(cert, step=EqualityTrace((RewriteStep("def.rev.nil", (999,)),), ()))
        self.assertFalse(t.check(forged))

    def test_sort_mismatch_rejected(self):
        with self.assertRaises(ValueError): A(V("head", "E"), N())
        with self.assertRaises(ValueError): C(V("xs"), N())
        self.assertIsNone(match(V("x", "E"), N()))

    def test_random_semantic_crosscheck(self):
        t, rng = demonstration_theory(), random.Random(411)
        for _ in range(100):
            values = {name: tuple(rng.randrange(5) for _ in range(rng.randrange(12)))
                      for name in ("xs", "ys", "zs")}
            for c in t.certificates.values():
                self.assertEqual(evaluation(c.equation.left, values), evaluation(c.equation.right, values))


class PositivityTests(unittest.TestCase):
    def test_sos_with_exact_replay(self):
        x, y = Poly.variable(2, 0), Poly.variable(2, 1)
        p = (x - y) ** 2 + 2 * (x + 1) ** 2 + Q(1, 3)
        cert = search_sos(p, square_dictionary(2, 2))
        self.assertIsNotNone(cert)
        self.assertTrue(check_sos(p, (), cert))
        self.assertFalse(check_sos(p + 1, (), cert))

    def test_constraint_multiplied_squares(self):
        x = Poly.variable(1, 0)
        p = x * (1 - x)
        cert = search_sos(p, square_dictionary(1, 1), [x, 1 - x])
        self.assertIsNotNone(cert)
        self.assertTrue(check_sos(p, [x, 1 - x], cert))
        self.assertFalse(check_sos(p, [], cert))

    def test_negative_weights_rejected(self):
        x = Poly.variable(1, 0)
        cert = SOSCertificate((WeightedSquare(Q(-1), x),))
        self.assertFalse(check_sos(-x ** 2, [], cert))

    def test_nonsos_and_negative_targets_not_accepted(self):
        x, y = Poly.variable(2, 0), Poly.variable(2, 1)
        self.assertIsNone(search_sos(-x ** 2, square_dictionary(2, 1)))
        motzkin = x ** 4 * y ** 2 + x ** 2 * y ** 4 + 1 - 3 * x ** 2 * y ** 2
        self.assertIsNone(search_sos(motzkin, square_dictionary(2, 3)))

    def test_subdivision_adds_a_certificate(self):
        x = Poly.variable(1, 0)
        p = (x - Q(1, 2)) ** 2 + Q(1, 100)
        root = search_bernstein(p, [(0, 1)], max_depth=0)
        full = search_bernstein(p, [(0, 1)], max_depth=1, strict=True)
        self.assertEqual(root.status, "unknown")
        self.assertEqual(full.status, "certified")
        self.assertEqual(full.leaves, 2)
        self.assertTrue(check_bernstein(p, [(0, 1)], full.tree, strict=True))

    def test_partition_corruption_rejected(self):
        x = Poly.variable(1, 0)
        p = (x - Q(1, 2)) ** 2 + Q(1, 100)
        tree = search_bernstein(p, [(0, 1)]).tree
        bad = copy.deepcopy(tree); bad["point"] = "0"
        self.assertFalse(check_bernstein(p, [(0, 1)], bad))
        bad = copy.deepcopy(tree); del bad["right"]
        self.assertFalse(check_bernstein(p, [(0, 1)], bad))
        bad = copy.deepcopy(tree); bad["axis"] = 1
        self.assertFalse(check_bernstein(p, [(0, 1)], bad))
        self.assertFalse(check_bernstein(p, [(0, 1)], {"kind": "leaf"}))

    def test_refutation_is_a_checked_point(self):
        x = Poly.variable(1, 0)
        p = x ** 2 - Q(1, 2)
        r = search_bernstein(p, [(-1, 1)])
        self.assertEqual(r.status, "refuted")
        self.assertLess(p.evaluate(r.counterexample), 0)

    def test_strict_and_weak_signs_distinguished(self):
        x = Poly.variable(1, 0)
        self.assertEqual(search_bernstein(x ** 2, [(0, 1)]).status, "certified")
        self.assertEqual(search_bernstein(x ** 2, [(0, 1)], strict=True).status, "refuted")
        self.assertFalse(check_bernstein(x ** 2, [(0, 1)], {"kind": "leaf"}, strict=True))

    def test_diagonal_square_budget_unknown_not_false(self):
        x, y = Poly.variable(2, 0), Poly.variable(2, 1)
        r = search_bernstein((x - y) ** 2, [(0, 1), (0, 1)], max_depth=4)
        self.assertEqual(r.status, "unknown")
        self.assertIsNone(r.counterexample)


class WitnessTests(unittest.TestCase):
    def test_affine_terms_not_single_model_values(self):
        p = WitnessProblem(1, 1, (), (Affine.make([-1, 1], -1), Affine.make([1, -1], 2)))
        self.assertIsNone(synthesize_witness(p, constant_only=True))
        c = synthesize_witness(p)
        self.assertIsNotNone(c)
        self.assertTrue(check_witness(p, c))
        self.assertEqual(c.witnesses[0].coefficients, (Q(1),))

    def test_domain_farkas_multipliers(self):
        # x>=0, exists y with y>=x and y<=2x. Witness y=x suffices.
        p = WitnessProblem(1, 1, (Affine.make([1]),),
                           (Affine.make([-1, 1]), Affine.make([2, -1])))
        c = synthesize_witness(p)
        self.assertIsNotNone(c)
        self.assertTrue(check_witness(p, c))

    def test_unsatisfiable_goal_not_certified(self):
        p = WitnessProblem(1, 1, (), (Affine.make([0, 1], -1), Affine.make([0, -1])))
        self.assertIsNone(synthesize_witness(p))

    def test_corrupted_witness_rejected(self):
        p = WitnessProblem(1, 1, (), (Affine.make([-1, 1], -1), Affine.make([1, -1], 2)))
        c = synthesize_witness(p)
        bad = dc_replace(c, witnesses=(Affine.make([0], 1),))
        self.assertFalse(check_witness(p, bad))
        self.assertFalse(check_witness(p, dc_replace(c, slacks=(Q(-1), Q(1)))))

    def test_inexact_certificate_rejected(self):
        with self.assertRaises(TypeError): Affine((0.1,), Q(0))
        p = WitnessProblem(1, 1, (), (Affine.make([-1, 1], -1), Affine.make([1, -1], 2)))
        c = synthesize_witness(p)
        self.assertFalse(check_witness(p, dc_replace(c, slacks=(0.0, 1.0))))


if __name__ == "__main__":
    unittest.main(verbosity=2)
