"""Witness families. Ported from p2, p1, p7, p4 and p9."""
from dataclasses import replace
from fractions import Fraction as Q
from itertools import product
from math import gcd
import random
import pytest
from forge.poly import Poly
from forge.certificates import check_cone
from forge.witness.affine import (Affine, WitnessProblem, WitnessCertificate,
                                  synthesize_witness, check_witness,
                                  AffineWitness, check_affine_witness,
                                  synthesize_affine_witness)
from forge.witness import lattice, modular
from forge.witness.polynomial import synthesize_majorant


# --------------------------------------------------------------------------
# p2: affine Skolem witnesses with Farkas multipliers.
# --------------------------------------------------------------------------
def test_affine_terms_not_single_model_values():
    p = WitnessProblem(1, 1, (), (Affine.make([-1, 1], -1), Affine.make([1, -1], 2)))
    assert synthesize_witness(p, constant_only=True) is None
    c = synthesize_witness(p)
    assert c is not None and check_witness(p, c)
    assert c.witnesses[0].coefficients == (Q(1),)


def test_domain_farkas_multipliers():
    p = WitnessProblem(1, 1, (Affine.make([1]),),
                       (Affine.make([-1, 1]), Affine.make([2, -1])))
    c = synthesize_witness(p)
    assert c is not None and check_witness(p, c)


def test_unsatisfiable_goal_not_certified():
    p = WitnessProblem(1, 1, (), (Affine.make([0, 1], -1), Affine.make([0, -1])))
    assert synthesize_witness(p) is None


@pytest.mark.parametrize('bad', ['witness', 'slack_sign', 'float_slack',
                                 'multiplier_sign', 'wrong_count'])
def test_corrupted_affine_witness_rejected(bad):
    p = WitnessProblem(1, 1, (), (Affine.make([-1, 1], -1), Affine.make([1, -1], 2)))
    c = synthesize_witness(p)
    assert c is not None
    if bad == 'witness':
        c = replace(c, witnesses=(Affine.make([0], 1),))
    elif bad == 'slack_sign':
        c = replace(c, slacks=(Q(-1), Q(1)))
    elif bad == 'float_slack':
        c = replace(c, slacks=(0.0, 1.0))
    elif bad == 'multiplier_sign':
        c = replace(c, multipliers=((Q(-1),), (Q(-1),)))
    else:
        c = replace(c, slacks=(Q(0),))
    assert not check_witness(p, c)


def test_affine_rejects_inexact_coefficients():
    with pytest.raises(TypeError):
        Affine((0.1,), Q(0))
    with pytest.raises(ValueError):
        WitnessProblem(0, 1, (), ())
    with pytest.raises(ValueError):
        WitnessProblem(1, 1, (Affine.make([1, 1]),), (Affine.make([1, 1]),))


# --------------------------------------------------------------------------
# p1: parametric integral affine witnesses.
# --------------------------------------------------------------------------
def test_integral_affine_witness():
    A, B, c = [[1, 2], [0, 1]], [[3, -1], [2, 4]], [5, -3]
    w = synthesize_affine_witness(A, B, c, True)
    assert w is not None and check_affine_witness(A, B, c, w, True)
    assert all(v.denominator == 1 for row in w.linear for v in row)
    bad = AffineWitness(w.linear, (w.offset[0] + 1, w.offset[1]))
    assert not check_affine_witness(A, B, c, bad, True)
    assert not check_affine_witness(A, B, c, AffineWitness((), ()), True)


def test_integral_mode_rejects_a_rational_solution():
    A, B, c = [[2]], [[1]], [1]
    rational_witness = synthesize_affine_witness(A, B, c, False)
    assert rational_witness is not None
    assert rational_witness.linear[0][0] == Q(1, 2)
    assert synthesize_affine_witness(A, B, c, True) is None


def test_affine_witness_shape_validation():
    with pytest.raises(ValueError):
        synthesize_affine_witness([], [], [])
    with pytest.raises(ValueError):
        synthesize_affine_witness([[1, 2]], [[1]], [1, 2])


# --------------------------------------------------------------------------
# p7: integer lattice witnesses. The 539-case one-row grid is the key test.
# --------------------------------------------------------------------------
def test_one_row_gcd_grid():
    """p7: 7*7*11 = 539 cases, expected status taken independently from math.gcd."""
    checked = feasible = infeasible = 0
    for a, b, rhs in product(range(-3, 4), range(-3, 4), range(-5, 6)):
        A, bs = [[a, b]], [rhs]
        cert = lattice.solve(A, bs)
        g = gcd(a, b)
        expected = rhs == 0 if not g else rhs % g == 0
        assert cert.feasible == expected
        assert lattice.check(A, bs, cert)
        checked += 1
        feasible += expected
        infeasible += not expected
    assert checked == 539
    assert feasible + infeasible == 539 and feasible and infeasible


@pytest.mark.parametrize('seed', range(20))
def test_random_feasible_lattice_systems(seed):
    """p7: the returned basis must span genuine solutions of every input row."""
    rng = random.Random(seed)
    m, n = rng.randint(1, 5), rng.randint(1, 6)
    A = [[rng.randint(-9, 9) for _ in range(n)] for _ in range(m)]
    hidden = [rng.randint(-20, 20) for _ in range(n)]
    bs = lattice.matvec(A, hidden)
    cert = lattice.solve(A, bs)
    assert cert.feasible and lattice.check(A, bs, cert)
    B = cert.basis
    d = len(B[0]) if B else 0
    for _ in range(4):
        z = [rng.randint(-5, 5) for _ in range(d)]
        x = [u + lattice.dot(row, z) for u, row in zip(cert.witness, B)]
        assert lattice.matvec(A, x) == bs
    bad = replace(cert, witness=(cert.witness[0] + 1,) + cert.witness[1:])
    assert not lattice.check(A, bs, bad)
    first = cert.steps[0]
    bad = replace(cert, steps=(replace(first, residual=first.residual + 1),) + cert.steps[1:])
    assert not lattice.check(A, bs, bad)


@pytest.mark.parametrize('j', range(10))
def test_prefix_obstructions(j):
    """p7: inconsistency that only appears after a consistent prefix."""
    A, bs = [[1, 1, 0], [2, 2, 0]], [j, 2 * j + 1]
    cert = lattice.solve(A, bs)
    assert not cert.feasible and lattice.check(A, bs, cert)
    assert cert.steps[-1].obstruction


def test_lattice_input_validation():
    with pytest.raises(ValueError):
        lattice.solve([], [])
    with pytest.raises(TypeError):
        lattice.solve([[1.0]], [1])
    with pytest.raises(ValueError):
        lattice.solve([[1, 2], [3]], [1, 2])
    assert lattice.determinant([[1, 0], [0, 1]]) == 1


# --------------------------------------------------------------------------
# p4: finite-residue modular witnesses.
# --------------------------------------------------------------------------
@pytest.mark.parametrize('a,b,m', [(a, b, m) for a in range(1, 6)
                                   for b in range(0, 4) for m in (1, 2, 3, 5, 6)])
def test_modular_witness(a, b, m):
    cert = modular.synthesize(a, b, m)
    solvable = b % gcd(a, m) == 0
    assert (cert is not None) == solvable
    if cert is None:
        return
    assert modular.verify(a, b, m, cert)
    for n in range(-6, 7):
        k = modular.instantiate(n, m, cert)
        assert n <= k < n + m and (a * k - b) % m == 0
    bad = {'offsets': [cert['offsets'][0] + m] + cert['offsets'][1:]}
    assert not modular.verify(a, b, m, bad)


def test_modular_input_validation():
    with pytest.raises(ValueError):
        modular.synthesize(1, 1, 0)
    with pytest.raises(ValueError):
        modular.synthesize(1, 1, 1.5)
    assert not modular.verify(3, 1, 5, {'offsets': []})
    assert not modular.verify(3, 1, 5, {})


# --------------------------------------------------------------------------
# p9: polynomial majorant witnesses.
# --------------------------------------------------------------------------
def test_witness_is_universally_certified():
    w, certs, stats = synthesize_majorant()
    x = Poly.var(1, 0)
    assert w == x * x + 1 and certs
    assert stats['status'] == 'certified'
    assert check_cone(w - x, (), (), certs[0])
    assert check_cone(w + x, (), (), certs[1])
    assert w.evaluate((Q(1, 2),)) == Q(5, 4)
    # Sampling alone would have accepted x^2, which is NOT a majorant of |x|.
    assert (x * x).evaluate((Q(1, 2),)) < abs(Q(1, 2))


def test_majorant_abstains_when_the_grammar_is_too_small():
    w, certs, stats = synthesize_majorant(bound=0)
    assert w is None and certs is None and stats['status'] == 'no_certificate'
