"""Cone / dictionary-SOS search. Ported from p5, p7, p8 and p9 suites."""
from dataclasses import replace
from fractions import Fraction as Q
import pytest
from forge.poly import Poly
from forge.certificates import ConeTerm, ConeCertificate, check_cone
from forge.cone import discover, goal_square_bases, square_dictionary


@pytest.mark.parametrize('offset', [1, 2, 3, 5, 7])
def test_automatic_binomial_squares(offset):
    """p5: the square root is inferred from the goal, not supplied by hand."""
    x = Poly.var(1, 0)
    p = (x - offset) ** 2
    r = discover(p, degree=2)
    assert r.status == 'proved' and check_cone(p, (), (), r.certificate)


def test_cauchy_schwarz_without_manual_square_hint():
    x, y, u, v = [Poly.var(4, i) for i in range(4)]
    p = (x * x + y * y) * (u * u + v * v) - (x * u + y * v) ** 2
    r = discover(p, degree=4)
    assert r.status == 'proved' and check_cone(p, (), (), r.certificate)


@pytest.mark.parametrize('degree', range(1, 4))
def test_positive_constraint_products(degree):
    """p5: repeated products of the hypotheses are part of the dictionary."""
    x = Poly.var(1, 0)
    gs = (x, 1 - x)
    p = x ** degree * (1 - x) ** degree
    r = discover(p, gs, degree=2 * degree)
    assert r.status == 'proved' and check_cone(p, gs, (), r.certificate)


def test_equality_ideal():
    x, y = Poly.var(2, 0), Poly.var(2, 1)
    p = y * y - 2 * x + 1
    es = (y - x,)
    r = discover(p, (), es, degree=2)
    assert r.status == 'proved' and check_cone(p, (), es, r.certificate)


def test_signed_ideal_columns_also_work():
    """p8: +/- ideal columns, for a solver restricted to nonnegative bounds."""
    x, y = Poly.var(2, 0), Poly.var(2, 1)
    p = x * x + y * y - Q(1, 2)
    es = (x + y - 1,)
    r = discover(p, (), es, degree=2, signed_ideal=True)
    assert r.status == 'proved' and check_cone(p, (), es, r.certificate)


@pytest.mark.parametrize('a,b', [(a, b) for a in range(1, 4) for b in range(1, 4)])
def test_product_certificate_and_ablations(a, b):
    """p8: the binomial/product ablation flags genuinely change reachability."""
    x, y = Poly.var(2, 0), Poly.var(2, 1)
    target = x * y - a * b
    ge = (x - a, y - b)
    r = discover(target, ge, degree=2)
    assert r.status == 'proved' and check_cone(target, ge, (), r.certificate)
    off = discover(target, ge, degree=2, products=1, binomials=False)
    assert off.status == 'unknown'


@pytest.mark.parametrize('seed', range(10))
def test_false_nonnegative_claims_are_not_certified(seed):
    """p5: a false claim must come back UNKNOWN, never proved."""
    x = Poly.var(1, 0)
    p = (x - seed) ** 2 - Q(1, 1000)
    assert p.evaluate([seed]) < 0
    assert discover(p, degree=2).status == 'unknown'


def test_motzkin_is_outside_the_dictionary():
    """p2/p8: a true statement outside the finite cone is UNKNOWN, not false."""
    x, y = Poly.var(2, 0), Poly.var(2, 1)
    motzkin = x ** 4 * y ** 2 + x ** 2 * y ** 4 + 1 - 3 * x ** 2 * y ** 2
    assert discover(motzkin, degree=6, max_generators=800).status == 'unknown'


def test_budgets_return_unknown_with_a_reason():
    """p5: every abstention carries a machine-readable reason."""
    x = Poly.var(1, 0)
    assert discover(x * x, degree=1).reason == 'target exceeds degree cap'
    r = discover(x * x, degree=4, max_generators=1)
    assert r.status == 'unknown' and 'budget' in r.reason
    with pytest.raises(ValueError):
        discover(x * x, degree=-1)
    with pytest.raises(ValueError):
        discover(x * x, (Poly.var(2, 0),))


def test_shifted_square_with_positive_rational_margin():
    x = Poly.var(1, 0)
    p = (x - Q(2, 3)) ** 2 + Q(1, 97)
    r = discover(p, degree=2)
    assert r.certificate and check_cone(p, (), (), r.certificate)


def test_checker_is_more_general_than_the_search():
    """p9: abstaining on a true square is honest incompleteness, not falsity."""
    x, y = Poly.var(2, 0), Poly.var(2, 1)
    p = (x + y + 1) ** 2
    direct = ConeCertificate((ConeTerm(Q(1), x + y + 1, ()),))
    assert check_cone(p, (), (), direct)


def test_goal_square_bases_are_finite_and_deduplicated():
    x, y = Poly.var(2, 0), Poly.var(2, 1)
    bases = goal_square_bases(x * x + y * y - 2 * x * y)
    assert len(bases) == len(set(bases))
    assert (x - y) in bases or (y - x) in bases
    assert len(goal_square_bases(x ** 2 + y ** 2, limit=2)) <= 2


def test_square_dictionary_ablation():
    n = len(square_dictionary(2, 1, binomials=False))
    assert n == 3
    assert len(square_dictionary(2, 1, binomials=True)) > n
