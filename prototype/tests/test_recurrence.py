"""Recurrences and accumulator invariants. Ported from p1, p2, p7 and p5."""
from dataclasses import replace
from fractions import Fraction as Q
import random
import pytest
from forge.poly import Poly
from forge.certificates import check_invariant
from forge.recurrence import (check_recurrence, synthesize_recurrence,
                              check_univariate_recurrence, synthesize_recurrence_cegis,
                              AccumulatorCertificate, check_accumulator,
                              synthesize_accumulator, run_accumulator,
                              changed_nonstructural_parameters, additive_invariant)


def test_triangular_closed_form():
    """p1/p2: the classic sum, synthesized exactly and re-checked."""
    x = Poly.var(1, 0)
    formula = synthesize_recurrence(x + 1, Poly.const(1, 0))
    assert formula == Q(1, 2) * x * (x + 1)
    assert check_recurrence(x + 1, Poly.const(1, 0), formula)


@pytest.mark.parametrize('degree', range(7))
def test_random_additive_recurrences(degree):
    """p2: closed forms agree with the unrolled recursion at many points."""
    rng = random.Random(410 + degree)
    for _ in range(4):
        f = Poly.make(1, [((k,), Q(rng.randrange(-5, 6), rng.randrange(1, 5)))
                          for k in range(degree + 1)])
        initial = Q(rng.randrange(-5, 6), 3)
        formula = synthesize_recurrence(f, Poly.const(1, initial), degree + 1)
        assert formula is not None
        assert check_recurrence(f, Poly.const(1, initial), formula)
        for n in range(12):
            assert formula.evaluate([n]) == initial + sum(f.evaluate([k]) for k in range(n))


def test_interpolation_is_not_a_certificate():
    """p2: agreeing on every sampled n is not a proof, and is not accepted."""
    x = Poly.var(1, 0)
    true = Q(1, 2) * x * (x + 1)
    false = true + x * (x - 1) * (x - 2) * (x - 3)
    assert all(true.evaluate([n]) == false.evaluate([n]) for n in range(4))
    assert not check_univariate_recurrence(x + 1, 0, false)
    assert not check_univariate_recurrence(x + 1, 1, true)
    assert not check_recurrence(x + 1, Poly.const(1, 0), false)


def test_degree_exhaustion_is_no_proof():
    """p2: running out of degree budget is UNKNOWN, not a disproof."""
    x = Poly.var(1, 0)
    assert synthesize_recurrence(x ** 3, Poly.const(1, 0), max_degree=3) is None
    assert synthesize_recurrence_cegis(x ** 3, Q(0), max_degree=3).polynomial is None
    with pytest.raises(ValueError):
        synthesize_recurrence(x, Poly.const(1, 0), max_degree=-1)


def test_cegis_diagnostic_reports_counterexamples():
    """p2's CEGIS loop, kept as a diagnostic: it must produce real witnesses."""
    x = Poly.var(1, 0)
    r = synthesize_recurrence_cegis(x + 1)
    assert r.polynomial == Q(1, 2) * x * (x + 1)
    assert check_univariate_recurrence(x + 1, Q(0), r.polynomial)
    assert r.counterexamples and r.candidates > 1
    for record in r.counterexamples:
        assert Q(record['step_residual']) != 0


def test_multivariate_recurrence():
    """p1: the merged synthesizer is multivariate, unlike p2's univariate one."""
    n, a = Poly.var(2, 0), Poly.var(2, 1)
    step = a * n
    formula = synthesize_recurrence(step, Poly.const(2, 0), 4)
    assert formula is not None and check_recurrence(step, Poly.const(2, 0), formula)
    assert formula == Q(1, 2) * a * n * (n - 1)


@pytest.mark.parametrize('power', range(5))
def test_accumulator_generalization(power):
    """p7: go(n+1,a) = go(n, a + r n), strengthened to a closed form in (n,a)."""
    n = Poly.var(2, 0)
    r = n ** power
    cert, stats = synthesize_accumulator(r)
    assert cert is not None and check_accumulator(r, cert)
    assert stats['generalized'] == ['a']
    for k in range(6):
        assert cert.invariant.evaluate([k, 3]) == run_accumulator(r, k, 3)
    assert not check_accumulator(r, replace(cert, invariant=cert.invariant + 1))


def test_accumulator_rejects_non_index_increment():
    a = Poly.var(2, 1)
    with pytest.raises(ValueError):
        synthesize_accumulator(a)
    assert not check_accumulator(a, AccumulatorCertificate(a))


def test_changed_nonstructural_parameters():
    """p7: the generalization trigger is read off the recursive call."""
    n, a = Poly.var(2, 0), Poly.var(2, 1)
    assert changed_nonstructural_parameters(('n', 'a'), (n, a + n), {0}) == ('a',)
    assert changed_nonstructural_parameters(('n', 'a'), (n, a), {0}) == ()
    with pytest.raises(ValueError):
        changed_nonstructural_parameters(('n',), (n, a), {0})


@pytest.mark.parametrize('power', range(9))
def test_additive_invariant_is_the_persisted_format(power):
    """p5: the persisted artefact is an InvariantCertificate, checked exactly."""
    x = Poly.var(1, 0)
    c = additive_invariant((x + 1) ** power)
    assert c is not None and check_invariant(c)
    assert not check_invariant(replace(c, invariant=c.invariant + 1))


def test_interpolation_does_not_count_as_proof():
    """p5: an increment vanishing at every sampled n is still not an invariant."""
    x = Poly.var(1, 0)
    p = x * (x - 1) * (x - 2)
    assert all(p.evaluate([n]) == 0 for n in range(3))
    assert additive_invariant(p, degree=2) is None
    assert additive_invariant(p) is not None
    with pytest.raises(ValueError):
        additive_invariant(Poly.var(2, 0))
