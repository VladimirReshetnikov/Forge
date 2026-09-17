"""The Gram-matrix SOS search (forge/gram.py).

Search code, not trusted: every certificate it returns is replayed by the exact
checker here and by the Lean kernel downstream. These tests pin what it finds,
and -- more importantly -- that it returns nothing for polynomials that are not
sums of squares.
"""
from fractions import Fraction as Q

from forge.certificates import check_cone
from forge.gram import gram_sos
from forge.poly import Poly


def P(n, terms):
    return Poly.make(n, [(tuple(e), Q(c)) for e, c in terms])


def assert_certified(p):
    cert = gram_sos(p, timeout_seconds=20)
    assert cert is not None
    assert check_cone(p, [], [], cert)
    assert all(t.weight >= 0 for t in cert.terms)
    return cert


def test_fourth_power_needs_a_trinomial_square():
    """(x - y)^4 expanded: the case the dictionary search missed in the
    tactic head-to-head. Its only Gram matrix is singular, so the exact
    reconstruction has to land on the boundary of the PSD cone."""
    cert = assert_certified(P(2, [((4, 0), 1), ((3, 1), -4), ((2, 2), 6),
                                  ((1, 3), -4), ((0, 4), 1)]))
    assert len(cert.terms) == 1


def test_quartic_two_variables():
    assert_certified(P(2, [((4, 0), 1), ((0, 4), 1), ((3, 1), -1), ((1, 3), -1)]))


def test_degree_six():
    assert_certified(P(2, [((6, 0), 1), ((0, 6), 1), ((3, 3), -2)]))


def test_three_variables_quartic():
    # x^4 + y^4 + z^4 - x^2 y^2 - y^2 z^2 - z^2 x^2
    assert_certified(P(3, [((4, 0, 0), 1), ((0, 4, 0), 1), ((0, 0, 4), 1),
                           ((2, 2, 0), -1), ((0, 2, 2), -1), ((2, 0, 2), -1)]))


def test_motzkin_is_not_certified():
    """Nonnegative, but provably not a sum of squares. A `None` here is the
    correct answer, and a certificate would mean the checker is broken."""
    assert gram_sos(P(2, [((4, 2), 1), ((2, 4), 1), ((2, 2), -3), ((0, 0), 1)]),
                    timeout_seconds=10) is None


def test_negative_polynomials_are_not_certified():
    assert gram_sos(P(2, [((2, 0), 1), ((0, 2), -2)])) is None
    assert gram_sos(P(1, [((4,), 1), ((2,), -1)])) is None
    assert gram_sos(P(1, [((2,), -1)])) is None


def test_odd_degree_is_unknown_not_a_crash():
    assert gram_sos(P(1, [((3,), 1)])) is None
