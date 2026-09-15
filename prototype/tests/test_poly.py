"""Exact polynomial kernel. Ported from p8, p5, p2 and p9 poly test suites."""
from fractions import Fraction as Q
from math import comb
from itertools import product
import random
import pytest
import sympy as sp
from forge.poly import (Poly, rational, monomials, monomial_exponents,
                        bernstein_coefficients, expand_bernstein)


@pytest.mark.parametrize('seed', range(30))
def test_poly_against_sympy(seed):
    """p8: differential arithmetic/evaluation against SymPy."""
    rng = random.Random(seed)
    xs = sp.symbols('x:2')

    def make():
        return Poly.make(2, {(i, j): Q(rng.randint(-8, 8), rng.randint(1, 5))
                             for i in range(3) for j in range(3 - i)})

    a, b = make(), make()

    def expr(p):
        return sum(sp.Rational(c.numerator, c.denominator) * xs[0] ** e[0] * xs[1] ** e[1]
                   for e, c in p.terms)

    assert sp.expand(expr(a * b) - expr(a) * expr(b)) == 0
    assert sp.expand(expr(a + b) - expr(a) - expr(b)) == 0
    pt = (Q(rng.randint(-3, 3), 2), Q(rng.randint(-3, 3), 3))
    actual = expr(a).subs(dict(zip(xs, [sp.Rational(v.numerator, v.denominator) for v in pt])))
    assert a.evaluate(pt) == Q(int(actual.p), int(actual.q))


def test_polynomial_domain_validation():
    """p8 + p5 + p2: floats and malformed canonical forms are rejected."""
    with pytest.raises(TypeError):
        Poly.const(1, 0.1)
    with pytest.raises(TypeError):
        Poly.make(1, {(0,): 0.0})  # p8: even a ZERO float is rejected
    with pytest.raises(TypeError):
        rational(0.0)
    with pytest.raises(ValueError):
        Poly(1, (((-1,), Q(1)),))
    with pytest.raises(ValueError):
        Poly(1, (((1,), Q(0)),))
    with pytest.raises(ValueError):
        Poly(1, (((1,), Q(1)), ((1,), Q(1))))
    with pytest.raises(ValueError):
        Poly.var(1, 2)
    with pytest.raises(ValueError):
        Poly.var(1, 0) + Poly.var(2, 0)
    with pytest.raises(ValueError):
        Poly.var(1, 0) ** -1
    with pytest.raises(ValueError):
        Poly.make(2, [((1,), 1)])


def test_from_json_rejects_duplicate_monomials():
    """p7: a duplicate monomial is never canonical input."""
    p = Poly.make(2, {(1, 0): Q(1), (0, 1): Q(-3, 2)})
    assert Poly.from_json(p.json()) == p
    bad = p.json()
    bad['terms'].append([[1, 0], '1'])
    with pytest.raises(ValueError):
        Poly.from_json(bad)


def test_monomial_enumeration_scaling():
    """p8: weak compositions, not a (d+1)^n grid."""
    ms = monomials(10, 3)
    assert len(ms) == comb(13, 3)
    assert len(set(ms)) == len(ms)
    assert all(m.degree <= 3 for m in ms)
    assert monomial_exponents(3, 2) == sorted(monomial_exponents(3, 2),
                                              key=lambda e: (sum(e), e))
    assert all(sum(e) <= 2 for e in monomial_exponents(3, 2))


def test_degrees_property():
    x, y = Poly.var(2, 0), Poly.var(2, 1)
    assert (x ** 3 * y + y ** 5).degrees == (3, 5)
    assert Poly.const(2, 0).degrees == (0, 0)


@pytest.mark.parametrize('seed', range(15))
def test_bernstein_round_trip(seed):
    """p8: convert to Bernstein, then replay by INDEPENDENT basis expansion."""
    rng = random.Random(seed)
    p = Poly.make(2, {(i, j): Q(rng.randint(-5, 5)) for i in range(3) for j in range(3)})
    box = ((Q(-2), Q(3)), (Q(1), Q(4)))
    ds, cs = bernstein_coefficients(p, box)
    assert expand_bernstein(2, ds, cs) == p.affine_box(box)


@pytest.mark.parametrize('seed', range(20))
def test_bernstein_identity_at_sampled_points(seed):
    """p2: the tensor Bernstein sum must equal p on the affine image, exactly."""
    rng = random.Random(400 + seed)
    n = 1 + seed % 2
    p = Poly.make(n, [(tuple(rng.randrange(4) for _ in range(n)), rng.randrange(-5, 6))
                      for _ in range(5)])
    box = tuple([(Q(-1), Q(2))] * n)
    ds, cs = bernstein_coefficients(p, box)
    t = [Q(rng.randrange(1, 5), 5) for _ in range(n)]
    total = Q(0)
    for alpha, c in zip(product(*(range(d + 1) for d in ds)), cs):
        b = c
        for a, d, v in zip(alpha, ds, t):
            b *= comb(d, a) * v ** a * (1 - v) ** (d - a)
        total += b
    assert total == p.evaluate([-1 + 3 * v for v in t])


def test_affine_box_requires_positive_width():
    x = Poly.var(1, 0)
    with pytest.raises(ValueError):
        x.affine_box(((Q(1), Q(1)),))
    with pytest.raises(ValueError):
        x.affine_box(((Q(2), Q(1)),))


def test_expand_bernstein_rejects_malformed_vectors():
    with pytest.raises(ValueError):
        expand_bernstein(1, (2,), (Q(1), Q(1)))
    with pytest.raises(ValueError):
        expand_bernstein(2, (1,), (Q(1), Q(1)))
