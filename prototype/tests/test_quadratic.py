"""Exact Schur-complement quadratics. Ported from p1's and p3's suites."""
from dataclasses import replace
from fractions import Fraction as Q
import random
import pytest
from forge.poly import Poly
from forge.certificates import check_cone
from forge.quadratic import quadratic_sos, solve_quadratic


def variables(n):
    return [Poly.var(n, i) for i in range(n)]


@pytest.mark.parametrize('seed', range(60))
def test_quadratic_generated(seed):
    """p1: planted sums of weighted affine squares are always recovered."""
    rng = random.Random(seed)
    n = 1 + seed % 5
    xs = variables(n)
    p = Poly.const(n, 0)
    for _ in range(1 + seed % 7):
        q = Q(rng.randrange(-6, 7), rng.randrange(1, 5))
        linear = Poly.const(n, q)
        for x in xs:
            linear += Q(rng.randrange(-5, 6), rng.randrange(1, 5)) * x
        p += Q(rng.randrange(1, 8), rng.randrange(1, 4)) * linear ** 2
    cert = quadratic_sos(p)
    assert cert is not None and check_cone(p, [], [], cert)
    assert not check_cone(p + 1, [], [], cert)
    if cert.terms:
        bad = replace(cert, terms=(replace(cert.terms[0], weight=Q(-1)),) + cert.terms[1:])
        assert not check_cone(p, [], [], bad)


@pytest.mark.parametrize('seed', range(20))
def test_nonnegative_not_assumed(seed):
    """p1: indefinite quadratics abstain; None is never a claim of falsity."""
    x, y = variables(2)
    assert quadratic_sos((seed + 1) * x * y) is None
    assert quadratic_sos(-(seed + 1) * x * x + y * y) is None


def test_quadratic_edges():
    """p1: zero, constants, degenerate PSD and out-of-fragment inputs."""
    x, y = variables(2)
    for p in [Poly.const(2, 0), Poly.const(2, 3), (x - y) ** 2, (x + Q(1, 3)) ** 2]:
        cert = quadratic_sos(p)
        assert cert is not None and check_cone(p, [], [], cert)
    assert quadratic_sos(x + 1) is None
    assert quadratic_sos(x ** 4) is None
    assert quadratic_sos(x * x + Q(1, 10 ** 30) * x * y) is None


def test_p3_status_strings():
    """p3: machine-readable statuses over the same exact decomposition."""
    x, y = variables(2)
    cert, stats = solve_quadratic((x - y) ** 2)
    assert cert is not None and stats['status'] == 'checked_python'
    assert stats['pivots'] == stats['certificate_terms'] == len(cert.terms)
    assert solve_quadratic(x ** 4)[1]['status'] == 'unsupported_degree'
    assert solve_quadratic(x * y)[1]['status'] == 'unknown_non_psd'
