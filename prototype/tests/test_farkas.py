"""Farkas refutations: the exact checker mirrors Lean's FarkasCert.check."""
from itertools import product

import pytest

from forge.witness.farkas import FarkasCertificate, check_farkas, synthesize_farkas
from forge.io.decode import DecodeError, verify

C = FarkasCertificate


def test_textbook_system_is_refuted():
    rows, bounds = [[1, 1], [-1, 0], [0, -1]], [1, -1, -1]
    cert = synthesize_farkas(rows, bounds)
    assert cert is not None and check_farkas(2, rows, bounds, cert)
    assert all(isinstance(v, int) and v >= 0 for v in cert.multipliers)


def test_rational_multipliers_are_scaled_to_integers():
    # 2x <= -1 and -3x <= 1 say x <= -1/2 and x >= -1/3; the refutation is (3, 2).
    rows, bounds = [[2], [-3]], [-1, 1]
    cert = synthesize_farkas(rows, bounds)
    assert cert is not None and check_farkas(1, rows, bounds, cert)


def test_feasible_systems_get_no_certificate():
    for a, b, c, d in product(range(-2, 3), repeat=4):
        rows, bounds = [[a], [b]], [c, d]
        feasible = any(a * x <= c and b * x <= d for x in range(-20, 21))
        cert = synthesize_farkas(rows, bounds)
        if feasible:
            assert cert is None
        elif cert is not None:
            assert check_farkas(1, rows, bounds, cert)


def test_each_conjunct_rejects():
    rows, bounds = [[1], [-1]], [-1, 0]
    assert check_farkas(1, rows, bounds, C((1, 1)))
    assert not check_farkas(1, [[1], [1]], [-1, 0], C((1, -1)))   # sign
    assert not check_farkas(1, [[1], [-1]], [0, 0], C((1, 1)))    # strictness
    assert not check_farkas(1, rows, bounds, C((1, 2)))           # combination
    assert not check_farkas(1, rows, bounds, C((1, 1, 0)))        # arity
    assert not check_farkas(2, [[1, 0], [-1, 0, 5]], bounds, C((1, 1)))  # width
    assert not check_farkas(1, [[0], [1]], [-1, 0], C((0, 0)))    # all zero
    assert check_farkas(1, [[0], [1]], [-1, 0], C((1, 0)))
    assert not check_farkas(0, [], [], C(()))                     # empty
    assert not check_farkas(1, rows, bounds, C((True, True)))      # bools are not ints


def test_decoder_bounds_and_mutations():
    rec = {'family': 'Farkas refutation',
           'input': {'n': 1, 'rows': [[1], [-1]], 'bounds': [-1, 0]},
           'certificate': {'multipliers': [1, 1]}}
    assert verify(rec)
    with pytest.raises(DecodeError):
        verify({**rec, 'certificate': {'multipliers': [1, 10 ** 30]}})
    with pytest.raises(DecodeError):
        verify({**rec, 'certificate': {'multipliers': [1, 1], 'extra': 0}})
    with pytest.raises(DecodeError):
        verify({**rec, 'input': {**rec['input'], 'n': '1'}})
