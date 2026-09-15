"""Exact linear algebra. Ported from p2's solver tests plus p7/p1 usage."""
from fractions import Fraction as Q
import pytest
from forge.poly import Poly
from forge.linalg import (solve_linear, solve_exact, exact_linear_solve,
                          polynomial_linear_combination, exact_feasible)


def test_exact_linear_solver():
    """p2: RREF, free variables zeroed, inconsistency reported as None."""
    assert solve_exact([[1, 1], [1, -1]], [3, 1]) == [Q(2), Q(1)]
    assert solve_exact([[0]], [1]) is None
    assert solve_exact([[1, 2]], [3]) == [Q(3), Q(0)]
    with pytest.raises(ValueError):
        solve_linear([[1, 2]], [1, 2], 2)


def test_exact_feasible_signs_and_overflow():
    """p2: SciPy proposes; the exact validation decides. Overflow is UNKNOWN."""
    assert exact_feasible([[1]], [Q(3, 7)], [True]) == [Q(3, 7)]
    # A numerically unrepresentable problem is a failed proposal, not a disproof.
    assert exact_feasible([[Q(10) ** 10000]], [1], [True]) is None
    assert exact_feasible([[1]], [Q(-1)], [True]) is None
    assert exact_feasible([[1]], [Q(-1)], [False]) == [Q(-1)]
    with pytest.raises(ValueError):
        exact_feasible([[1, 2]], [1], [True])


def test_polynomial_columns():
    """p7's exact_linear_solve and p1's polynomial_linear_combination agree."""
    x, y = Poly.var(2, 0), Poly.var(2, 1)
    target = 3 * x * x + 2 * y
    columns = [x * x, y, x * y]
    weights = exact_linear_solve(columns, target)
    assert weights == [Q(3), Q(2), Q(0)]
    assert polynomial_linear_combination(target, columns) == weights
    assert exact_linear_solve([x * x], y) is None
    with pytest.raises(ValueError):
        exact_linear_solve([Poly.var(3, 0)], target)


def test_free_variables_are_set_to_zero_not_guessed():
    weights = exact_linear_solve([Poly.var(1, 0), Poly.var(1, 0)], Poly.var(1, 0))
    assert weights == [Q(1), Q(0)]
