"""Exact linear algebra plus an explicitly untrusted floating-point LP proposer."""
from __future__ import annotations
from fractions import Fraction as Q
from typing import Sequence


def solve_exact(a: Sequence[Sequence[Q]], b: Sequence[Q], width: int | None = None):
    """RREF solution with free variables set to zero, or None if inconsistent."""
    if len(a) != len(b):
        raise ValueError("matrix shape mismatch")
    n = width if width is not None else (len(a[0]) if a else 0)
    if any(len(row) != n for row in a):
        raise ValueError("ragged matrix")
    m = [[Q(x) for x in row] + [Q(y)] for row, y in zip(a, b)]
    r, pivots = 0, []
    for col in range(n):
        pivot = next((i for i in range(r, len(m)) if m[i][col]), None)
        if pivot is None:
            continue
        m[r], m[pivot] = m[pivot], m[r]
        q = m[r][col]
        m[r] = [x / q for x in m[r]]
        for i in range(len(m)):
            if i != r and m[i][col]:
                q = m[i][col]
                m[i] = [x - q * y for x, y in zip(m[i], m[r])]
        pivots.append(col)
        r += 1
        if r == len(m):
            break
    if any(not any(row[:n]) and row[n] for row in m):
        return None
    result = [Q(0)] * n
    for row, col in zip(m, pivots):
        result[col] = row[n]
    return result


def exact_feasible(a: Sequence[Sequence[Q]], b: Sequence[Q], nonnegative: Sequence[bool]):
    """Search A*x=b with designated x_i >= 0.

    SciPy supplies a proposal, never a proof. Rational reconstruction is accepted
    only if all equalities and signs hold exactly. None means no certificate;
    it does NOT prove infeasibility (nor mathematical falsity).
    """
    from scipy.optimize import linprog
    import numpy as np
    n = len(nonnegative)
    if any(len(row) != n for row in a) or len(a) != len(b):
        raise ValueError("matrix shape mismatch")
    if n == 0:
        return [] if all(Q(y) == 0 for y in b) else None
    # A numerically unrepresentable exact problem is a failed proposal, not a
    # proof of infeasibility. Shapes were checked above, before this boundary.
    try:
        result = linprog(np.zeros(n), A_eq=np.array(a, dtype=float) if a else None,
                         b_eq=np.array(b, dtype=float) if a else None,
                         bounds=[(0, None) if nn else (None, None) for nn in nonnegative],
                         method="highs")
    except (OverflowError, ValueError):
        return None
    if not result.success or result.x is None or not np.all(np.isfinite(result.x)):
        return None

    def valid(x):
        return (all(not nn or v >= 0 for nn, v in zip(nonnegative, x))
                and all(sum((Q(c) * v for c, v in zip(row, x)), Q(0)) == Q(y)
                        for row, y in zip(a, b)))

    candidate = [Q(float(v)).limit_denominator(1_000_000) for v in result.x]
    if valid(candidate):
        return candidate
    # Exact support reconstruction: numerical zero is only a search heuristic.
    # The exact validation below is mandatory even after exact elimination.
    active = [i for i, (v, nn) in enumerate(zip(result.x, nonnegative))
              if not nn or abs(v) > 1e-9]
    solved = solve_exact([[Q(row[i]) for i in active] for row in a], b, len(active))
    if solved is None:
        return None
    candidate = [Q(0)] * n
    for i, value in zip(active, solved):
        candidate[i] = value
    return candidate if valid(candidate) else None
