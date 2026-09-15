"""Exact linear algebra, plus an explicitly untrusted floating-point LP proposer.

PROVENANCE
  BASE  p7-successor-architecture/prototype/polynomial.py::exact_linear_solve
        (stdlib rational RREF, free variables set to zero, no tolerance).
  FOLD  p2-obligation-controller/prototype/forge_proto/linear.py::exact_feasible
        (SciPy proposal -> exact support re-solve -> MANDATORY exact validation,
        including its OverflowError/ValueError handling at the float boundary).
  FOLD  p1-structural-search/prototype/forge/poly.py::solve_linear and
        polynomial_linear_combination (moved here).

This module is the single home for RREF/feasibility in the merged package; p1,
p2, p3 and p7 each shipped their own copy and only one survives. Nothing here
accepts a floating-point answer: SciPy proposes, exact arithmetic disposes.
"""
from __future__ import annotations
from fractions import Fraction as Q
from typing import Sequence
from .poly import Poly


def solve_linear(a: Sequence[Sequence[Q | int]], b: Sequence[Q | int],
                 columns: int | None = None) -> list[Q] | None:
    """Exact RREF; free parameters set to zero. None means inconsistent."""
    if len(a) != len(b):
        raise ValueError('matrix shape mismatch')
    n = columns if columns is not None else (len(a[0]) if a else 0)
    if n < 0 or any(len(r) != n for r in a):
        raise ValueError('matrix shape mismatch')
    rows = [[Q(v) for v in r] + [Q(rhs)] for r, rhs in zip(a, b)]
    rank = 0
    pivots: list[int] = []
    for col in range(n):
        pivot = next((r for r in range(rank, len(rows)) if rows[r][col]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        q = rows[rank][col]
        rows[rank] = [x / q for x in rows[rank]]
        for r in range(len(rows)):
            if r != rank and rows[r][col]:
                q = rows[r][col]
                rows[r] = [x - q * y for x, y in zip(rows[r], rows[rank])]
        pivots.append(col)
        rank += 1
        if rank == len(rows):
            break
    if any(not any(r[:n]) and r[n] for r in rows):
        return None
    ans = [Q(0)] * n
    for r, c in enumerate(pivots):
        ans[c] = rows[r][n]
    return ans


# p2 spelled this solve_exact; kept as an alias so both provenances read.
solve_exact = solve_linear


def exact_linear_solve(columns: Sequence[Poly], target: Poly) -> list[Q] | None:
    """Solve sum x_i * columns[i] == target over Q (p7 API, shared RREF)."""
    if any(p.n != target.n for p in columns):
        raise ValueError('inconsistent dimensions')
    keys = sorted(set(dict(target.terms)).union(
        *(set(dict(p.terms)) for p in columns)) if columns else set(dict(target.terms)))
    maps = [dict(p.terms) for p in columns]
    rhs = dict(target.terms)
    return solve_linear([[m.get(k, Q(0)) for m in maps] for k in keys],
                        [rhs.get(k, Q(0)) for k in keys], len(columns))


def polynomial_linear_combination(target: Poly, basis: Sequence[Poly]) -> list[Q] | None:
    return exact_linear_solve(list(basis), target)


def exact_feasible(a: Sequence[Sequence[Q]], b: Sequence[Q],
                   nonnegative: Sequence[bool]) -> list[Q] | None:
    """Search A*x=b with designated x_i >= 0.

    SciPy supplies a proposal, never a proof. A rational reconstruction is
    accepted only if every equality and sign holds exactly. None means "no
    certificate"; it does NOT prove infeasibility (nor mathematical falsity).
    """
    from scipy.optimize import linprog
    import numpy as np
    n = len(nonnegative)
    if any(len(row) != n for row in a) or len(a) != len(b):
        raise ValueError('matrix shape mismatch')
    if n == 0:
        return [] if all(Q(y) == 0 for y in b) else None

    def valid(x):
        return (all(not nn or v >= 0 for nn, v in zip(nonnegative, x))
                and all(sum((Q(c) * v for c, v in zip(row, x)), Q(0)) == Q(y)
                        for row, y in zip(a, b)))

    # A numerically unrepresentable exact problem is a failed proposal, not a
    # proof of infeasibility. Shapes were checked above, before this boundary.
    try:
        result = linprog(np.zeros(n),
                         A_eq=np.array(a, dtype=float) if a else None,
                         b_eq=np.array(b, dtype=float) if a else None,
                         bounds=[(0, None) if nn else (None, None) for nn in nonnegative],
                         method='highs')
    except (OverflowError, ValueError):
        return None
    if not result.success or result.x is None or not np.all(np.isfinite(result.x)):
        return None
    candidate = [Q(float(v)).limit_denominator(1_000_000) for v in result.x]
    if valid(candidate):
        return candidate
    # Exact support reconstruction: numerical zero is only a search heuristic.
    # The exact validation below is mandatory even after exact elimination.
    active = [i for i, (v, nn) in enumerate(zip(result.x, nonnegative))
              if not nn or abs(v) > 1e-9]
    solved = solve_linear([[Q(row[i]) for i in active] for row in a], b, len(active))
    if solved is None:
        return None
    candidate = [Q(0)] * n
    for i, value in zip(active, solved):
        candidate[i] = value
    return candidate if valid(candidate) else None
