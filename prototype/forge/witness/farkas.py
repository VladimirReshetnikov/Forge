"""Farkas refutations of linear systems  a_i . x <= b_i.

A certificate is a list of INTEGER multipliers lambda_i >= 0 with
sum lambda_i a_i = 0 and sum lambda_i b_i < 0: adding the constraints with those
weights gives 0 <= sum lambda_i b_i < 0, so no real (hence no integer) x
satisfies them all.

This is the shape `lean/Forge/Checker/Farkas.lean` checks, and the checker below
mirrors `FarkasCert.check` exactly, including its rejections: the multiplier
count must equal the row count, every row must have exactly `n` coefficients,
and an empty system has no certificate. Multipliers are integers so the
certificate is emitted to Lean verbatim; the search clears denominators.

`check_farkas` uses only the standard library. `synthesize_farkas` asks SciPy
(through `forge.linalg.exact_feasible`) for a proposal and returns it only after
the exact check passes. None means "no certificate found", never "feasible".
Farkas certificates are complete for RATIONAL infeasibility only: `2x = 1` has
integer-only obstructions this family cannot express.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from math import lcm


@dataclass(frozen=True)
class FarkasCertificate:
    multipliers: tuple[int, ...]


def _is_int(v) -> bool:
    return isinstance(v, int) and not isinstance(v, bool)


def check_farkas(n: int, rows, bounds, cert: FarkasCertificate) -> bool:
    """Exact check: shapes, nonnegativity, zero combination, negative bound sum."""
    if not _is_int(n) or n < 0:
        return False
    lam = cert.multipliers
    if not (len(rows) == len(bounds) == len(lam)) or not rows:
        return False
    if not all(_is_int(v) for v in lam) or not all(_is_int(b) for b in bounds):
        return False
    if any(len(r) != n or not all(_is_int(a) for a in r) for r in rows):
        return False
    if any(l < 0 for l in lam):
        return False
    if any(sum(l * r[j] for l, r in zip(lam, rows)) != 0 for j in range(n)):
        return False
    return sum(l * b for l, b in zip(lam, bounds)) < 0


def synthesize_farkas(rows, bounds) -> FarkasCertificate | None:
    """Find integer multipliers by LP: A^T lambda = 0, b . lambda = -1, lambda >= 0."""
    from ..linalg import exact_feasible
    if not rows:
        return None
    n = len(rows[0])
    a = [[Q(r[j]) for r in rows] for j in range(n)] + [[Q(b) for b in bounds]]
    rhs = [Q(0)] * n + [Q(-1)]
    lam = exact_feasible(a, rhs, [True] * len(rows))
    if lam is None:
        return None
    scale = lcm(*(v.denominator for v in lam))
    cert = FarkasCertificate(tuple(int(v * scale) for v in lam))
    return cert if check_farkas(n, rows, bounds, cert) else None
