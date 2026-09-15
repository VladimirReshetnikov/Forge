"""Bounded cone / dictionary-SOS SEARCH. Every answer is replayed exactly.

PROVENANCE
  BASE  p5-certificate-first/prototype/forge/nonlinear.py -- goal_square_bases
        target-driven square inference, explicit product/generator/ideal budgets,
        ConeResult carrying a machine-readable `reason`, and the np.isfinite
        overflow guard before the LP boundary.
  FOLD  p7-successor-architecture/prototype/sos.py -- the `products` and
        `binomials` ablation flags, and the exact RREF repair path (this drops
        SymPy from the repair entirely; p5 and p8 both called gauss_jordan_solve).
  FOLD  p8-obligation-broker/prototype/cone.py -- `timeout_seconds` handed to the
        LP backend and the optional +/- ideal columns (so an ideal multiplier can
        be produced by a solver restricted to nonnegative bounds).

NOT ported: p4's polynomial_search.py (SymPy-expression-native, duplicating this
over the exact Poly type) and p2's check_sos (one constraint factor per square --
strictly weaker than every other cone checker here).

This is a finite dictionary search, NOT a complete SOS/Positivstellensatz solver
or a semidefinite program. LP infeasibility is never a disproof: it is UNKNOWN.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import combinations, combinations_with_replacement
from math import isqrt
from time import perf_counter
from typing import Sequence
from .poly import Poly, monomials
from .linalg import exact_linear_solve
from .certificates import ConeTerm, ConeCertificate, check_cone, powers_from_indices


@dataclass
class ConeResult:
    status: str  # 'proved' or 'unknown'; LP infeasibility is never a disproof
    certificate: ConeCertificate | None
    generators: int
    seconds: float
    reason: str = ''


def goal_square_bases(target: Poly, limit: int = 200) -> tuple[Poly, ...]:
    """Heuristic binomial-square roots inferred from positive even monomials (p5).

    For a*m^2 + b*n^2, try m +/- r*n when r^2 = b/a is a rational square; also
    complete each oriented pair using its cross coefficient. A finite dictionary,
    not a complete SOS search.
    """
    roots = []
    for mon, c in target.terms:
        if c > 0 and all(e % 2 == 0 for e in mon):
            roots.append((Poly.monomial(target.n, tuple(e // 2 for e in mon)), c))
    out: list[Poly] = []
    coeffs = dict(target.terms)
    for i, (p, a) in enumerate(roots):
        for q, b in roots[i + 1:]:
            ratios = [Q(1)]
            r = b / a
            sn, sd = isqrt(r.numerator), isqrt(r.denominator)
            if sn * sn == r.numerator and sd * sd == r.denominator:
                ratios.append(Q(sn, sd))
            # A positive residual constant can hide the square-root ratio.
            cross_mon = tuple(u + v for u, v in zip(p.terms[0][0], q.terms[0][0]))
            cross = coeffs.get(cross_mon, Q(0))
            if cross:
                out.extend([p + (cross / (2 * a)) * q, q + (cross / (2 * b)) * p])
            for ratio in ratios:
                out.extend([p + ratio * q, p - ratio * q])
                if len(out) >= limit:
                    return tuple(dict.fromkeys(out[:limit]))
    return tuple(dict.fromkeys(out))


def square_dictionary(n: int, degree: int, *, binomials: bool = True) -> list[Poly]:
    """Monomials, optionally extended with pairwise sums/differences (p7/p2)."""
    ms = list(monomials(n, degree))
    out = list(ms)
    if binomials:
        for a, b in combinations(ms, 2):
            out.extend([a + b, a - b])
    return list(dict.fromkeys(out))


def discover(target: Poly, nonnegative: Sequence[Poly] = (),
             equal_zero: Sequence[Poly] = (), *, degree: int = 4,
             square_bases: Sequence[Poly] = (), max_generators: int = 4000,
             products: int | None = None, binomials: bool = True,
             signed_ideal: bool = False, timeout_seconds: float = 10.0) -> ConeResult:
    start = perf_counter()
    nonnegative, equal_zero = tuple(nonnegative), tuple(equal_zero)
    n = target.n
    if degree < 0 or max_generators < 1 or timeout_seconds <= 0:
        raise ValueError('invalid search budget')
    if any(p.n != n for p in nonnegative + equal_zero + tuple(square_bases)):
        raise ValueError('dimension mismatch')
    if target.degree > degree:
        return ConeResult('unknown', None, 0, perf_counter() - start,
                          'target exceeds degree cap')
    depth = degree if products is None else min(products, degree)
    if depth < 0:
        raise ValueError('invalid product depth')

    # Monomial squares plus optional affine/polynomial squares. Finite cone.
    bases = list(monomials(n, degree // 2))
    if binomials:
        bases += list(goal_square_bases(target))
    bases = list(dict.fromkeys(bases + list(square_bases)))

    products_list: list[tuple[tuple[int, ...], Poly]] = [((), Poly.const(n, 1))]
    # Repeated factors allowed. Constant constraints are omitted from products:
    # zero adds nothing, positive is absorbed by weights, negative is retained
    # as a linear generator so contradictions remain possible.
    for k in range(1, depth + 1):
        for inds in combinations_with_replacement(range(len(nonnegative)), k):
            if k > 1 and any(nonnegative[i].degree <= 0 for i in inds):
                continue
            p = Poly.const(n, 1)
            for i in inds:
                p *= nonnegative[i]
            if p.terms and p.degree <= degree:
                products_list.append((inds, p))
            if len(products_list) > max_generators:
                return ConeResult('unknown', None, len(products_list),
                                  perf_counter() - start, 'product budget')

    columns: list[Poly] = []
    descriptors: list[tuple[Poly, tuple[int, ...]]] = []
    seen: set[Poly] = set()
    for q in bases:
        for inds, p in products_list:
            col = q * q * p
            if not col.terms or col.degree > degree or col in seen:
                continue
            seen.add(col)
            columns.append(col)
            descriptors.append((q, inds))
            if len(columns) > max_generators:
                return ConeResult('unknown', None, len(columns), perf_counter() - start,
                                  'generator budget')
    cone_count = len(columns)

    ideal_desc: list[tuple[int, Poly]] = []
    for j, e in enumerate(equal_zero):
        if not e.terms:
            continue
        for q in monomials(n, max(0, degree - e.degree)):
            columns.append(q * e)
            ideal_desc.append((j, q))
            if signed_ideal:  # p8: usable by an LP restricted to x >= 0
                columns.append(-(q * e))
                ideal_desc.append((j, -q))
    if len(columns) > max_generators:
        return ConeResult('unknown', None, len(columns), perf_counter() - start,
                          'ideal budget')
    if not columns:
        return ConeResult('unknown', None, 0, perf_counter() - start, 'empty basis')

    rows = sorted(set(m for p in columns + [target] for m, _ in p.terms))
    maps = [dict(p.terms) for p in columns]
    td = dict(target.terms)
    exact = [[d.get(m, Q(0)) for d in maps] for m in rows]
    rhs = [td.get(m, Q(0)) for m in rows]

    import numpy as np
    from scipy.optimize import linprog
    A = np.array(exact, dtype=float)
    b = np.array(rhs, dtype=float)
    if not np.isfinite(A).all() or not np.isfinite(b).all():
        return ConeResult('unknown', None, len(columns), perf_counter() - start,
                          'floating overflow')
    ideal_bound = (0, None) if signed_ideal else (None, None)
    opt = linprog(np.r_[np.ones(cone_count), np.zeros(len(ideal_desc))],
                  A_eq=A, b_eq=b,
                  bounds=[(0, None)] * cone_count + [ideal_bound] * len(ideal_desc),
                  method='highs', options={'time_limit': timeout_seconds})
    if not opt.success or opt.x is None:
        return ConeResult('unknown', None, len(columns), perf_counter() - start,
                          'LP found no candidate')

    def package(ws: Sequence[Q]) -> ConeCertificate:
        terms = tuple(ConeTerm(ws[i], q, powers_from_indices(inds, len(nonnegative)))
                      for i, (q, inds) in enumerate(descriptors) if ws[i])
        hs = [Poly.const(n, 0) for _ in equal_zero]
        for i, (j, q) in enumerate(ideal_desc, cone_count):
            hs[j] += ws[i] * q
        return ConeCertificate(terms, tuple(hs))

    # Floating weights are proposals only. Exact rational reconstruction followed
    # by a separate identity/sign check is the sole acceptance criterion.
    weights = [Q(float(v)).limit_denominator(10 ** 7) for v in opt.x]
    cert = package(weights)
    if not check_cone(target, nonnegative, equal_zero, cert):
        # Re-solve the proposed support exactly with rational RREF (no SymPy).
        # This can fail or pick negative coefficients; that is UNKNOWN, never a
        # relaxed acceptance test.
        support = [i for i, v in enumerate(opt.x) if abs(v) > 1e-9]
        solved = exact_linear_solve([columns[i] for i in support], target)
        if solved is None:
            return ConeResult('unknown', None, len(columns), perf_counter() - start,
                              'exact reconstruction failed')
        weights = [Q(0)] * len(columns)
        for i, v in zip(support, solved):
            weights[i] = v
        if any(w < 0 for w in weights[:cone_count]):
            return ConeResult('unknown', None, len(columns), perf_counter() - start,
                              'exact reconstruction went negative')
        cert = package(weights)
    if not check_cone(target, nonnegative, equal_zero, cert):
        return ConeResult('unknown', None, len(columns), perf_counter() - start,
                          'certificate rejected')
    return ConeResult('proved', cert, len(columns), perf_counter() - start, 'checked_python')
