"""Untrusted numerical search; successful outputs require exact poly.py replay."""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import combinations, combinations_with_replacement, product
from time import perf_counter
import numpy as np
from scipy.optimize import linprog
from .poly import Poly, ConeTerm, ConeCertificate, Box, BoxCertificate
from .poly import check_cone, bernstein_coefficients, split_box


def monomials(n: int, degree: int) -> list[Poly]:
    exps = [e for e in product(range(degree + 1), repeat=n) if sum(e) <= degree]
    return [Poly.make(n, {e: Q(1)}) for e in sorted(exps, key=lambda e: (sum(e), e))]


def square_dictionary(n: int, degree: int) -> list[Poly]:
    basis = monomials(n, degree)
    result = list(basis)
    # A deliberately incomplete, finite dictionary: not an SDP/SOS-complete solver.
    for a, b in combinations(basis, 2):
        for c in (Q(-2), Q(-1), Q(-1, 2), Q(1, 2), Q(1), Q(2)):
            result.append(a + c * b)
    return list(dict.fromkeys(result))


def cone_search(target: Poly, guards: tuple[Poly, ...] = (),
                max_guard_factors: int = 2) -> tuple[ConeCertificate | None, dict]:
    start = perf_counter()
    if max_guard_factors < 0 or any(g.n != target.n for g in guards):
        raise ValueError('Invalid guard configuration')
    candidates: list[ConeTerm] = []
    columns: list[Poly] = []
    seen: set[Poly] = set()
    selections = [()]
    for d in range(1, max_guard_factors + 1):
        selections.extend(combinations_with_replacement(range(len(guards)), d))
    for gs in selections:
        mul = Poly.const(target.n, 1)
        for j in gs:
            mul *= guards[j]
        if mul.degree > target.degree:
            continue
        for q in square_dictionary(target.n, (target.degree - mul.degree) // 2):
            p = q ** 2 * mul
            if not p.terms or p in seen:
                continue
            seen.add(p)
            candidates.append(ConeTerm(Q(1), q, gs))
            columns.append(p)
    mons = sorted(set(dict(target.terms)).union(*(dict(p.terms) for p in columns)))
    coeffs = [dict(p.terms) for p in columns]
    a = np.array([[float(p.get(m, 0)) for p in coeffs] for m in mons])
    td = dict(target.terms)
    b = np.array([float(td.get(m, 0)) for m in mons])
    stats = {'candidates': len(columns), 'coefficient_equations': len(mons)}
    if not columns:
        return None, {**stats, 'seconds': perf_counter() - start, 'status': 'empty_dictionary'}
    res = linprog(np.ones(len(columns)), A_eq=a, b_eq=b, bounds=(0, None), method='highs')
    if not res.success:
        return None, {**stats, 'seconds': perf_counter() - start,
                      'status': 'no_certificate_in_dictionary', 'optimizer_status': int(res.status)}
    terms = tuple(ConeTerm(Q(float(w)).limit_denominator(1000000), t.square, t.guards)
                  for w, t in zip(res.x, candidates) if w > 1e-9)
    cert = ConeCertificate(terms)
    if not check_cone(target, guards, cert):
        # A numerical answer is not accepted, even when its residual is tiny.
        return None, {**stats, 'seconds': perf_counter() - start, 'status': 'exact_replay_rejected'}
    return cert, {**stats, 'seconds': perf_counter() - start, 'status': 'certified', 'terms': len(terms)}


def box_search(p: Poly, box: Box, max_depth: int = 10,
               strict: bool = False) -> tuple[BoxCertificate | None, dict]:
    start = perf_counter()
    stats = {'nodes': 0, 'leaves': 0, 'max_depth_used': 0}
    def go(b: Box, depth: int) -> BoxCertificate | None:
        stats['nodes'] += 1
        stats['max_depth_used'] = max(stats['max_depth_used'], depth)
        lower = min(bernstein_coefficients(p, b))
        if lower > 0 or (lower == 0 and not strict):
            stats['leaves'] += 1
            return BoxCertificate(lower=lower)
        if depth >= max_depth:
            return None
        axis = max(range(p.n), key=lambda i: b[i][1] - b[i][0])
        s = sum(b[axis]) / 2
        left, right = split_box(b, axis, s)
        lc = go(left, depth + 1)
        if lc is None:
            return None
        rc = go(right, depth + 1)
        if rc is None:
            return None
        return BoxCertificate(axis=axis, split=s, left=lc, right=rc)
    cert = go(box, 0)
    return cert, {**stats, 'seconds': perf_counter() - start,
                  'status': 'certified' if cert else 'budget_exhausted_or_not_positive'}
