"""Bounded nonlinear cone search, with independent exact certificate replay.

Search: a floating LP proposes a nonnegative combination of a FINITE dictionary
of squares and products of assumptions. Exact reconstruction is mandatory.
Checker: only Fraction polynomial arithmetic; no scipy, sympy, tolerance, or LP.
Not a complete SOS/Positivstellensatz solver. All inequalities are weak (>= 0).
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import combinations_with_replacement
from poly import Poly, monomials

@dataclass(frozen=True)
class Atom:
    square: Poly
    factors: tuple[int, ...] = ()

@dataclass(frozen=True)
class ConeCertificate:
    # Sum c * square^2 * product(g_i), c >= 0; plus unrestricted q_j * h_j.
    positive: tuple[tuple[Q, Atom], ...]
    equalities: tuple[tuple[int, Poly], ...]

    def to_json(self) -> dict:
        return {"positive": [{"coefficient": str(c), "square": a.square.to_json(),
                              "factors": list(a.factors)} for c, a in self.positive],
                "equalities": [{"index": i, "multiplier": q.to_json()}
                               for i, q in self.equalities]}


def replay(target: Poly, ge: tuple[Poly, ...], eq: tuple[Poly, ...],
           cert: ConeCertificate) -> bool:
    """Validate that hypotheses ge>=0, eq=0 imply target>=0.

    The problem, including target and ordered hypotheses, is supplied by caller;
    the certificate is never allowed to replace that problem.
    """
    try:
        if any(p.n != target.n for p in ge+eq):
            return False
        total = Poly.const(target.n, 0)
        for c, atom in cert.positive:
            if not isinstance(c, Q) or c < 0 or atom.square.n != target.n:
                return False
            p = atom.square**2
            for i in atom.factors:
                if type(i) is not int or not 0 <= i < len(ge):
                    return False
                p *= ge[i]
            total += c*p
        for i, q in cert.equalities:
            if type(i) is not int or not 0 <= i < len(eq) or q.n != target.n:
                return False
            total += q*eq[i]
        return total == target
    except (ValueError, TypeError, AttributeError):
        return False


def dictionary(n: int, ge: tuple[Poly, ...], eq: tuple[Poly, ...],
               degree: int, product_depth: int, binomials: bool,
               max_columns: int) -> tuple[list[Poly], list[tuple]]:
    one = Poly.const(n, 1)
    base = monomials(n, degree//2)
    squares = list(base)
    if binomials:
        # A finite, explicit candidate language, not semidefinite programming.
        # Limit binomials to affine terms so the quadratic dictionary stays small.
        affine = [m for m in base if m.degree <= 1]
        for j, a in enumerate(affine):
            for b in affine[j+1:]:
                squares.extend((a+b, a-b))
    factors = [()]
    for k in range(1, product_depth+1):
        factors.extend(combinations_with_replacement(range(len(ge)), k))
    cols: list[Poly] = []
    tags: list[tuple] = []
    seen: set[Poly] = set()
    def add(p: Poly, tag: tuple) -> None:
        if p.terms and p.degree <= degree and p not in seen and len(cols)<max_columns:
            seen.add(p); cols.append(p); tags.append(tag)
    for fs in factors:
        prod = one
        for i in fs:
            prod *= ge[i]
        for s in squares:
            add((s**2)*prod, ("positive", Atom(s, fs)))
    for j, h in enumerate(eq):
        for m in monomials(n, max(0, degree-h.degree)):
            add(m*h, ("equality", j, m))
            add(-m*h, ("equality", j, -m))
    return cols, tags


def _reconstruct(columns: list[Poly], target: Poly, approx) -> tuple[Q, ...] | None:
    # First inexpensive reconstruction. This can fail but never licenses a proof.
    qs = tuple(Q(float(x)).limit_denominator(10**6) if x > 1e-10 else Q(0)
               for x in approx)
    if all(q >= 0 for q in qs) and sum((q*p for q, p in zip(qs, columns)),
                                      Poly.const(target.n, 0)) == target:
        return qs
    # Re-solve the proposed support exactly. Floating point chooses a support only.
    import sympy as sp
    support = [j for j, x in enumerate(approx) if x > 1e-10]
    if not support:
        return None
    exps = sorted({e for p in columns for e, _ in p.terms} | {e for e,_ in target.terms})
    maps = [dict(columns[j].terms) for j in support]
    matrix = sp.Matrix([[sp.Rational(m.get(e,Q(0)).numerator,
                                   m.get(e,Q(0)).denominator) for m in maps]
                        for e in exps])
    tm = dict(target.terms)
    rhs = sp.Matrix([sp.Rational(tm.get(e,Q(0)).numerator,tm.get(e,Q(0)).denominator)
                     for e in exps])
    try:
        sol, params = matrix.gauss_jordan_solve(rhs)
        sol = sol.subs({s: 0 for s in params})
        qs_list = [Q(0)]*len(columns)
        for j, x in zip(support, sol):
            qs_list[j] = Q(int(x.p), int(x.q))
        if min(qs_list) < 0:
            return None
        return tuple(qs_list)
    except (ValueError, TypeError, AttributeError):
        return None


def search(target: Poly, ge: tuple[Poly, ...] = (), eq: tuple[Poly, ...] = (),
           *, degree: int = 4, product_depth: int = 2,
           binomials: bool = True, max_columns: int = 3000,
           timeout_seconds: float = 5.0) -> ConeCertificate | None:
    """Return exact certificate or None (unknown). No SAT/false claim on failure."""
    import numpy as np
    from scipy.optimize import linprog
    if degree < 0 or product_depth < 0 or max_columns < 1:
        raise ValueError("invalid search bounds")
    if any(p.n != target.n for p in ge+eq):
        raise ValueError("hypothesis arity mismatch")
    if not target.terms:
        return ConeCertificate((), ())
    cols, tags = dictionary(target.n, ge, eq, degree, product_depth, binomials, max_columns)
    if not cols:
        return None
    exps = sorted({e for p in cols for e, _ in p.terms} | {e for e,_ in target.terms})
    maps = [dict(p.terms) for p in cols]
    tm = dict(target.terms)
    A = np.array([[float(m.get(e, 0)) for m in maps] for e in exps])
    b = np.array([float(tm.get(e, 0)) for e in exps])
    if not np.all(np.isfinite(A)) or not np.all(np.isfinite(b)):
        return None
    out = linprog(np.ones(len(cols)), A_eq=A, b_eq=b, bounds=(0, None),
                  method="highs", options={"time_limit": timeout_seconds})
    if not out.success or out.x is None:
        return None
    weights = _reconstruct(cols, target, out.x)
    if weights is None:
        return None
    positive = []
    multipliers: dict[int, Poly] = {}
    for q, tag in zip(weights, tags):
        if not q:
            continue
        if tag[0] == "positive":
            positive.append((q, tag[1]))
        else:
            _, i, m = tag
            multipliers[i] = multipliers.get(i, Poly.const(target.n, 0)) + q*m
    cert = ConeCertificate(tuple(positive), tuple(sorted(multipliers.items())))
    return cert if replay(target, ge, eq, cert) else None
