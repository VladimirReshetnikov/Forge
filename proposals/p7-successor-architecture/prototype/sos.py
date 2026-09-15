"""Bounded sparse conic/SOS search with independent rational certificate replay.

This is not a complete real-arithmetic solver or a semidefinite SOS solver.
It searches a finite dictionary of monomial/binomial squares multiplied by
square-free products of nonnegative assumptions, plus an equality ideal.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import combinations
from polynomial import Poly, monomials, exact_linear_solve

@dataclass(frozen=True)
class Problem:
    target: Poly
    ge: tuple[Poly, ...] = ()
    eq: tuple[Poly, ...] = ()

@dataclass(frozen=True)
class Atom:
    square: Poly
    assumptions: tuple[int, ...] = ()

@dataclass(frozen=True)
class Certificate:
    positive: tuple[tuple[Q, Atom], ...]
    ideal: tuple[tuple[int, Poly], ...] = ()

    def json(self):
        return {'positive': [
            {'weight': str(c), 'square': a.square.json(),
             'assumptions': list(a.assumptions)} for c, a in self.positive],
                'ideal': [{'equality': i, 'multiplier': p.json()} for i, p in self.ideal]}


def expand_atom(problem: Problem, atom: Atom) -> Poly:
    p = atom.square**2
    for i in atom.assumptions:
        if type(i) is not int or i < 0 or i >= len(problem.ge):
            raise ValueError('invalid premise reference')
        p = p*problem.ge[i]
    return p


def check(problem: Problem, cert: Certificate) -> bool:
    """Exact acceptance criterion. No scipy or SymPy calls."""
    try:
        p = Poly.const(problem.target.n)
        for c, a in cert.positive:
            if not isinstance(c, Q) or c < 0: return False
            p = p+c*expand_atom(problem, a)
        for i, multiplier in cert.ideal:
            if type(i) is not int or not 0 <= i < len(problem.eq): return False
            p = p+multiplier*problem.eq[i]
        return p == problem.target
    except (ValueError, TypeError, IndexError, OverflowError):
        return False


def dictionary(problem: Problem, degree: int, products: int = 2,
               binomials: bool = True) -> tuple[list[Atom], list[Poly]]:
    n = problem.target.n
    atoms, values, seen = [], [], set()
    for k in range(min(products, len(problem.ge))+1):
        for ids in combinations(range(len(problem.ge)), k):
            gp = Poly.const(n, 1)
            for i in ids: gp = gp*problem.ge[i]
            qdegree = (degree-gp.degree)//2
            ms = [Poly.mono(n, m) for m in monomials(n, qdegree)]
            qs = list(ms)
            if binomials:
                for i, a in enumerate(ms):
                    for b in ms[i+1:]:
                        qs.extend([a-b, a+b])
            for q in qs:
                v = q*q*gp
                if v.terms and v not in seen:
                    seen.add(v); atoms.append(Atom(q, ids)); values.append(v)
    return atoms, values


def discover(problem: Problem, degree: int | None = None, products: int = 2,
             binomials: bool = True) -> tuple[Certificate | None, dict]:
    """HiGHS proposes support; exact RREF repairs it; check() is mandatory.

    A numeric failure or failed rational reconstruction means UNKNOWN, never
    a proof of infeasibility or a counterexample to the input inequality.
    """
    import numpy as np
    from scipy.optimize import linprog
    degree = problem.target.degree if degree is None else degree
    atoms, vals = dictionary(problem, degree, products, binomials)
    ideal_terms = []
    for i, h in enumerate(problem.eq):
        for m in monomials(problem.target.n, degree-h.degree):
            multiplier = Poly.mono(problem.target.n, m)
            ideal_terms.append((i, multiplier)); vals.append(multiplier*h)
    stats = {'candidates': len(vals), 'positive_candidates': len(atoms)}
    if not vals:
        cert = Certificate(())
        return (cert if check(problem, cert) else None), stats
    keys = sorted(set(dict(problem.target.terms)).union(
        *(set(dict(v.terms)) for v in vals)))
    ds = [dict(v.terms) for v in vals]
    rhs = dict(problem.target.terms)
    A = np.array([[float(d.get(k, 0)) for d in ds] for k in keys])
    b = np.array([float(rhs.get(k, 0)) for k in keys])
    cost = np.array([1.0 + 1e-7*i for i in range(len(atoms))] +
                    [0.0]*len(ideal_terms))
    bounds = [(0, None)] * len(atoms) + [(None, None)] * len(ideal_terms)
    result = linprog(cost, A_eq=A, b_eq=b, bounds=bounds, method='highs')
    stats['numeric_status'] = int(result.status)
    if not result.success: return None, stats
    support = [i for i, v in enumerate(result.x) if abs(v) > 1e-8]
    coeffs = exact_linear_solve([vals[i] for i in support], problem.target)
    if coeffs is None: return None, stats
    positive, ideal = [], []
    for i, c in zip(support, coeffs):
        if not c: continue
        if i < len(atoms): positive.append((c, atoms[i]))
        else:
            j, monomial = ideal_terms[i-len(atoms)]
            ideal.append((j, c*monomial))
    cert = Certificate(tuple(positive), tuple(ideal))
    stats['certificate_terms'] = len(positive)+len(ideal)
    return (cert if check(problem, cert) else None), stats
