"""Exact polynomial recurrence and parametric affine-witness synthesis.

No induction is automated in Lean here. A recurrence certificate consists of
universal base/step polynomial identities; the article gives the induction rule
and the package emits optional, NOT locally compiled, Lean examples.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from typing import Sequence
from .poly import Poly, monomial_exponents, solve_linear


def check_recurrence(step: Poly, initial: Poly, formula: Poly) -> bool:
    """Check F(0,a)=initial(a), F(n+1,a)-F(n,a)=step(n,a)."""
    try:
        if not step.n == initial.n == formula.n:
            return False
        if any(e[0] for e,_ in initial.terms):
            return False
        variables = [Poly.var(step.n,i) for i in range(step.n)]
        shifted = [variables[0]+1,*variables[1:]]
        at_zero = [Poly.const(step.n,0),*variables[1:]]
        return (formula.substitute(at_zero) == initial and
                formula.substitute(shifted)-formula == step)
    except (ValueError,TypeError,AttributeError):
        return False


def synthesize_recurrence(step: Poly, initial: Poly,
                         max_degree: int = 8) -> Poly | None:
    if step.n != initial.n or any(e[0] for e,_ in initial.terms):
        raise ValueError('initial value must not depend on recurrence index')
    if max_degree < 0:
        raise ValueError('negative degree budget')
    variables = [Poly.var(step.n,i) for i in range(step.n)]
    shifted = [variables[0]+1,*variables[1:]]
    at_zero = [Poly.const(step.n,0),*variables[1:]]
    for degree in range(max_degree+1):
        basis = [Poly.make(step.n,[(e,1)]) for e in monomial_exponents(step.n,degree)]
        deltas = [q.substitute(shifted)-q for q in basis]
        bases = [q.substitute(at_zero) for q in basis]
        support_step = sorted(set(e for q in [step,*deltas] for e,_ in q.terms))
        support_base = sorted(set(e for q in [initial,*bases] for e,_ in q.terms))
        ds,bs = [dict(q.terms) for q in deltas],[dict(q.terms) for q in bases]
        sd,bd = dict(step.terms),dict(initial.terms)
        a = [[d.get(e,0) for d in ds] for e in support_step]
        a += [[d.get(e,0) for d in bs] for e in support_base]
        b = [sd.get(e,0) for e in support_step]+[bd.get(e,0) for e in support_base]
        coefficients = solve_linear(a,b,len(basis))
        if coefficients is not None:
            formula = sum((c*q for c,q in zip(coefficients,basis)),Poly.const(step.n,0))
            if check_recurrence(step,initial,formula):
                return formula
    return None

@dataclass(frozen=True)
class AffineWitness:
    """w = linear*x + offset, with exact rational coefficients."""
    linear: tuple[tuple[Q,...],...]
    offset: tuple[Q,...]


def _shape(a, b, c) -> tuple[int,int,int]:
    if not a or not b or len(a) != len(b) or len(a) != len(c):
        raise ValueError('nonempty compatible equation arrays required')
    k,p = len(a[0]),len(b[0])
    if k < 1 or p < 1 or any(len(r) != k for r in a) or any(len(r) != p for r in b):
        raise ValueError('ragged or empty matrix')
    return len(a),k,p


def check_affine_witness(a, b, c, witness: AffineWitness,
                         require_integral: bool = False) -> bool:
    """Verify A W = B and A d = c. This does not check extra inequalities."""
    try:
        m,k,p = _shape(a,b,c)
        if len(witness.linear) != k or len(witness.offset) != k:
            return False
        if any(len(r) != p for r in witness.linear):
            return False
        coeffs = [z for r in witness.linear for z in r]+list(witness.offset)
        if any(not isinstance(z,Q) for z in coeffs):
            return False
        if require_integral and any(z.denominator != 1 for z in coeffs):
            return False
        for i in range(m):
            if sum((Q(a[i][j])*witness.offset[j] for j in range(k)),Q(0)) != Q(c[i]):
                return False
            for t in range(p):
                if sum((Q(a[i][j])*witness.linear[j][t] for j in range(k)),Q(0)) != Q(b[i][t]):
                    return False
        return True
    except (ValueError,TypeError,AttributeError,IndexError):
        return False


def synthesize_affine_witness(a,b,c,require_integral: bool = False) -> AffineWitness | None:
    _,k,p = _shape(a,b,c)
    columns = []
    for t in range(p):
        column = solve_linear(a,[r[t] for r in b],k)
        if column is None:
            return None
        columns.append(column)
    offset = solve_linear(a,c,k)
    if offset is None:
        return None
    witness = AffineWitness(tuple(tuple(columns[t][j] for t in range(p)) for j in range(k)),tuple(offset))
    return witness if check_affine_witness(a,b,c,witness,require_integral) else None
