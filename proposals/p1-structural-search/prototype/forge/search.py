"""Untrusted search oracles; successful output must pass certificates.py.

quadratic_sos: exact Schur-complement factorization.
cone_search: floating LP proposal followed by exact support reconstruction.
bernstein_search: exact rational dyadic subdivision.
"""
from __future__ import annotations
from fractions import Fraction as Q
from typing import Sequence
from .poly import Poly, polynomial_linear_combination
from .certificates import (ConeTerm, ConeCertificate, check_cone, Box,
    BernsteinTree, BernsteinLeaf, BernsteinSplit, bernstein_coefficients, split_box)


def quadratic_sos(p: Poly) -> ConeCertificate | None:
    """Global nonnegativity of rational quadratics via a rational PSD matrix.

    A returned certificate is exact. None = outside this search fragment or
    matrix not PSD; callers must not interpret None as a counterexample.
    """
    if p.degree > 2:
        return None
    n = p.n + 1
    matrix = [[Q(0) for _ in range(n)] for _ in range(n)]
    for exponent,c in p.terms:
        positions = [i+1 for i,k in enumerate(exponent) for _ in range(k)]
        if not positions:
            matrix[0][0] += c
        elif len(positions) == 1:
            j = positions[0]
            matrix[0][j] += c/2
            matrix[j][0] += c/2
        elif positions[0] == positions[1]:
            matrix[positions[0]][positions[0]] += c
        else:
            i,j = positions
            matrix[i][j] += c/2
            matrix[j][i] += c/2
    basis = [Poly.const(p.n,1)] + [Poly.var(p.n,i) for i in range(p.n)]
    terms = []
    active = list(range(n))
    while active:
        if any(matrix[i][i] < 0 for i in active):
            return None
        pivot = next((i for i in active if matrix[i][i] > 0),None)
        if pivot is None:
            if any(matrix[i][j] for i in active for j in active):
                return None  # a zero-diagonal PSD matrix must be zero
            break
        d = matrix[pivot][pivot]
        q = basis[pivot]
        rest = [j for j in active if j != pivot]
        for j in rest:
            q += (matrix[pivot][j]/d)*basis[j]
        terms.append(ConeTerm(d,q,()))
        for i in rest:
            for j in rest:
                matrix[i][j] -= matrix[i][pivot]*matrix[pivot][j]/d
        active = rest
    cert = ConeCertificate(tuple(terms))
    if not check_cone(p,[],[],cert):
        raise AssertionError('search produced an invalid certificate')
    return cert


def cone_search(p: Poly, inequalities: Sequence[Poly],
                candidates: Sequence[ConeTerm]) -> ConeCertificate | None:
    """Find a nonnegative combination of an explicitly finite candidate cone.

    This is NOT full SOS SDP search. HiGHS is only an untrusted support oracle;
    its 'infeasible' result never becomes a logical disproof.
    """
    import numpy as np
    from scipy.optimize import linprog
    columns = []
    for t in candidates:
        if t.square.n != p.n or len(t.powers) != len(inequalities):
            raise ValueError('bad candidate dimension')
        if any(type(k) is not int or k < 0 for k in t.powers):
            raise ValueError('bad candidate exponent')
        c = t.square**2
        for g,k in zip(inequalities,t.powers):
            c *= g**k
        columns.append(c)
    if not columns:
        return ConeCertificate(()) if not p.terms else None
    support = sorted(set(e for q in [p,*columns] for e,_ in q.terms))
    if not support:
        return ConeCertificate(())
    ds,td = [dict(q.terms) for q in columns],dict(p.terms)
    a = np.array([[float(d.get(e,0)) for d in ds] for e in support])
    b = np.array([float(td.get(e,0)) for e in support])
    costs = np.array([1 + len(q.terms)/1000 for q in columns])
    result = linprog(costs,A_eq=a,b_eq=b,bounds=(0,None),method='highs')
    if not result.success:
        return None
    indices = [i for i,v in enumerate(result.x) if v > 1e-9]
    coefficients = polynomial_linear_combination(p,[columns[i] for i in indices])
    if coefficients is None or any(c < 0 for c in coefficients):
        return None
    cert = ConeCertificate(tuple(ConeTerm(c,candidates[i].square,candidates[i].powers)
                                 for i,c in zip(indices,coefficients) if c))
    return cert if check_cone(p,inequalities,[],cert) else None


def bernstein_search(p: Poly, box: Box, max_depth: int = 12,
                     max_nodes: int = 10_000) -> BernsteinTree | None:
    """Search only. None is Unknown, including when a negative value exists."""
    if max_depth < 0 or max_nodes < 1:
        raise ValueError('invalid search budget')
    nodes = 0
    def visit(domain: Box, depth: int) -> BernsteinTree | None:
        nonlocal nodes
        nodes += 1
        if nodes > max_nodes:
            return None
        coeffs = bernstein_coefficients(p,domain)
        lower = min(coeffs.values())
        if lower >= 0:
            return BernsteinLeaf(lower)
        # A counterexample can stop search, but it is not returned as a proof.
        midpoint = [(l+u)/2 for l,u in domain]
        if p.evaluate(midpoint) < 0 or depth == max_depth:
            return None
        axis = max(range(p.n),key=lambda i: (domain[i][1]-domain[i][0],-i))
        point = sum(domain[axis],Q(0))/2
        left_box,right_box = split_box(domain,axis,point)
        left = visit(left_box,depth+1)
        if left is None:
            return None
        right = visit(right_box,depth+1)
        if right is None:
            return None
        return BernsteinSplit(axis,point,left,right)
    return visit(box,0)
