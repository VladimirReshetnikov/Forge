"""Exact Schur-complement decomposition of a global quadratic polynomial.

PROVENANCE
  BASE  p1-structural-search/prototype/forge/search.py::quadratic_sos, kept
        verbatim (stdlib only, handles the zero-diagonal PSD case, and
        self-verifies through the general cone checker in certificates.py).
  FOLD  p3-planner-certificate-layer/prototype/quadratic.py -- its machine
        readable status strings, exposed through solve_quadratic().

For z = (1, x_1, ..., x_n) the polynomial is z^T H z; symmetric diagonal pivoting
writes H as a sum of rank-one terms. No floating point, no LP, no SymPy.
"""
from __future__ import annotations
from fractions import Fraction as Q
from .poly import Poly
from .certificates import ConeTerm, ConeCertificate, check_cone


def quadratic_sos(p: Poly) -> ConeCertificate | None:
    """Global nonnegativity of rational quadratics via a rational PSD matrix.

    A returned certificate is exact. None = outside this search fragment or
    matrix not PSD; callers must not interpret None as a counterexample.
    """
    if p.degree > 2:
        return None
    n = p.n + 1
    matrix = [[Q(0) for _ in range(n)] for _ in range(n)]
    for exponent, c in p.terms:
        positions = [i + 1 for i, k in enumerate(exponent) for _ in range(k)]
        if not positions:
            matrix[0][0] += c
        elif len(positions) == 1:
            j = positions[0]
            matrix[0][j] += c / 2
            matrix[j][0] += c / 2
        elif positions[0] == positions[1]:
            matrix[positions[0]][positions[0]] += c
        else:
            i, j = positions
            matrix[i][j] += c / 2
            matrix[j][i] += c / 2
    basis = [Poly.const(p.n, 1)] + [Poly.var(p.n, i) for i in range(p.n)]
    terms = []
    active = list(range(n))
    while active:
        if any(matrix[i][i] < 0 for i in active):
            return None
        pivot = next((i for i in active if matrix[i][i] > 0), None)
        if pivot is None:
            if any(matrix[i][j] for i in active for j in active):
                return None  # a zero-diagonal PSD matrix must be zero
            break
        d = matrix[pivot][pivot]
        q = basis[pivot]
        rest = [j for j in active if j != pivot]
        for j in rest:
            q += (matrix[pivot][j] / d) * basis[j]
        terms.append(ConeTerm(d, q, ()))
        for i in rest:
            for j in rest:
                matrix[i][j] -= matrix[i][pivot] * matrix[pivot][j] / d
        active = rest
    cert = ConeCertificate(tuple(terms))
    if not check_cone(p, [], [], cert):
        raise AssertionError('search produced an invalid certificate')
    return cert


def solve_quadratic(p: Poly) -> tuple[ConeCertificate | None, dict]:
    """p3's reporting wrapper: (certificate | None, machine-readable status)."""
    if p.degree > 2:
        return None, {'status': 'unsupported_degree'}
    cert = quadratic_sos(p)
    if cert is None:
        return None, {'status': 'unknown_non_psd'}
    return cert, {'status': 'checked_python', 'pivots': len(cert.terms),
                  'certificate_terms': len(cert.terms)}
