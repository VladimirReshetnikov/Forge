"""Gram-matrix sum-of-squares SEARCH, with exact rational reconstruction.

WHY. `cone.discover` searches a finite dictionary of squares. The tactic
head-to-head showed where that stops: `(x - y)^4` written out is the square of
`x^2 - 2xy + y^2`, a trinomial with specific coefficients that no fixed
dictionary proposes. A Gram-matrix search does not guess squares; it looks for
a positive semidefinite matrix Q with p = m^T Q m over a monomial vector m, and
reads the squares off Q.

HOW. There is no SDP solver in this environment, and none is needed for the
problem sizes the oracle accepts:

  1. Basis. Monomials of half the degree, pruned to the half-exponent box of the
     target's support. Any square q with sum q^2 = p has support inside half the
     Newton polytope of p, which lies inside that box, so pruning loses nothing.
  2. Constraints. p = m^T Q m is a linear system in the entries of Q. Its
     solution space is computed EXACTLY over the rationals: a particular
     solution and a nullspace basis.
  3. Numeric PSD point. Alternating projections between that affine space and
     the PSD cone. Converges to a point in the intersection when it is nonempty,
     possibly on its boundary -- which is where exact certificates for
     polynomials with real zeros, such as (x - y)^4, live.
  4. Exact reconstruction. The numeric point's coordinates in the exact
     nullspace basis are rounded to rationals at increasing denominators, and
     Q is rebuilt EXACTLY from the exact particular solution and basis, so the
     linear constraints hold exactly by construction. An exact LDL
     decomposition then either shows Q is PSD and yields weighted squares, or
     the next denominator is tried.
  5. Self-check. The certificate is checked with `certificates.check_cone`, the
     prototype's exact checker, before being returned.

TRUST. None of this is trusted. It is search. Whatever it returns is replayed
exactly here and then re-checked by the Lean kernel. A `None` is UNKNOWN, never
a proof that p is not a sum of squares -- although for the Motzkin polynomial,
which is not, `None` is also the right answer.
"""
from __future__ import annotations

from fractions import Fraction as Q
from time import monotonic

from .certificates import ConeCertificate, ConeTerm, check_cone
from .poly import Poly, monomial_exponents

MAX_BASIS = 28


def _basis(p: Poly) -> list[tuple[int, ...]]:
    if p.degree % 2:
        return []
    half = p.degree // 2
    exps = [e for e, _ in p.terms]
    lo = [min(e[i] for e in exps) for i in range(p.n)]
    hi = [max(e[i] for e in exps) for i in range(p.n)]
    lo_deg = min(sum(e) for e in exps)
    out = []
    for m in monomial_exponents(p.n, half):
        if all(2 * m[i] >= lo[i] and 2 * m[i] <= hi[i] for i in range(p.n)) \
                and 2 * sum(m) >= lo_deg:
            out.append(tuple(m))
    return out


def _rref_solution(rows: list[list[Q]], rhs: list[Q], ncols: int):
    """Exact particular solution and nullspace basis of rows * x = rhs, or None."""
    a = [list(r) + [b] for r, b in zip(rows, rhs)]
    pivots = []
    r = 0
    for c in range(ncols):
        piv = next((i for i in range(r, len(a)) if a[i][c] != 0), None)
        if piv is None:
            continue
        a[r], a[piv] = a[piv], a[r]
        inv = 1 / a[r][c]
        a[r] = [v * inv for v in a[r]]
        for i in range(len(a)):
            if i != r and a[i][c] != 0:
                f = a[i][c]
                a[i] = [vi - f * vr for vi, vr in zip(a[i], a[r])]
        pivots.append(c)
        r += 1
        if r == len(a):
            break
    if any(all(v == 0 for v in row[:ncols]) and row[ncols] != 0 for row in a):
        return None                                   # inconsistent: p is not m^T Q m
    x0 = [Q(0)] * ncols
    for i, c in enumerate(pivots):
        x0[c] = a[i][ncols]
    free = [c for c in range(ncols) if c not in pivots]
    null = []
    for f in free:
        v = [Q(0)] * ncols
        v[f] = Q(1)
        for i, c in enumerate(pivots):
            v[c] = -a[i][f]
        null.append(v)
    return x0, null


def _ldl_terms(matrix: list[list[Q]], basis_polys: list[Poly]):
    """Exact LDL with zero-pivot handling; weighted squares, or None if not PSD."""
    m = [row[:] for row in matrix]
    active = list(range(len(m)))
    terms = []
    while active:
        if any(m[i][i] < 0 for i in active):
            return None
        pivot = next((i for i in active if m[i][i] > 0), None)
        if pivot is None:
            if any(m[i][j] for i in active for j in active):
                return None                           # zero diagonal forces a zero block
            break
        d = m[pivot][pivot]
        q = basis_polys[pivot]
        rest = [j for j in active if j != pivot]
        for j in rest:
            q = q + (m[pivot][j] / d) * basis_polys[j]
        terms.append(ConeTerm(d, q, ()))
        for i in rest:
            for j in rest:
                m[i][j] -= m[i][pivot] * m[pivot][j] / d
        active = rest
    return terms


def gram_sos(p: Poly, *, timeout_seconds: float = 10.0) -> ConeCertificate | None:
    """A sum-of-squares certificate for p, or None (UNKNOWN)."""
    deadline = monotonic() + timeout_seconds
    if not p.terms:
        return ConeCertificate(())
    basis = _basis(p)
    k = len(basis)
    if k == 0 or k > MAX_BASIS:
        return None

    # Unknowns: Q[i][j] for i <= j. Equation per product monomial.
    idx = [(i, j) for i in range(k) for j in range(i, k)]
    col = {ij: c for c, ij in enumerate(idx)}
    products: dict[tuple[int, ...], list[tuple[int, int]]] = {}
    for c, (i, j) in enumerate(idx):
        prod = tuple(a + b for a, b in zip(basis[i], basis[j]))
        products.setdefault(prod, []).append((c, 1 if i == j else 2))
    target = dict(p.terms)
    if any(mono not in products for mono in target):
        return None
    monos = sorted(products)
    rows = []
    for mono in monos:
        row = [Q(0)] * len(idx)
        for c, mult in products[mono]:
            row[c] = Q(mult)
        rows.append(row)
    rhs = [target.get(mono, Q(0)) for mono in monos]
    solved = _rref_solution(rows, rhs, len(idx))
    if solved is None:
        return None
    x0, null = solved

    import numpy as np

    def to_matrix(x):
        mat = np.zeros((k, k))
        for c, (i, j) in enumerate(idx):
            mat[i, j] = mat[j, i] = x[c]
        return mat

    def from_matrix(mat):
        return np.array([mat[i, j] for (i, j) in idx])

    X0 = np.array([float(v) for v in x0])
    N = np.array([[float(v) for v in vec] for vec in null]).T if null else np.zeros((len(idx), 0))
    # Metric for projecting onto the affine space in MATRIX (Frobenius) norm:
    # off-diagonal unknowns appear twice in the matrix.
    w = np.array([1.0 if i == j else 2.0 for (i, j) in idx])
    NtW = N.T * w if N.shape[1] else N.T
    gram = NtW @ N if N.shape[1] else None

    x = X0.copy()
    for _ in range(4000):
        if monotonic() > deadline:
            break
        vals, vecs = np.linalg.eigh(to_matrix(x))
        if vals.min() >= -1e-12:
            break
        psd = (vecs * np.clip(vals, 0, None)) @ vecs.T
        y = from_matrix(psd)
        if N.shape[1]:
            t = np.linalg.solve(gram, NtW @ (y - X0))
            x = X0 + N @ t
        else:
            x = X0
            break

    # Exact reconstruction at increasing denominators.
    if N.shape[1]:
        t = np.linalg.lstsq(N * np.sqrt(w)[:, None], (x - X0) * np.sqrt(w), rcond=None)[0]
    else:
        t = np.zeros(0)
    basis_polys = [Poly.monomial(p.n, e) for e in basis]
    for denom in (1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 64, 128, 256, 1024, 4096):
        if monotonic() > deadline:
            break
        tq = [Q(float(v)).limit_denominator(denom) for v in t]
        xq = list(x0)
        for coeff, vec in zip(tq, null):
            if coeff:
                xq = [a + coeff * b for a, b in zip(xq, vec)]
        mat = [[Q(0)] * k for _ in range(k)]
        for c, (i, j) in enumerate(idx):
            mat[i][j] = mat[j][i] = xq[c]
        terms = _ldl_terms(mat, basis_polys)
        if terms is None:
            continue
        cert = ConeCertificate(tuple(terms))
        if check_cone(p, [], [], cert):
            return cert
    return None
