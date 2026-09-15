# PROVENANCE: p7-successor-architecture/prototype/lattice.py, VERBATIM.
# Unique to p7 (integer lattice / unimodular elimination); only this banner added.
"""Exact integer witness synthesis with a replayable unimodular trace.

At row i, all solutions of the prefix are x = x0 + B z, z integral.
A column-unimodular U reduces a_i B to (g,0,...,0). One parameter is
eliminated if g divides the residual. A nondivisibility obstruction is a
certificate of impossibility. There is no bounded search for the witnesses.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from math import gcd


def identity(n): return [[int(i == j) for j in range(n)] for i in range(n)]
def dot(a, b): return sum(x*y for x, y in zip(a, b))
def matvec(A, x): return [dot(a, x) for a in A]
def matmul(A, B):
    width = len(B[0]) if B else 0
    return [[sum(a[k]*B[k][j] for k in range(len(B)))
             for j in range(width)] for a in A]


def bezout(a: int, b: int):
    x0, x1, y0, y1 = 1, 0, 0, 1
    aa, bb = a, b
    while bb:
        q = aa // bb
        aa, bb = bb, aa-q*bb
        x0, x1 = x1, x0-q*x1
        y0, y1 = y1, y0-q*y1
    if aa < 0: aa, x0, y0 = -aa, -x0, -y0
    return aa, x0, y0


def reduce_row(v):
    n = len(v); U = identity(n); w = list(v)
    if not n: return U, 0
    for j in range(1, n):
        a, b = w[0], w[j]
        if not b: continue
        g, s, t = bezout(a, b)
        c0, cj = [U[i][0] for i in range(n)], [U[i][j] for i in range(n)]
        for i in range(n):
            U[i][0] = s*c0[i] + t*cj[i]
            U[i][j] = -(b//g)*c0[i] + (a//g)*cj[i]
        w[0], w[j] = g, 0
    if w[0] < 0:
        for row in U: row[0] = -row[0]
        w[0] = -w[0]
    return U, w[0]


@dataclass(frozen=True)
class Step:
    row: int
    transform: tuple[tuple[int, ...], ...]
    gcd: int
    residual: int
    quotient: int | None
    obstruction: bool = False

@dataclass(frozen=True)
class Certificate:
    feasible: bool
    steps: tuple[Step, ...]
    witness: tuple[int, ...] = ()
    basis: tuple[tuple[int, ...], ...] = ()

    def json(self):
        from dataclasses import asdict
        return asdict(self)


def validate_input(A, b):
    if not A or len(A) != len(b): raise ValueError('nonempty matching rows required')
    n = len(A[0])
    if any(len(row) != n for row in A): raise ValueError('ragged matrix')
    if any(type(x) is not int for row in A for x in row): raise TypeError('integer matrix required')
    if any(type(x) is not int for x in b): raise TypeError('integer RHS required')
    return n


def solve(A, b) -> Certificate:
    n = validate_input(A, b)
    x = [0]*n; B = identity(n); dimension = n; steps = []
    for i, (row, rhs) in enumerate(zip(A, b)):
        v = [sum(row[k]*B[k][j] for k in range(n)) for j in range(dimension)]
        residual = rhs-dot(row, x)
        U, g = reduce_row(v)
        bad = residual != 0 if g == 0 else residual % g != 0
        quotient = residual//g if g and not bad else None
        steps.append(Step(i, tuple(map(tuple, U)), g, residual, quotient, bad))
        if bad: return Certificate(False, tuple(steps))
        if g:
            C = matmul(B, U)
            x = [xi+ci[0]*quotient for xi, ci in zip(x, C)]
            B = [ci[1:] for ci in C]; dimension -= 1
    return Certificate(True, tuple(steps), tuple(x), tuple(map(tuple, B)))


def determinant(A):
    """Independent rational elimination for unimodularity checking."""
    n = len(A)
    if any(len(row) != n for row in A): raise ValueError('not square')
    M = [list(map(Fraction, row)) for row in A]; result = Fraction(1)
    for j in range(n):
        pivot = next((i for i in range(j, n) if M[i][j]), None)
        if pivot is None: return 0
        if pivot != j:
            M[pivot], M[j] = M[j], M[pivot]; result = -result
        v = M[j][j]; result *= v
        for i in range(j+1, n):
            c = M[i][j]/v
            for k in range(j+1, n): M[i][k] -= c*M[j][k]
    return result


def check(A, b, cert: Certificate) -> bool:
    """Replays the full-lattice invariant; does not call solve/reduce_row/bezout."""
    try:
        n = validate_input(A, b); x = [0]*n; B = identity(n); d = n
        if not cert.steps or len(cert.steps) > len(A): return False
        for i, step in enumerate(cert.steps):
            if step.row != i: return False
            U = step.transform
            if len(U) != d or any(len(r) != d for r in U): return False
            if any(type(v) is not int for r in U for v in r): return False
            if abs(determinant(U)) != 1: return False
            row = A[i]
            v = [sum(row[k]*B[k][j] for k in range(n)) for j in range(d)]
            w = [sum(v[k]*U[k][j] for k in range(d)) for j in range(d)]
            g = step.gcd
            if type(g) is not int or g < 0: return False
            if w != ([g]+[0]*(d-1) if d else []): return False
            if not d and g != 0: return False
            residual = b[i]-dot(row, x)
            if residual != step.residual: return False
            bad = residual != 0 if g == 0 else residual % g != 0
            if step.obstruction:
                return (bad and not cert.feasible and i == len(cert.steps)-1
                        and not cert.witness and not cert.basis)
            if bad: return False
            if g:
                q = step.quotient
                if type(q) is not int or q*g != residual: return False
                C = matmul(B, U)
                x = [xi+ci[0]*q for xi, ci in zip(x, C)]
                B = [ci[1:] for ci in C]; d -= 1
            elif step.quotient is not None:
                return False
        return (cert.feasible and len(cert.steps) == len(A)
                and tuple(x) == cert.witness and tuple(map(tuple, B)) == cert.basis
                and matvec(A, x) == b)
    except (ValueError, TypeError, IndexError, ZeroDivisionError):
        return False
