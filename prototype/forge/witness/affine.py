"""Affine Skolem witnesses with exact Farkas certificates over Q.

PROVENANCE
  BASE  p2-obligation-controller/prototype/forge_proto/witness.py -- Affine,
        WitnessProblem, WitnessCertificate, check_witness and synthesize_witness
        (exact coefficient identities for h(x, Mx+c) = slack + sum lambda_i g_i(x),
        with nonnegative multipliers and slacks).
  FOLD  p1-structural-search/prototype/forge/synthesis.py -- AffineWitness with
        check_affine_witness / synthesize_affine_witness, including its integral
        mode (every coefficient required to have denominator 1).

A witness here is a TERM in the universally quantified inputs, not values read
off one satisfying assignment. There is no integer or strict-inequality
inference in the Farkas half; the integral mode applies to the p1 form only.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from typing import Sequence
from ..linalg import exact_feasible, solve_linear


# ---------------------------------------------------------------------------
# p2: affine witnesses with Farkas multipliers.
# ---------------------------------------------------------------------------
@dataclass(frozen=True)
class Affine:
    coefficients: tuple[Q, ...]
    constant: Q = Q(0)

    def __post_init__(self):
        if not isinstance(self.constant, Q) or any(not isinstance(c, Q) for c in self.coefficients):
            raise TypeError('exact Fraction coefficients required')

    @classmethod
    def make(cls, coefficients, constant=0):
        return cls(tuple(Q(c) for c in coefficients), Q(constant))

    def evaluate(self, values):
        if len(values) != len(self.coefficients):
            raise ValueError('arity mismatch')
        return self.constant + sum((a * Q(x) for a, x in zip(self.coefficients, values)), Q(0))


@dataclass(frozen=True)
class WitnessProblem:
    inputs: int
    outputs: int
    domain: tuple[Affine, ...]  # g_i(x) >= 0
    goals: tuple[Affine, ...]   # h_k(x,y) >= 0, x coefficients first

    def __post_init__(self):
        if self.inputs < 1 or self.outputs < 1:
            raise ValueError('positive dimensions required')
        if any(len(g.coefficients) != self.inputs for g in self.domain):
            raise ValueError('domain arity mismatch')
        if any(len(g.coefficients) != self.inputs + self.outputs for g in self.goals):
            raise ValueError('goal arity mismatch')


@dataclass(frozen=True)
class WitnessCertificate:
    witnesses: tuple[Affine, ...]
    multipliers: tuple[tuple[Q, ...], ...]
    slacks: tuple[Q, ...]

    def to_json(self):
        return {'witnesses': [{'coefficients': list(map(str, w.coefficients)),
                               'constant': str(w.constant)} for w in self.witnesses],
                'multipliers': [[str(c) for c in row] for row in self.multipliers],
                'slacks': list(map(str, self.slacks))}


def check_witness(problem: WitnessProblem, cert: WitnessCertificate) -> bool:
    n, m = problem.inputs, problem.outputs
    if (len(cert.witnesses) != m or any(len(w.coefficients) != n for w in cert.witnesses)
            or len(cert.multipliers) != len(problem.goals)
            or len(cert.slacks) != len(problem.goals)):
        return False
    for goal, lambdas, slack in zip(problem.goals, cert.multipliers, cert.slacks):
        if (len(lambdas) != len(problem.domain) or not isinstance(slack, Q)
                or any(not isinstance(c, Q) for c in lambdas)
                or slack < 0 or any(c < 0 for c in lambdas)):
            return False
        # Exact coefficient identities for h(x, Mx+c) = slack + sum lambda_i g_i(x).
        for j in range(n):
            lhs = goal.coefficients[j] + sum(
                (goal.coefficients[n + k] * cert.witnesses[k].coefficients[j]
                 for k in range(m)), Q(0))
            rhs = sum((l * g.coefficients[j] for l, g in zip(lambdas, problem.domain)), Q(0))
            if lhs != rhs:
                return False
        lhs = goal.constant + sum((goal.coefficients[n + k] * cert.witnesses[k].constant
                                   for k in range(m)), Q(0))
        rhs = slack + sum((l * g.constant for l, g in zip(lambdas, problem.domain)), Q(0))
        if lhs != rhs:
            return False
    return True


def synthesize_witness(problem: WitnessProblem,
                       constant_only: bool = False) -> WitnessCertificate | None:
    n, m = problem.inputs, problem.outputs
    r, s = len(problem.domain), len(problem.goals)
    # Unknowns: flattened rows [M_k,*, c_k], then each [lambda_k,*, slack_k].
    witness_width = m * (n + 1)
    total = witness_width + s * (r + 1)
    a, b = [], []
    for k, goal in enumerate(problem.goals):
        for j in range(n + 1):
            row = [Q(0)] * total
            for out in range(m):
                row[out * (n + 1) + j] = goal.coefficients[n + out]
            for i, g in enumerate(problem.domain):
                row[witness_width + k * (r + 1) + i] = -(g.coefficients[j] if j < n else g.constant)
            if j == n:
                row[witness_width + k * (r + 1) + r] = -1
            a.append(row)
            b.append(-(goal.coefficients[j] if j < n else goal.constant))
    if constant_only:
        for out in range(m):
            for j in range(n):
                row = [Q(0)] * total
                row[out * (n + 1) + j] = 1
                a.append(row)
                b.append(Q(0))
    solved = exact_feasible(a, b, [False] * witness_width + [True] * (s * (r + 1)))
    if solved is None:
        return None
    cert = WitnessCertificate(
        tuple(Affine.make(solved[k * (n + 1):k * (n + 1) + n], solved[k * (n + 1) + n])
              for k in range(m)),
        tuple(tuple(solved[witness_width + k * (r + 1):witness_width + k * (r + 1) + r])
              for k in range(s)),
        tuple(solved[witness_width + k * (r + 1) + r] for k in range(s)))
    return cert if check_witness(problem, cert) else None


# ---------------------------------------------------------------------------
# p1: parametric witnesses for A W = B, A d = c, with an optional integral mode.
# ---------------------------------------------------------------------------
@dataclass(frozen=True)
class AffineWitness:
    """w = linear*x + offset, with exact rational coefficients."""
    linear: tuple[tuple[Q, ...], ...]
    offset: tuple[Q, ...]


def _shape(a, b, c) -> tuple[int, int, int]:
    if not a or not b or len(a) != len(b) or len(a) != len(c):
        raise ValueError('nonempty compatible equation arrays required')
    k, p = len(a[0]), len(b[0])
    if k < 1 or p < 1 or any(len(r) != k for r in a) or any(len(r) != p for r in b):
        raise ValueError('ragged or empty matrix')
    return len(a), k, p


def check_affine_witness(a, b, c, witness: AffineWitness,
                         require_integral: bool = False) -> bool:
    """Verify A W = B and A d = c. This does not check extra inequalities."""
    try:
        m, k, p = _shape(a, b, c)
        if len(witness.linear) != k or len(witness.offset) != k:
            return False
        if any(len(r) != p for r in witness.linear):
            return False
        coeffs = [z for r in witness.linear for z in r] + list(witness.offset)
        if any(not isinstance(z, Q) for z in coeffs):
            return False
        if require_integral and any(z.denominator != 1 for z in coeffs):
            return False
        for i in range(m):
            if sum((Q(a[i][j]) * witness.offset[j] for j in range(k)), Q(0)) != Q(c[i]):
                return False
            for t in range(p):
                if sum((Q(a[i][j]) * witness.linear[j][t] for j in range(k)), Q(0)) != Q(b[i][t]):
                    return False
        return True
    except (ValueError, TypeError, AttributeError, IndexError):
        return False


def synthesize_affine_witness(a, b, c, require_integral: bool = False) -> AffineWitness | None:
    _, k, p = _shape(a, b, c)
    columns = []
    for t in range(p):
        column = solve_linear(a, [r[t] for r in b], k)
        if column is None:
            return None
        columns.append(column)
    offset = solve_linear(a, c, k)
    if offset is None:
        return None
    witness = AffineWitness(
        tuple(tuple(columns[t][j] for t in range(p)) for j in range(k)), tuple(offset))
    return witness if check_affine_witness(a, b, c, witness, require_integral) else None
