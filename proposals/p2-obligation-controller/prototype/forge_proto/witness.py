"""Affine Skolem-witness synthesis with exact Farkas certificates over Q/R.

There is NO integer or strict-inequality inference in this prototype. A returned
witness is a term depending on the universally quantified inputs, not values
from one satisfying assignment.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from typing import Sequence
from .linear import exact_feasible


@dataclass(frozen=True)
class Affine:
    coefficients: tuple[Q, ...]
    constant: Q = Q(0)

    def __post_init__(self):
        if not isinstance(self.constant, Q) or any(not isinstance(c, Q) for c in self.coefficients):
            raise TypeError("exact Fraction coefficients required")

    @classmethod
    def make(cls, coefficients, constant=0):
        return cls(tuple(Q(c) for c in coefficients), Q(constant))

    def evaluate(self, values):
        if len(values) != len(self.coefficients):
            raise ValueError("arity mismatch")
        return self.constant + sum((a * Q(x) for a, x in zip(self.coefficients, values)), Q(0))


@dataclass(frozen=True)
class WitnessProblem:
    inputs: int
    outputs: int
    domain: tuple[Affine, ...]  # g_i(x) >= 0
    goals: tuple[Affine, ...]   # h_k(x,y) >= 0, x coefficients first

    def __post_init__(self):
        if self.inputs < 1 or self.outputs < 1:
            raise ValueError("positive dimensions required")
        if any(len(g.coefficients) != self.inputs for g in self.domain):
            raise ValueError("domain arity mismatch")
        if any(len(g.coefficients) != self.inputs + self.outputs for g in self.goals):
            raise ValueError("goal arity mismatch")


@dataclass(frozen=True)
class WitnessCertificate:
    witnesses: tuple[Affine, ...]
    multipliers: tuple[tuple[Q, ...], ...]
    slacks: tuple[Q, ...]

    def to_json(self):
        return {"witnesses": [{"coefficients": list(map(str, w.coefficients)), "constant": str(w.constant)}
                              for w in self.witnesses],
                "multipliers": [[str(c) for c in row] for row in self.multipliers],
                "slacks": list(map(str, self.slacks))}


def check_witness(problem: WitnessProblem, cert: WitnessCertificate) -> bool:
    n, m = problem.inputs, problem.outputs
    if (len(cert.witnesses) != m or any(len(w.coefficients) != n for w in cert.witnesses)
            or len(cert.multipliers) != len(problem.goals) or len(cert.slacks) != len(problem.goals)):
        return False
    for goal, lambdas, slack in zip(problem.goals, cert.multipliers, cert.slacks):
        if (len(lambdas) != len(problem.domain) or not isinstance(slack, Q)
                or any(not isinstance(c, Q) for c in lambdas)
                or slack < 0 or any(c < 0 for c in lambdas)):
            return False
        # Exact coefficient identities for h(x,Mx+c)=slack+sum lambda_i*g_i(x).
        for j in range(n):
            lhs = goal.coefficients[j] + sum((goal.coefficients[n + k] * cert.witnesses[k].coefficients[j]
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


def synthesize_witness(problem: WitnessProblem, constant_only: bool = False) -> WitnessCertificate | None:
    n, m, r, s = problem.inputs, problem.outputs, len(problem.domain), len(problem.goals)
    # Unknowns: flattened rows [M_k,* , c_k], then each [lambda_k,* , slack_k].
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
        tuple(Affine.make(solved[k * (n + 1):k * (n + 1) + n], solved[k * (n + 1) + n]) for k in range(m)),
        tuple(tuple(solved[witness_width + k * (r + 1):witness_width + k * (r + 1) + r]) for k in range(s)),
        tuple(solved[witness_width + k * (r + 1) + r] for k in range(s)))
    return cert if check_witness(problem, cert) else None
