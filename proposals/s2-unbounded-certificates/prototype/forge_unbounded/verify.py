"""Finite, exact certificate checks. This module never imports search.

Shared code is restricted to data shapes, validation and serialization.
The arithmetic below is deliberately implemented separately from producers.
No claim of formal verification or hostile-input hardening is made.
"""
from __future__ import annotations
from fractions import Fraction as Q
from typing import Any
from .model import Petri, PPS, Problem, nat, rat, subject, validate_object, vector


def _qvec(xs: Any, n: int) -> list[Q]:
    if not isinstance(xs, list) or len(xs) != n:
        raise ValueError("rational vector dimension")
    return [rat(x) for x in xs]


def _matrix(xs: Any, n: int) -> list[list[Q]]:
    if not isinstance(xs, list) or len(xs) != n:
        raise ValueError("rational matrix dimension")
    return [_qvec(row, n) for row in xs]


def _eval(p: PPS, x: list[Q]) -> list[Q]:
    # Unlike search.evaluate, build factors, then multiply left to right.
    values = []
    for row in p.polynomials:
        terms = []
        for t in row:
            z = t.coefficient
            for i in range(p.d):
                for _ in range(t.powers[i]):
                    z *= x[i]
            terms.append(z)
        values.append(sum(terms, Q(0)))
    return values


def _derivative(p: PPS, x: list[Q]) -> list[list[Q]]:
    out = []
    for row in p.polynomials:
        deriv = []
        for j in range(p.d):
            z = Q(0)
            for t in row:
                k = t.powers[j]
                if k == 0:
                    continue
                term = Q(k) * t.coefficient
                for i in range(p.d):
                    for _ in range(t.powers[i] - (1 if i == j else 0)):
                        term *= x[i]
                z += term
            deriv.append(z)
        out.append(deriv)
    return out


def _below(a: tuple[int, ...], b: tuple[int, ...]) -> bool:
    return len(a) == len(b) and not any(a[i] > b[i] for i in range(len(a)))


def _index(k: Any, n: int) -> int:
    k = nat(k)
    if k >= n:
        raise ValueError("index outside certificate")
    return k


def _petri(p: Petri, c: dict) -> bool:
    if c["kind"] == "coverable":
        m = list(p.initial)
        if not isinstance(c["word"], list):
            return False
        for symbol in c["word"]:
            pre, post = p.transitions[_index(symbol, len(p.transitions))]
            if any(m[i] < pre[i] for i in range(p.d)):
                return False
            # Operational firing, not the search's backward recurrence.
            m = [m[i] - pre[i] + post[i] for i in range(p.d)]
        return any(_below(t, tuple(m)) for t in p.targets)
    if c["kind"] != "safe":
        return False
    basis = [vector(x, p.d) for x in c["basis"]]
    covers = c["target_cover"]
    predecessors = c["predecessor_cover"]
    if len(covers) != len(p.targets) or len(predecessors) != len(basis):
        return False
    if any(_below(b, p.initial) for b in basis):
        return False
    for target, i in zip(p.targets, covers, strict=True):
        if not _below(basis[_index(i, len(basis))], target):
            return False
    for b, row in zip(basis, predecessors, strict=True):
        if len(row) != len(p.transitions):
            return False
        for (pre, post), k in zip(p.transitions, row, strict=True):
            a = basis[_index(k, len(basis))]
            # Minimal enabling-and-reaching threshold written directly as
            # max(pre, pre+bad-post), independently of producer code.
            for j in range(p.d):
                threshold = max(pre[j], pre[j] + b[j] - post[j])
                if a[j] > threshold:
                    return False
    return True


def _enclosure(p: PPS, c: dict) -> bool:
    n = p.d
    lower = [Q(0)] * n
    if not isinstance(c["ledger"], list):
        return False
    for step in c["ledger"]:
        nxt = _qvec(step["next"], n)
        if any(not (lower[i] <= nxt[i] <= 1) for i in range(n)):
            return False
        value = _eval(p, lower)
        if step["kind"] == "kleene":
            if any(nxt[i] > value[i] for i in range(n)):
                return False
        elif step["kind"] == "newton":
            inv = _matrix(step["inverse"], n)
            if any(v < 0 for row in inv for v in row):
                return False
            j = _derivative(p, lower)
            # Only check multiplication; never solve or invert a matrix here.
            for r in range(n):
                for s in range(n):
                    v = sum((inv[r][k] * (Q(k == s) - j[k][s])
                             for k in range(n)), Q(0))
                    if v != Q(r == s):
                        return False
            delta = [sum((inv[r][k] * (value[k] - lower[k])
                          for k in range(n)), Q(0)) for r in range(n)]
            if any(delta[i] < 0 or nxt[i] > lower[i] + delta[i] for i in range(n)):
                return False
        elif step["kind"] == "weighted_newton":
            weight = _qvec(step["weight"], n)
            direction = _qvec(step["direction"], n)
            if any(v <= 0 for v in weight) or any(v < 0 for v in direction):
                return False
            j = _derivative(p, lower)
            # A weighted maximum principle, not matrix inversion, licenses
            # the lower step. Strictness in EVERY row is required here.
            for i in range(n):
                jw = sum((j[i][k] * weight[k] for k in range(n)), Q(0))
                jd = sum((j[i][k] * direction[k] for k in range(n)), Q(0))
                if jw >= weight[i]:
                    return False
                if direction[i] - jd > value[i] - lower[i]:
                    return False
                if nxt[i] > lower[i] + direction[i]:
                    return False
        else:
            return False
        lower = nxt
    if lower != _qvec(c["lower"], n):
        return False
    upper = _qvec(c["upper"], n)
    if any(not (lower[i] <= upper[i] <= 1) for i in range(n)):
        return False
    value = _eval(p, upper)
    if any(value[i] > upper[i] for i in range(n)):
        return False
    bits = nat(c["requested_bits"])
    met = max(upper[i] - lower[i] for i in range(n)) <= Q(1, 1 << bits)
    if type(c["target_met"]) is not bool or c["target_met"] != met:
        return False
    if "contraction" in c:
        w = _qvec(c["contraction"]["weight"], n)
        rho = rat(c["contraction"]["rho"])
        if not 0 <= rho < 1 or any(v <= 0 for v in w):
            return False
        j = _derivative(p, upper)
        if any(sum((j[i][k] * w[k] for k in range(n)), Q(0)) > rho * w[i]
               for i in range(n)):
            return False
    return True


def _connected(m: list[list[Q]], reverse: bool) -> bool:
    n = len(m)
    seen, frontier = {0}, [0]
    while frontier:
        i = frontier.pop()
        for j in range(n):
            entry = m[j][i] if reverse else m[i][j]
            if entry > 0 and j not in seen:
                seen.add(j)
                frontier.append(j)
    return len(seen) == n


def _critical(p: PPS, c: dict) -> bool:
    n = p.d
    if _eval(p, [Q(1)] * n) != [Q(1)] * n:
        return False
    w = _qvec(c["weight"], n)
    if any(v <= 0 for v in w):
        return False
    m = _derivative(p, [Q(1)] * n)
    if not _connected(m, False) or not _connected(m, True):
        return False
    mw = [sum((m[i][j] * w[j] for j in range(n)), Q(0)) for i in range(n)]
    if any(mw[i] > w[i] for i in range(n)):
        return False
    strict_row = any(mw[i] < w[i] for i in range(n))
    branching = any(sum(t.powers) >= 2 and t.coefficient > 0
                    for row in p.polynomials for t in row)
    # Without this final condition, P(x)=x would be accepted unsoundly.
    return strict_row or branching


def _trim(a: list[Q]) -> list[Q]:
    a = a.copy()
    while len(a) > 1 and not a[-1]:
        a.pop()
    return a


def _product(a: list[Q], b: list[Q]) -> list[Q]:
    c = [Q(0)] * (len(a) + len(b) - 1)
    for i, u in enumerate(a):
        for j, v in enumerate(b):
            c[i + j] += u * v
    return _trim(c)


def _interval_poly(a: list[Q], lo: Q, hi: Q) -> tuple[Q, Q]:
    l, u = Q(0), Q(0)
    for v in reversed(a):
        corners = (l * lo, l * hi, u * lo, u * hi)
        l, u = min(corners) + v, max(corners) + v
    return l, u


def _algebraic(p: PPS, c: dict) -> bool:
    e = c["enclosure"]
    if p.d != 1 or e.get("kind") != "enclosure" or e.get("subject") != subject(p):
        return False
    if not _enclosure(p, e):
        return False
    g, h = [rat(x) for x in c["factor"]], [rat(x) for x in c["cofactor"]]
    if len(g) < 2 or not h or g[-1] == 0 or h[-1] == 0:
        return False
    degree = max([1] + [t.powers[0] for t in p.polynomials[0]])
    polynomial = [Q(0)] * (degree + 1)
    for t in p.polynomials[0]:
        polynomial[t.powers[0]] += t.coefficient
    polynomial[1] -= 1
    if _product(g, h) != _trim(polynomial):
        return False
    lo, hi = rat(e["lower"][0]), rat(e["upper"][0])
    hl, hu = _interval_poly(h, lo, hi)
    if not (hu < 0 or hl > 0):
        return False
    dg = [Q(i) * g[i] for i in range(1, len(g))]
    dl, du = _interval_poly(dg, lo, hi)
    if not (dl > 0 or du < 0):
        return False
    # The existing enclosure supplies existence of q. Derivative sign supplies
    # uniqueness of the root of g in this exact rational isolating interval.
    return True


def verify(problem: Problem | dict, certificate: Any) -> bool:
    """Accept only a finite certificate bound to the independently supplied input.

    `unknown` is never an accepted proof. An accepted enclosure may still miss
    its requested width; target_met records that separate quantitative outcome.
    """
    try:
        from .model import parse_problem
        p = parse_problem(problem) if isinstance(problem, dict) else validate_object(problem)
        if not isinstance(certificate, dict) or certificate.get("subject") != subject(p):
            return False
        if isinstance(p, Petri):
            return _petri(p, certificate)
        kind = certificate.get("kind")
        if kind == "enclosure":
            return _enclosure(p, certificate)
        if kind == "extinction_one":
            return _critical(p, certificate)
        if kind == "algebraic_lfp":
            return _algebraic(p, certificate)
        return False
    except (KeyError, TypeError, ValueError, IndexError, ZeroDivisionError, OverflowError):
        return False
