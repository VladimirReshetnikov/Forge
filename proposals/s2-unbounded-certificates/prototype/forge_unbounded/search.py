"""Untrusted producers. All results must pass verify.verify(problem, receipt)."""
from __future__ import annotations
from collections import deque
from fractions import Fraction as Q
from itertools import product
from typing import Sequence
from .model import Petri, PPS, Term, encq, subject, validate_object


def below(a: Sequence[int], b: Sequence[int]) -> bool:
    return all(x <= y for x, y in zip(a, b, strict=True))


def predecessor(b: tuple[int, ...], pre: tuple[int, ...],
                post: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(c + max(0, x - o) for x, c, o in zip(b, pre, post, strict=True))


def petri_coverability(p: Petri, *, max_expansions: int = 100_000,
                       max_basis: int = 20_000) -> dict:
    p = validate_object(p)
    assert isinstance(p, Petri)
    # Historical provenance is never deleted when active antichains are pruned.
    nodes: list[tuple[tuple[int, ...], int | None, int | None]] = []
    active: dict[tuple[int, ...], int] = {}
    work: deque[int] = deque()
    expansions = 0
    peak = 0

    def admit(v: tuple[int, ...], transition: int | None,
              child: int | None) -> int | None:
        nonlocal peak
        if any(below(a, v) for a in active):
            return None
        for a in list(active):
            if below(v, a):
                del active[a]
        k = len(nodes)
        nodes.append((v, transition, child))
        active[v] = k
        work.append(k)
        peak = max(peak, len(active))
        return k

    def positive(k: int) -> dict:
        word = []
        while nodes[k][1] is not None:
            _, transition, child = nodes[k]
            word.append(transition)
            assert child is not None
            k = child
        return {"kind": "coverable", "subject": subject(p), "word": word,
                "stats": {"expansions": expansions, "peak_basis": peak,
                          "provenance_nodes": len(nodes)}}

    for target in p.targets:
        k = admit(target, None, None)
        if k is not None and below(target, p.initial):
            return positive(k)
    while work:
        if expansions >= max_expansions or len(active) > max_basis:
            return {"kind": "unknown", "subject": subject(p),
                    "reason": "coverability budget", "expansions": expansions}
        k = work.popleft()
        b = nodes[k][0]
        if active.get(b) != k:
            continue
        expansions += 1
        for ti, (pre, post) in enumerate(p.transitions):
            v = predecessor(b, pre, post)
            new = admit(v, ti, k)
            if new is not None and below(v, p.initial):
                return positive(new)
    basis = sorted(active)
    # Search for the short finite membership witnesses, not for paths.
    cover = lambda v: next(i for i, a in enumerate(basis) if below(a, v))
    return {"kind": "safe", "subject": subject(p),
            "basis": [list(a) for a in basis],
            "target_cover": [cover(t) for t in p.targets],
            "predecessor_cover": [[cover(predecessor(b, pre, post))
                                   for pre, post in p.transitions] for b in basis],
            "stats": {"expansions": expansions, "peak_basis": peak,
                      "provenance_nodes": len(nodes)}}


def evaluate(p: PPS, x: Sequence[Q]) -> list[Q]:
    result = []
    for row in p.polynomials:
        z = Q(0)
        for term in row:
            v = term.coefficient
            for y, k in zip(x, term.powers, strict=True):
                v *= y ** k
            z += v
        result.append(z)
    return result


def jacobian(p: PPS, x: Sequence[Q]) -> list[list[Q]]:
    ans = [[Q(0) for _ in range(p.d)] for _ in range(p.d)]
    for i, row in enumerate(p.polynomials):
        for t in row:
            for j, degree in enumerate(t.powers):
                if degree:
                    c = t.coefficient * degree
                    for k, e in enumerate(t.powers):
                        c *= x[k] ** (e - int(k == j))
                    ans[i][j] += c
    return ans


def inverse(a: Sequence[Sequence[Q]]) -> list[list[Q]] | None:
    n = len(a)
    mat = [list(row) + [Q(i == j) for j in range(n)] for i, row in enumerate(a)]
    for c in range(n):
        pivot = next((r for r in range(c, n) if mat[r][c]), None)
        if pivot is None:
            return None
        mat[c], mat[pivot] = mat[pivot], mat[c]
        scale = mat[c][c]
        mat[c] = [v / scale for v in mat[c]]
        for r in range(n):
            if r != c:
                f = mat[r][c]
                mat[r] = [v - f * w for v, w in zip(mat[r], mat[c], strict=True)]
    return [row[n:] for row in mat]


def matvec(a: Sequence[Sequence[Q]], x: Sequence[Q]) -> list[Q]:
    return [sum((u * v for u, v in zip(row, x, strict=True)), Q(0)) for row in a]


def one_minus(j: list[list[Q]]) -> list[list[Q]]:
    return [[Q(r == c) - v for c, v in enumerate(row)] for r, row in enumerate(j)]


def floor_dyadic(x: Q, bits: int) -> Q:
    scale = 1 << bits
    return Q((x.numerator * scale) // x.denominator, scale)


def pps_enclosure(p: PPS, *, target_bits: int = 24, rounding_bits: int = 48,
                  max_steps: int = 60) -> dict:
    p = validate_object(p)
    assert isinstance(p, PPS)
    if target_bits < 0 or rounding_bits < target_bits + 4 or max_steps < 0:
        raise ValueError("require rounding_bits >= target_bits + 4 and nonnegative budgets")
    n = p.d
    lower, upper = [Q(0)] * n, [Q(1)] * n
    ledger = []
    target = Q(1, 1 << target_bits)
    for _ in range(max_steps):
        if max(u - l for u, l in zip(upper, lower, strict=True)) <= target:
            break
        f = evaluate(p, lower)
        inv = inverse(one_minus(jacobian(p, lower)))
        residual = [a - b for a, b in zip(f, lower, strict=True)]
        delta = matvec(inv, residual) if inv is not None else None
        if (inv is not None and all(x >= 0 for row in inv for x in row)
                and delta is not None and all(x >= 0 for x in delta)):
            new = [floor_dyadic(l + d, rounding_bits)
                   for l, d in zip(lower, delta, strict=True)]
            if new == lower:
                break
            ledger.append({"kind": "newton", "inverse": [[encq(x) for x in row] for row in inv],
                           "next": [encq(x) for x in new]})
            lower = new
        else:
            new = [max(l, floor_dyadic(y, rounding_bits))
                   for l, y in zip(lower, f, strict=True)]
            if new == lower or any(a > b for a, b in zip(new, f, strict=True)):
                break
            ledger.append({"kind": "kleene", "next": [encq(x) for x in new]})
            lower = new
        # Proposal only: try a rational positive inverse direction. Each upper
        # candidate is admitted by the ORIGINAL nonlinear prefixed inequality.
        inv2 = inverse(one_minus(jacobian(p, lower)))
        direction = matvec(inv2, [Q(1)] * n) if inv2 is not None else [Q(1)] * n
        if not all(w > 0 for w in direction):
            direction = [Q(1)] * n
        for bits in range(0, rounding_bits + 1):
            eps = Q(1, 1 << bits)
            u = [l + eps * w for l, w in zip(lower, direction, strict=True)]
            if any(v > 1 for v in u):
                continue
            if all(y <= v for y, v in zip(evaluate(p, u), u, strict=True)):
                # Min of prefixed points is prefixed for monotone P.
                upper = [min(old, v) for old, v in zip(upper, u, strict=True)]
    receipt = {"kind": "enclosure", "subject": subject(p), "ledger": ledger,
               "lower": [encq(x) for x in lower], "upper": [encq(x) for x in upper],
               "requested_bits": target_bits,
               "target_met": max(u - l for u, l in zip(upper, lower, strict=True)) <= target}
    invu = inverse(one_minus(jacobian(p, upper)))
    if invu is not None:
        w = matvec(invu, [Q(1)] * n)
        if all(v > 0 for v in w):
            jw = matvec(jacobian(p, upper), w)
            rho = max(a / b for a, b in zip(jw, w, strict=True))
            if 0 <= rho < 1:
                receipt["contraction"] = {"weight": [encq(x) for x in w], "rho": encq(rho)}
    return receipt


def nullspace(a: list[list[Q]]) -> list[list[Q]]:
    """Exact RREF basis; a proposal utility, not part of the checker."""
    m = [list(row) for row in a]
    rows, cols = len(m), len(m[0]) if m else 0
    pivots, r = [], 0
    for c in range(cols):
        k = next((i for i in range(r, rows) if m[i][c]), None)
        if k is None:
            continue
        m[r], m[k] = m[k], m[r]
        z = m[r][c]
        m[r] = [v / z for v in m[r]]
        for i in range(rows):
            if i != r:
                z = m[i][c]
                m[i] = [v - z * w for v, w in zip(m[i], m[r], strict=True)]
        pivots.append(c)
        r += 1
        if r == rows:
            break
    result = []
    for f in range(cols):
        if f not in pivots:
            x = [Q(0)] * cols
            x[f] = Q(1)
            for i, c in enumerate(pivots):
                x[c] = -m[i][f]
            result.append(x)
    return result


def critical_extinction(p: PPS) -> dict:
    p = validate_object(p)
    assert isinstance(p, PPS)
    n = p.d
    m = jacobian(p, [Q(1)] * n)
    a = one_minus(m)
    candidates = [[Q(1)] * n]
    inv = inverse(a)
    if inv is not None:
        candidates.append(matvec(inv, [Q(1)] * n))
    for x in nullspace(a):
        candidates.extend([x, [-v for v in x]])
    # The checker (not this producer) establishes strong connectivity and
    # nondegeneracy. Trying all candidates is inexpensive for this prototype.
    from .verify import verify
    for w in candidates:
        result = {"kind": "extinction_one", "subject": subject(p),
                  "weight": [encq(x) for x in w]}
        if verify(p, result):
            return result
    return {"kind": "unknown", "subject": subject(p),
            "reason": "no accepted irreducible spectral certificate"}


def scalar_algebraic(p: PPS, enclosure: dict, factor: list[Q],
                     cofactor: list[Q]) -> dict:
    """Attach an untrusted factorization; verification will check it exactly."""
    if p.d != 1:
        raise ValueError("the algebraic decoder in this prototype is scalar")
    return {"kind": "algebraic_lfp", "subject": subject(p), "enclosure": enclosure,
            "factor": [encq(x) for x in factor],
            "cofactor": [encq(x) for x in cofactor]}
