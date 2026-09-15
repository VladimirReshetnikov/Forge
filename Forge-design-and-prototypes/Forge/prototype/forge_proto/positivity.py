"""Exact certificate formats and untrusted searches for polynomial nonnegativity."""
from __future__ import annotations
from dataclasses import dataclass, field
from fractions import Fraction as Q
from itertools import product
from typing import Sequence
from .poly import Poly, bernstein_coefficients, monomials
from .linear import exact_feasible


@dataclass(frozen=True)
class WeightedSquare:
    weight: Q
    square_root: Poly
    constraint: int | None = None


@dataclass(frozen=True)
class SOSCertificate:
    squares: tuple[WeightedSquare, ...]

    def to_json(self):
        return {"squares": [{"weight": str(s.weight), "root": s.square_root.to_json(),
                             "constraint": s.constraint} for s in self.squares]}


def check_sos(p: Poly, constraints: Sequence[Poly], cert: SOSCertificate) -> bool:
    """Checks p = sum w*q^2 + sum w*q^2*g_i, w>=0.

    The conclusion is conditional on EACH input constraint g_i >= 0.
    Constraints and the target are supplied by the caller, not trusted from cert.
    """
    try:
        if any(g.n != p.n for g in constraints):
            return False
        total = Poly.constant(p.n, 0)
        for entry in cert.squares:
            if not isinstance(entry.weight, Q) or entry.weight < 0 or entry.square_root.n != p.n:
                return False
            g = Poly.constant(p.n, 1)
            if entry.constraint is not None:
                if type(entry.constraint) is not int or not 0 <= entry.constraint < len(constraints):
                    return False
                g = constraints[entry.constraint]
            total += entry.weight * entry.square_root ** 2 * g
        return total == p
    except (ValueError, TypeError, IndexError):
        return False


def square_dictionary(n: int, degree: int = 2) -> list[Poly]:
    """Finite library: monomials, plus their pairwise sums and differences."""
    ms = monomials(n, degree)
    out = list(ms)
    for i, a in enumerate(ms):
        for b in ms[i + 1:]:
            out.extend([a + b, a - b])
    return out


def search_sos(p: Poly, roots: Sequence[Poly], constraints: Sequence[Poly] = ()) -> SOSCertificate | None:
    if any(q.n != p.n for q in [*roots, *constraints]):
        raise ValueError("polynomial arity mismatch")
    generators, entries = [], []
    for i in [None, *range(len(constraints))]:
        g = Poly.constant(p.n, 1) if i is None else constraints[i]
        for q in roots:
            generators.append(q ** 2 * g)
            entries.append((q, i))
    basis = sorted({e for poly in [p, *generators] for e, _ in poly.terms})
    weights = exact_feasible([[g.coefficient(e) for g in generators] for e in basis],
                             [p.coefficient(e) for e in basis], [True] * len(generators))
    if weights is None:
        return None
    cert = SOSCertificate(tuple(WeightedSquare(w, q, i)
                                for w, (q, i) in zip(weights, entries) if w))
    return cert if check_sos(p, constraints, cert) else None


@dataclass
class BernsteinResult:
    status: str
    tree: dict | None = None
    counterexample: tuple[Q, ...] | None = None
    visited: int = 0
    leaves: int = 0
    deepest: int = 0


def search_bernstein(p: Poly, box: Sequence[tuple[Q, Q]], max_depth: int = 10,
                     strict: bool = False, max_nodes: int = 10000) -> BernsteinResult:
    """Status is certified, refuted, or unknown. Bounds and samples are exact."""
    box = tuple((Q(a), Q(b)) for a, b in box)
    if len(box) != p.n or any(a >= b for a, b in box):
        raise ValueError("invalid box")
    result = BernsteinResult("unknown")

    def visit(bounds, depth):
        if result.visited >= max_nodes:
            return None
        result.visited += 1
        result.deepest = max(result.deepest, depth)
        coefficients = bernstein_coefficients(p, bounds)
        if all(c > 0 if strict else c >= 0 for c in coefficients):
            result.leaves += 1
            return {"kind": "leaf"}
        points = [tuple((a + b) / 2 for a, b in bounds)]
        points.extend(product(*[(a, b) for a, b in bounds]))
        for point in points:
            value = p.evaluate(point)
            if value <= 0 if strict else value < 0:
                result.status, result.counterexample = "refuted", tuple(point)
                return None
        if depth >= max_depth:
            return None
        axis = depth % p.n  # Fair shrinking of every coordinate along every path.
        lo, hi = bounds[axis]
        mid = (lo + hi) / 2
        left, right = list(bounds), list(bounds)
        left[axis], right[axis] = (lo, mid), (mid, hi)
        ltree = visit(tuple(left), depth + 1)
        if ltree is None:
            return None
        rtree = visit(tuple(right), depth + 1)
        if rtree is None:
            return None
        return {"kind": "split", "axis": axis, "point": str(mid), "left": ltree, "right": rtree}

    tree = visit(box, 0)
    if tree is not None:
        result.status, result.tree = "certified", tree
    return result


def check_bernstein(p: Poly, box: Sequence[tuple[Q, Q]], tree: dict,
                    strict: bool = False, max_nodes: int = 100000) -> bool:
    """Independent replay: recompute all coefficients and validate full coverage.

    Limits reject oversized/malformed inputs, not prove anything about them.
    """
    remaining = max_nodes
    try:
        bounds = tuple((Q(a), Q(b)) for a, b in box)
        if len(bounds) != p.n or any(a >= b for a, b in bounds):
            return False

        def check(b, node, depth):
            nonlocal remaining
            remaining -= 1
            if remaining < 0 or depth > 200 or not isinstance(node, dict):
                return False
            if node.get("kind") == "leaf":
                return all(c > 0 if strict else c >= 0 for c in bernstein_coefficients(p, b))
            if node.get("kind") != "split":
                return False
            axis = node["axis"]
            if type(axis) is not int or not 0 <= axis < p.n:
                return False
            point = Q(node["point"])
            lo, hi = b[axis]
            if not lo < point < hi:
                return False
            left, right = list(b), list(b)
            left[axis], right[axis] = (lo, point), (point, hi)
            return check(tuple(left), node["left"], depth + 1) and check(tuple(right), node["right"], depth + 1)

        return check(bounds, tree, 0)
    except (KeyError, TypeError, ValueError, ZeroDivisionError, RecursionError):
        return False
