"""Exact certificate CHECKING. There is deliberately no search code in here.

PROVENANCE
  BASE  p1-structural-search/prototype/forge/certificates.py::check_cone
        (full validation: Fraction weight, weight >= 0, integer exponents,
        matching arity, exact multiplier count) plus its Bernstein split-tree
        checker, split_box, tree_size/tree_json/cone_json.
  MERGE p5-certificate-first/prototype/forge/checkers.py --
        InvariantCertificate(invariant, initial, transition) with check_invariant,
        and p5's Bernstein reconstruction performed in the ORIGINAL x coordinates
        (exposed here as CoefficientLeaf/CoefficientSplit + check_bernstein_expansion;
        p1's lower-bound tree keeps the BernsteinLeaf/BernsteinSplit names).

Every acceptance path uses Fraction arithmetic only -- no floats, no tolerance,
no LP. These checkers are tested, not formally verified, and are not Lean.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
from math import comb, prod
from typing import Sequence
from .poly import Poly, Box, bernstein_coefficients as _bernstein_pairs


@dataclass(frozen=True)
class ConeTerm:
    weight: Q
    square: Poly
    powers: tuple[int, ...] = ()


@dataclass(frozen=True)
class ConeCertificate:
    terms: tuple[ConeTerm, ...]
    equality_multipliers: tuple[Poly, ...] = ()


def check_cone(target: Poly, inequalities: Sequence[Poly], equalities: Sequence[Poly],
               cert: ConeCertificate) -> bool:
    """Check target = sum c*q^2*prod(g_i^a_i) + sum r_j*h_j.

    Semantics: if every g_i >= 0 and every h_j = 0, then target >= 0.
    The original goal/hypotheses, not certificate metadata, supply the
    polynomials, so a certificate can never silently replace the problem.
    """
    if not isinstance(cert, ConeCertificate):
        return False
    try:
        if any(p.n != target.n for p in [*inequalities, *equalities]):
            return False
        if len(cert.equality_multipliers) != len(equalities):
            return False
        total = Poly.const(target.n, 0)
        for term in cert.terms:
            if not isinstance(term.weight, Q) or isinstance(term.weight, bool):
                return False
            if term.weight < 0:
                return False
            if term.square.n != target.n or len(term.powers) != len(inequalities):
                return False
            if any(type(k) is not int or k < 0 for k in term.powers):
                return False
            p = term.weight * term.square ** 2
            for g, k in zip(inequalities, term.powers):
                p *= g ** k
            total += p
        for h, r in zip(equalities, cert.equality_multipliers):
            total += h * r
        return total == target
    except (ValueError, TypeError, AttributeError):
        return False


def powers_from_indices(indices: Sequence[int], count: int) -> tuple[int, ...]:
    """Convert p5/p7/p8-style factor index multisets into p1-style power tuples."""
    powers = [0] * count
    for i in indices:
        if type(i) is not int or not 0 <= i < count:
            raise ValueError('invalid hypothesis index')
        powers[i] += 1
    return tuple(powers)


# ----------------------------------------------------------------------------
# Conserved-quantity (equality) invariants -- p5.
# ----------------------------------------------------------------------------
@dataclass(frozen=True)
class InvariantCertificate:
    invariant: Poly
    initial: tuple[Q, ...]
    transition: tuple[Poly, ...]


def check_invariant(cert: InvariantCertificate) -> bool:
    """A conserved-polynomial certificate: I(s0)=0 and I(T(s))=I(s).

    Sufficient, not necessary, for an inductive equality invariant. The base and
    step obligations are universal polynomial identities, never sampled points.
    """
    try:
        return (cert.invariant.evaluate(cert.initial) == 0 and
                cert.invariant.substitute(cert.transition) == cert.invariant)
    except (ValueError, TypeError, AttributeError):
        return False


# ----------------------------------------------------------------------------
# Bernstein: p1's lower-bound split tree.
# ----------------------------------------------------------------------------
@dataclass(frozen=True)
class BernsteinLeaf:
    lower_bound: Q


@dataclass(frozen=True)
class BernsteinSplit:
    axis: int
    point: Q
    left: 'BernsteinTree'
    right: 'BernsteinTree'


BernsteinTree = BernsteinLeaf | BernsteinSplit


def bernstein_coefficients(p: Poly, box: Box, max_coefficients: int = 100_000) -> dict:
    """Tensor-product Bernstein coefficients keyed by multi-index (p1 shape)."""
    degrees, values = _bernstein_pairs(p, box, max_coefficients)
    return dict(zip(product(*(range(d + 1) for d in degrees)), values))


def split_box(box: Box, axis: int, point: Q) -> tuple[Box, Box]:
    if type(axis) is not int or not 0 <= axis < len(box) or not isinstance(point, Q):
        raise ValueError('invalid split')
    l, u = box[axis]
    if not l < point < u:
        raise ValueError('split must lie strictly inside the interval')
    left, right = list(box), list(box)
    left[axis], right[axis] = (l, point), (point, u)
    return tuple(left), tuple(right)


def check_bernstein(p: Poly, box: Box, tree: BernsteinTree,
                    max_nodes: int = 100_000) -> bool:
    """Check every leaf and complete domain coverage, not just selected boxes."""
    stack = [(box, tree)]
    nodes = 0
    try:
        while stack:
            domain, node = stack.pop()
            nodes += 1
            if nodes > max_nodes:
                return False
            if isinstance(node, BernsteinLeaf):
                if not isinstance(node.lower_bound, Q) or node.lower_bound < 0:
                    return False
                if min(bernstein_coefficients(p, domain).values()) < node.lower_bound:
                    return False
            elif isinstance(node, BernsteinSplit):
                left, right = split_box(domain, node.axis, node.point)
                stack.extend([(left, node.left), (right, node.right)])
            else:
                return False
        return True
    except (ValueError, TypeError, AttributeError):
        return False


def tree_size(tree: BernsteinTree) -> tuple[int, int]:
    """(leaf count, maximum split depth)."""
    if isinstance(tree, BernsteinLeaf):
        return 1, 0
    a, d = tree_size(tree.left)
    b, e = tree_size(tree.right)
    return a + b, 1 + max(d, e)


def tree_json(tree: BernsteinTree) -> dict:
    if isinstance(tree, BernsteinLeaf):
        return {'leaf': str(tree.lower_bound)}
    return {'axis': tree.axis, 'point': str(tree.point),
            'left': tree_json(tree.left), 'right': tree_json(tree.right)}


def cone_json(cert: ConeCertificate) -> dict:
    return {'terms': [{'weight': str(t.weight), 'square': t.square.json(),
                       'powers': list(t.powers)} for t in cert.terms],
            'equality_multipliers': [p.json() for p in cert.equality_multipliers]}


# ----------------------------------------------------------------------------
# Bernstein: p5's explicit-coefficient tree, reconstructed in ORIGINAL x
# coordinates. This never calls the search-side power-to-Bernstein formula.
# ----------------------------------------------------------------------------
@dataclass(frozen=True)
class CoefficientLeaf:
    box: Box
    degrees: tuple[int, ...]
    coefficients: tuple[tuple[tuple[int, ...], Q], ...]


@dataclass(frozen=True)
class CoefficientSplit:
    box: Box
    axis: int
    cut: Q
    left: 'CoefficientTree'
    right: 'CoefficientTree'


CoefficientTree = CoefficientLeaf | CoefficientSplit


def check_bernstein_expansion(target: Poly, box: Box, tree: CoefficientTree) -> bool:
    """Reconstruct every Bernstein identity over a full binary box cover (p5)."""
    try:
        if len(box) != target.n or any(a >= b for a, b in box) or tree.box != box:
            return False
        if isinstance(tree, CoefficientSplit):
            i, cut = tree.axis, tree.cut
            if type(i) is not int or not 0 <= i < len(box) or not isinstance(cut, Q):
                return False
            if not box[i][0] < cut < box[i][1]:
                return False
            left, right = list(box), list(box)
            left[i] = (box[i][0], cut)
            right[i] = (cut, box[i][1])
            return (check_bernstein_expansion(target, tuple(left), tree.left) and
                    check_bernstein_expansion(target, tuple(right), tree.right))
        if not isinstance(tree, CoefficientLeaf) or len(tree.degrees) != target.n:
            return False
        if any(type(d) is not int or d < 0 or d > 64 for d in tree.degrees):
            return False
        if prod(d + 1 for d in tree.degrees) > 100_000:
            return False
        expected = list(product(*(range(d + 1) for d in tree.degrees)))
        if [k for k, _ in tree.coefficients] != expected:
            return False
        if any(not isinstance(c, Q) or isinstance(c, bool) or c < 0
               for _, c in tree.coefficients):
            return False
        vs = [Poly.var(target.n, i) for i in range(target.n)]
        acc = Poly.const(target.n, 0)
        # Work directly in original x coordinates, unlike discovery in t.
        for idx, c in tree.coefficients:
            term = Poly.const(target.n, c)
            for i, (k, d) in enumerate(zip(idx, tree.degrees)):
                a, b = box[i]
                w = b - a
                term *= comb(d, k) * (vs[i] - a) ** k * (b - vs[i]) ** (d - k) * (Q(1) / w ** d)
            acc += term
        return acc == target
    except (ValueError, TypeError, AttributeError, IndexError, ZeroDivisionError):
        return False


def coefficient_leaves(tree: CoefficientTree) -> int:
    return 1 if isinstance(tree, CoefficientLeaf) else (
        coefficient_leaves(tree.left) + coefficient_leaves(tree.right))
