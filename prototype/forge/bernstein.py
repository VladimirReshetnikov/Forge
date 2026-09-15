"""Box-subdivision search for polynomial bounds, with independent exact replay.

PROVENANCE
  BASE  p8-obligation-broker/prototype/bernstein.py -- the three-valued
        PROVED / REFUTED(witness) / UNKNOWN Result, replay by EXPANSION in the
        opposite direction from the producer, check_witness, node+depth fuel,
        and size().
  FOLD  p3-planner-certificate-layer/prototype/bernstein.py -- the tensor-size
        cap applied before any expansion, and relative-width axis selection
        (avoids coordinate-unit bias); plus its explicit-coefficient leaf tree,
        which the checker in certificates.py replays in original x coordinates.
  FOLD  p2-obligation-controller/prototype/forge_proto/positivity.py -- the
        `axis = depth % n` fair-shrink mode, and the strict/weak sign flag.

CORRECTNESS FIX (all three sources): leaf degrees are derived from the
affine-TRANSFORMED polynomial, never from the original one.

Everything here is exact rational arithmetic. A negative Bernstein coefficient
proves nothing; only a sampled point with a genuinely negative value refutes.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
from math import prod
from .poly import Poly, Box, bernstein_coefficients, expand_bernstein
from .certificates import (CoefficientLeaf, CoefficientSplit, CoefficientTree,
                           BernsteinLeaf, BernsteinSplit, BernsteinTree,
                           check_bernstein)


@dataclass(frozen=True)
class Leaf:
    coefficients: tuple[Q, ...]


@dataclass(frozen=True)
class Split:
    axis: int
    cut: Q
    left: 'Tree'
    right: 'Tree'


Tree = Leaf | Split


@dataclass(frozen=True)
class Result:
    status: str  # PROVED, REFUTED (exact witness), UNKNOWN (no conclusion)
    tree: Tree | None
    witness: tuple[Q, ...] | None
    nodes: int


def children(box: Box, axis: int, cut: Q) -> tuple[Box, Box]:
    if type(axis) is not int or not 0 <= axis < len(box):
        raise ValueError('invalid split axis')
    l, u = box[axis]
    if not isinstance(cut, Q) or not l < cut < u:
        raise ValueError('cut must be rational and strictly interior')
    a, b = list(box), list(box)
    a[axis], b[axis] = (l, cut), (cut, u)
    return tuple(a), tuple(b)


def _choose_axis(p: Poly, root: Box, b: Box, depth: int, axis_mode: str) -> int:
    if axis_mode == 'depth':
        return depth % p.n  # p2: fair shrinking of every coordinate
    if axis_mode == 'width':
        return max(range(p.n), key=lambda i: (b[i][1] - b[i][0], -i))
    if axis_mode == 'relative':  # p3: largest relative width
        return max(range(p.n),
                   key=lambda i: ((b[i][1] - b[i][0]) / (root[i][1] - root[i][0]), -i))
    raise ValueError('unknown axis selection mode')


def search(p: Poly, box: Box, *, strict: bool = False, max_depth: int = 12,
           max_nodes: int = 10000, axis_mode: str = 'relative') -> Result:
    p.affine_box(box)  # Validate the external domain before starting search.
    if max_depth < 0 or max_nodes < 1:
        raise ValueError('invalid search bounds')
    nodes = 0

    def visit(b: Box, depth: int) -> Result:
        nonlocal nodes
        if nodes >= max_nodes:
            return Result('UNKNOWN', None, None, nodes)
        nodes += 1
        _, cs = bernstein_coefficients(p, b)
        if all(c > 0 if strict else c >= 0 for c in cs):
            return Result('PROVED', Leaf(cs), None, nodes)
        # One genuine counterexample disproves the requested universal bound.
        for pt in [tuple((l + u) / 2 for l, u in b), *product(*[(l, u) for l, u in b])]:
            v = p.evaluate(pt)
            if (v <= 0 if strict else v < 0):
                return Result('REFUTED', None, pt, nodes)
        if depth >= max_depth:
            return Result('UNKNOWN', None, None, nodes)
        j = _choose_axis(p, box, b, depth, axis_mode)
        cut = sum(b[j], Q(0)) / 2
        left_box, right_box = children(b, j, cut)
        left = visit(left_box, depth + 1)
        if left.status != 'PROVED':
            return left
        right = visit(right_box, depth + 1)
        if right.status != 'PROVED':
            return right
        return Result('PROVED', Split(j, cut, left.tree, right.tree), None, nodes)

    return visit(box, 0)


def replay(p: Poly, box: Box, tree: Tree, *, strict: bool = False,
           max_nodes: int = 100000, max_depth: int = 100) -> bool:
    """The polynomial and the entire root box are external, not certificate-owned."""
    remaining = max_nodes

    def visit(b: Box, t: Tree, depth: int) -> bool:
        nonlocal remaining
        remaining -= 1
        if remaining < 0 or depth > max_depth:
            return False
        if isinstance(t, Leaf):
            transformed = p.affine_box(b)
            ds = transformed.degrees  # degrees of the TRANSFORMED polynomial
            if prod(d + 1 for d in ds) > 100_000:
                return False
            if len(t.coefficients) != prod(d + 1 for d in ds):
                return False
            if any(not isinstance(c, Q) or isinstance(c, bool)
                   or (c <= 0 if strict else c < 0) for c in t.coefficients):
                return False
            return expand_bernstein(p.n, ds, t.coefficients) == transformed
        if isinstance(t, Split):
            lb, rb = children(b, t.axis, t.cut)
            return visit(lb, t.left, depth + 1) and visit(rb, t.right, depth + 1)
        return False

    try:
        p.affine_box(box)
        return visit(box, tree, 0)
    except (ValueError, TypeError, AttributeError, RecursionError):
        return False


def check_witness(p: Poly, box: Box, point: tuple[Q, ...], *, strict: bool = False) -> bool:
    try:
        p.affine_box(box)
        if len(point) != p.n or not all(isinstance(x, Q) and l <= x <= u
                                        for x, (l, u) in zip(point, box)):
            return False
        v = p.evaluate(point)
        return v <= 0 if strict else v < 0
    except (ValueError, TypeError):
        return False


def tree_json(t: Tree) -> dict:
    if isinstance(t, Leaf):
        return {'leaf': [str(c) for c in t.coefficients]}
    return {'axis': t.axis, 'cut': str(t.cut),
            'left': tree_json(t.left), 'right': tree_json(t.right)}


def size(t: Tree) -> tuple[int, int]:
    """(node count, leaf count)."""
    if isinstance(t, Leaf):
        return 1, 1
    a, b = size(t.left), size(t.right)
    return 1 + a[0] + b[0], a[1] + b[1]


def bernstein_search(p: Poly, box: Box, max_depth: int = 12,
                     max_nodes: int = 10_000) -> BernsteinTree | None:
    """p1's lower-bound split tree (search only; None is Unknown, not False).

    Kept alongside the p8 coefficient tree because the two carry different
    evidence: this one records a rational lower bound per leaf, which is what
    certificates.check_bernstein re-derives and what the Lean emitter needs.
    """
    if max_depth < 0 or max_nodes < 1:
        raise ValueError('invalid search budget')
    nodes = 0

    def visit(domain: Box, depth: int) -> BernsteinTree | None:
        nonlocal nodes
        nodes += 1
        if nodes > max_nodes:
            return None
        _, coeffs = bernstein_coefficients(p, domain)
        lower = min(coeffs)
        if lower >= 0:
            return BernsteinLeaf(lower)
        # A counterexample can stop search, but it is not returned as a proof.
        midpoint = [(l + u) / 2 for l, u in domain]
        if p.evaluate(midpoint) < 0 or depth == max_depth:
            return None
        axis = _choose_axis(p, box, domain, depth, 'width')
        point = sum(domain[axis], Q(0)) / 2
        left_box, right_box = children(domain, axis, point)
        left = visit(left_box, depth + 1)
        if left is None:
            return None
        right = visit(right_box, depth + 1)
        if right is None:
            return None
        return BernsteinSplit(axis, point, left, right)

    tree = visit(box, 0)
    if tree is None:
        return None
    if not check_bernstein(p, box, tree):
        raise AssertionError('search produced an invalid Bernstein certificate')
    return tree


# ---------------------------------------------------------------------------
# p5/p3 explicit-coefficient tree: leaves carry (box, degrees, coefficients) so
# the checker can rebuild the identity in ORIGINAL x coordinates.
# ---------------------------------------------------------------------------
def discover_coefficient_tree(p: Poly, box: Box, *, depth: int = 8,
                              strict: bool = False,
                              axis_mode: str = 'relative') -> CoefficientTree | None:
    def go(b: Box, remaining: int, level: int) -> CoefficientTree | None:
        degrees, values = bernstein_coefficients(p, b)
        keys = list(product(*(range(d + 1) for d in degrees)))
        if all(c > 0 if strict else c >= 0 for c in values):
            return CoefficientLeaf(b, degrees, tuple(zip(keys, values)))
        if remaining <= 0:
            return None
        axis = _choose_axis(p, box, b, level, axis_mode)
        a, u = b[axis]
        cut = (a + u) / 2
        bl, br = list(b), list(b)
        bl[axis], br[axis] = (a, cut), (cut, u)
        left = go(tuple(bl), remaining - 1, level + 1)
        if left is None:
            return None
        right = go(tuple(br), remaining - 1, level + 1)
        if right is None:
            return None
        return CoefficientSplit(b, axis, cut, left, right)

    return go(box, depth, 0)
