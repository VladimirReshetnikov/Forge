"""Exact certificates for polynomial bounds on rational boxes.

The producer converts power coefficients to Bernstein coefficients. The checker
instead EXPANDS the claimed Bernstein representation. Both use poly.py's exact
arithmetic, which is tested, not formally verified. No floating point is used.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
from math import comb, prod
from poly import Poly, bernstein_coefficients, unit_transform

Box = tuple[tuple[Q, Q], ...]

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


def search(p: Poly, box: Box, *, strict: bool = False,
           max_depth: int = 12, max_nodes: int = 10000) -> Result:
    unit_transform(p, box)  # Validate external domain before starting search.
    if max_depth < 0 or max_nodes < 1:
        raise ValueError('invalid search bounds')
    nodes = 0
    def visit(b: Box, depth: int) -> Result:
        nonlocal nodes
        if nodes >= max_nodes:
            return Result('UNKNOWN', None, None, nodes)
        nodes += 1
        cs = bernstein_coefficients(p, b)
        if all(c > 0 if strict else c >= 0 for c in cs):
            return Result('PROVED', Leaf(cs), None, nodes)
        # One genuine counterexample disproves the requested universal bound.
        for pt in [tuple((l+u)/2 for l,u in b), *product(*[(l,u) for l,u in b])]:
            v = p.evaluate(pt)
            if v <= 0 if strict else v < 0:
                return Result('REFUTED', None, pt, nodes)
        if depth >= max_depth:
            return Result('UNKNOWN', None, None, nodes)
        j = max(range(p.n), key=lambda i: b[i][1]-b[i][0])
        cut = sum(b[j])/2
        left_box, right_box = children(b, j, cut)
        left = visit(left_box, depth+1)
        if left.status != 'PROVED':
            return left
        right = visit(right_box, depth+1)
        if right.status != 'PROVED':
            return right
        return Result('PROVED', Split(j, cut, left.tree, right.tree), None, nodes)
    return visit(box, 0)


def replay(p: Poly, box: Box, tree: Tree, *, strict: bool = False,
           max_nodes: int = 100000, max_depth: int = 100) -> bool:
    """The polynomial and entire root box are external, not certificate-owned."""
    remaining = max_nodes
    def visit(b: Box, t: Tree, depth: int) -> bool:
        nonlocal remaining
        remaining -= 1
        if remaining < 0 or depth > max_depth:
            return False
        if isinstance(t, Leaf):
            ds = p.degrees
            if len(t.coefficients) != prod(d+1 for d in ds):
                return False
            if any(not isinstance(c, Q) or (c <= 0 if strict else c < 0)
                   for c in t.coefficients):
                return False
            ts = tuple(Poly.var(p.n, j) for j in range(p.n))
            expanded = Poly.const(p.n, 0)
            for i, c in zip(product(*(range(d+1) for d in ds)), t.coefficients):
                basis = Poly.const(p.n, c)
                for x, d, k in zip(ts, ds, i):
                    basis *= comb(d,k)*x**k*(1-x)**(d-k)
                expanded += basis
            return expanded == unit_transform(p, b)
        if isinstance(t, Split):
            lb, rb = children(b, t.axis, t.cut)
            return visit(lb, t.left, depth+1) and visit(rb, t.right, depth+1)
        return False
    try:
        unit_transform(p, box)
        return visit(box, tree, 0)
    except (ValueError, TypeError, AttributeError, RecursionError):
        return False


def check_witness(p: Poly, box: Box, point: tuple[Q, ...], *, strict: bool=False) -> bool:
    try:
        unit_transform(p, box)
        if len(point) != p.n or not all(isinstance(x,Q) and l <= x <= u
                                        for x,(l,u) in zip(point, box)):
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
    if isinstance(t, Leaf):
        return 1, 1
    a,b = size(t.left), size(t.right)
    return 1+a[0]+b[0], a[1]+b[1]
