"""Exact certificate checking. Search oracles live in search.py.

All positivity claims here have real semantics and exact rational coefficients.
Tests exercise this code, but it is NOT formally verified in Lean.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
from math import comb, prod
from typing import Sequence
from .poly import Poly

@dataclass(frozen=True)
class ConeTerm:
    weight: Q
    square: Poly
    powers: tuple[int, ...]

@dataclass(frozen=True)
class ConeCertificate:
    terms: tuple[ConeTerm, ...]
    equality_multipliers: tuple[Poly, ...] = ()


def check_cone(target: Poly, inequalities: Sequence[Poly], equalities: Sequence[Poly],
               cert: ConeCertificate) -> bool:
    """Check target = sum c*q^2*prod(g_i^a_i) + sum r_j*h_j.

    Semantics: if every g_i >= 0 and every h_j = 0, target >= 0.
    The original goal/hypotheses, not certificate metadata, supply the polynomials.
    """
    if not isinstance(cert, ConeCertificate):
        return False
    try:
        if any(p.n != target.n for p in [*inequalities,*equalities]):
            return False
        if len(cert.equality_multipliers) != len(equalities):
            return False
        total = Poly.const(target.n, 0)
        for term in cert.terms:
            if not isinstance(term.weight, Q) or term.weight < 0:
                return False
            if term.square.n != target.n or len(term.powers) != len(inequalities):
                return False
            if any(type(k) is not int or k < 0 for k in term.powers):
                return False
            p = term.weight * term.square**2
            for g,k in zip(inequalities,term.powers):
                p *= g**k
            total += p
        for h,r in zip(equalities,cert.equality_multipliers):
            total += h*r
        return total == target
    except (ValueError, TypeError, AttributeError):
        return False

Box = tuple[tuple[Q,Q], ...]

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
    """Tensor-product Bernstein coefficients after exact affine box substitution."""
    if len(box) != p.n or any(not (isinstance(l,Q) and isinstance(u,Q) and l < u) for l,u in box):
        raise ValueError('nondegenerate rational box required')
    variables = [Poly.var(p.n,i) for i in range(p.n)]
    q = p.substitute([l+(u-l)*x for x,(l,u) in zip(variables,box)])
    degrees = [max((e[i] for e,_ in q.terms),default=0) for i in range(p.n)]
    if prod(d+1 for d in degrees) > max_coefficients:
        raise ValueError('Bernstein tensor size limit')
    coefficients = {}
    for beta in product(*(range(d+1) for d in degrees)):
        value = Q(0)
        for alpha,c in q.terms:
            if all(a <= b for a,b in zip(alpha,beta)):
                for a,b,d in zip(alpha,beta,degrees):
                    c *= Q(comb(b,a),comb(d,a))
                value += c
        coefficients[beta] = value
    return coefficients


def split_box(box: Box, axis: int, point: Q) -> tuple[Box,Box]:
    if type(axis) is not int or not 0 <= axis < len(box) or not isinstance(point,Q):
        raise ValueError('invalid split')
    l,u = box[axis]
    if not l < point < u:
        raise ValueError('split must lie strictly inside the interval')
    left,right = list(box),list(box)
    left[axis],right[axis] = (l,point),(point,u)
    return tuple(left),tuple(right)


def check_bernstein(p: Poly, box: Box, tree: BernsteinTree,
                    max_nodes: int = 100_000) -> bool:
    """Check every leaf and complete domain coverage, not just selected boxes."""
    stack = [(box,tree)]
    nodes = 0
    try:
        while stack:
            domain,node = stack.pop()
            nodes += 1
            if nodes > max_nodes:
                return False
            if isinstance(node,BernsteinLeaf):
                if not isinstance(node.lower_bound,Q) or node.lower_bound < 0:
                    return False
                if min(bernstein_coefficients(p,domain).values()) < node.lower_bound:
                    return False
            elif isinstance(node,BernsteinSplit):
                left,right = split_box(domain,node.axis,node.point)
                stack.extend([(left,node.left),(right,node.right)])
            else:
                return False
        return True
    except (ValueError,TypeError,AttributeError):
        return False


def tree_size(tree: BernsteinTree) -> tuple[int,int]:
    """(leaf count, maximum split depth)."""
    if isinstance(tree,BernsteinLeaf):
        return 1,0
    a,d = tree_size(tree.left)
    b,e = tree_size(tree.right)
    return a+b,1+max(d,e)


def tree_json(tree: BernsteinTree) -> dict:
    if isinstance(tree,BernsteinLeaf):
        return {'leaf':str(tree.lower_bound)}
    return {'axis':tree.axis,'point':str(tree.point),
            'left':tree_json(tree.left),'right':tree_json(tree.right)}


def cone_json(cert: ConeCertificate) -> dict:
    return {'terms':[{'weight':str(t.weight),'square':t.square.json(),
                      'powers':list(t.powers)} for t in cert.terms],
            'equality_multipliers':[p.json() for p in cert.equality_multipliers]}
