"""Exact adaptive Bernstein certificates with independent coefficient expansion.

A split tree certifies domain coverage. Refuting a box is deliberately absent:
search failure and a negative Bernstein coefficient both mean UNKNOWN.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from polynomial import Poly, bernstein_coefficients, expand_bernstein

Box = tuple[tuple[Q,Q],...]

@dataclass(frozen=True)
class Leaf:
    degrees: tuple[int,...]
    coefficients: tuple[Q,...]

@dataclass(frozen=True)
class Split:
    axis: int
    cut: Q
    left: 'Tree'
    right: 'Tree'

Tree = Leaf | Split


def bisect(box: Box, axis: int, cut: Q) -> tuple[Box, Box]:
    if type(axis) is not int or not 0 <= axis < len(box):
        raise ValueError('Invalid split axis')
    l,u = box[axis]
    if not isinstance(cut,Q) or not l < cut < u:
        raise ValueError('Cut must be a rational interior point')
    a,b = list(box),list(box)
    a[axis],b[axis] = (l,cut),(cut,u)
    return tuple(a),tuple(b)


def check_tree(p: Poly, box: Box, tree: Tree, *, strict: bool = False,
               node_limit: int = 100000) -> bool:
    """No search, no float, no shared conversion formula with the producer."""
    try:
        p.affine_box(box)  # validates dimensions and positive widths
        todo = [(box,tree)]
        visited = 0
        while todo:
            b,t = todo.pop()
            visited += 1
            if visited > node_limit:
                return False
            if isinstance(t,Leaf):
                if (len(t.degrees) != p.n or any(type(d) is not int or d<0 or d>64 for d in t.degrees)
                    or not t.coefficients or any(not isinstance(c,Q) for c in t.coefficients)):
                    return False
                if any(c <= 0 if strict else c < 0 for c in t.coefficients):
                    return False
                # Also cap tensor size before expanding adversarial certificates.
                size = 1
                for d in t.degrees: size *= d+1
                if size > 100000 or size != len(t.coefficients): return False
                if expand_bernstein(p.n,t.degrees,t.coefficients) != p.affine_box(b):
                    return False
            elif isinstance(t,Split):
                a,c = bisect(b,t.axis,t.cut)
                todo.extend(((a,t.left),(c,t.right)))
            else:
                return False
        return True
    except (ValueError,TypeError,IndexError,AttributeError,RecursionError):
        return False


def certify(p: Poly, box: Box, *, max_depth: int = 12, max_nodes: int = 8191,
            strict: bool = False) -> tuple[Tree|None,dict]:
    stats = {'nodes':0,'leaves':0,'max_depth':0}
    def go(b: Box, depth: int) -> Tree|None:
        if stats['nodes'] >= max_nodes: return None
        stats['nodes'] += 1
        stats['max_depth'] = max(depth,stats['max_depth'])
        ds,cs = bernstein_coefficients(p,b)
        if all(c>0 if strict else c>=0 for c in cs):
            stats['leaves'] += 1
            return Leaf(ds,cs)
        if depth >= max_depth: return None
        # Largest relative width: avoid coordinate-unit bias.
        axis = max(range(p.n),key=lambda i: ((b[i][1]-b[i][0])/(box[i][1]-box[i][0]),-i))
        cut = (b[axis][0]+b[axis][1])/2
        left,right = bisect(b,axis,cut)
        a = go(left,depth+1)
        if a is None: return None
        c = go(right,depth+1)
        if c is None: return None
        return Split(axis,cut,a,c)
    tree = go(box,0)
    stats['status'] = 'checked_python' if tree is not None and check_tree(p,box,tree,strict=strict) else 'unknown'
    return tree if stats['status']=='checked_python' else None,stats


def tree_json(t: Tree) -> dict:
    if isinstance(t,Leaf):
        return {'leaf':{'degrees':list(t.degrees),'coefficients':[str(c) for c in t.coefficients]}}
    return {'split':{'axis':t.axis,'cut':str(t.cut),'left':tree_json(t.left),'right':tree_json(t.right)}}
