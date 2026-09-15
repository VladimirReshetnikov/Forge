"""Certificate validators, deliberately separated from all discovery routines.

These validate exact algebraic identities / finite proof DAGs in Python. They
are not Lean's kernel and have not been formally verified. A Lean port must
prove each checker's semantic soundness and certify the reification map.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from .polynomial import Poly

@dataclass(frozen=True)
class ConeTerm:
    weight: Q
    square: Poly
    factors: tuple[int, ...] = ()

@dataclass(frozen=True)
class ConeCertificate:
    terms: tuple[ConeTerm, ...]
    ideal: tuple[Poly, ...] = ()


def check_cone(target: Poly, nonnegative: tuple[Poly, ...],
               equal_zero: tuple[Poly, ...], cert: ConeCertificate) -> bool:
    """Check target = sum w*q^2*prod(g_i) + sum h_j*e_j, w>=0.

The context's g_i>=0 and e_j=0 are assumptions, not asserted by this function.
They must be proved in the actual Lean scope before a certificate is replayed.
"""
    try:
        if len(cert.ideal) != len(equal_zero):
            return False
        if any(p.nvars != target.nvars for p in nonnegative + equal_zero):
            return False
        acc = Poly.constant(target.nvars,0)
        for term in cert.terms:
            if not isinstance(term.weight,Q) or term.weight < 0:
                return False
            p = term.weight * term.square**2
            for i in term.factors:
                if type(i) is not int or i < 0 or i >= len(nonnegative):
                    return False
                p *= nonnegative[i]
            acc += p
        for h,e in zip(cert.ideal,equal_zero):
            acc += h*e
        return acc == target
    except (ValueError, TypeError, IndexError, AttributeError):
        return False


@dataclass(frozen=True)
class InvariantCertificate:
    invariant: Poly
    initial: tuple[Q, ...]
    transition: tuple[Poly, ...]


def check_invariant(cert: InvariantCertificate) -> bool:
    """A conserved-polynomial certificate: I(s0)=0 and I(T(s))=I(s).

This is sufficient, not necessary, for an inductive equality invariant.
"""
    try:
        return (cert.invariant.eval(cert.initial) == 0 and
                cert.invariant.substitute(cert.transition) == cert.invariant)
    except (ValueError, TypeError, AttributeError):
        return False


@dataclass(frozen=True)
class BernsteinLeaf:
    box: tuple[tuple[Q,Q], ...]
    degrees: tuple[int, ...]
    coefficients: tuple[tuple[tuple[int, ...], Q], ...]

@dataclass(frozen=True)
class BernsteinSplit:
    box: tuple[tuple[Q,Q], ...]
    axis: int
    cut: Q
    left: 'BernsteinTree'
    right: 'BernsteinTree'

BernsteinTree = BernsteinLeaf | BernsteinSplit


def check_bernstein(target: Poly, box: tuple[tuple[Q,Q], ...],
                    tree: BernsteinTree) -> bool:
    """Reconstruct every Bernstein identity, checking a full binary box cover.

Does NOT call the search-side power-to-Bernstein transformation.
"""
    from math import comb
    from itertools import product
    try:
        if len(box) != target.nvars or any(a>=b for a,b in box) or tree.box != box:
            return False
        if isinstance(tree, BernsteinSplit):
            i,cut = tree.axis,tree.cut
            if type(i) is not int or not 0<=i<len(box) or not box[i][0]<cut<box[i][1]:
                return False
            left = list(box); right = list(box)
            left[i]=(box[i][0],cut); right[i]=(cut,box[i][1])
            return check_bernstein(target,tuple(left),tree.left) and check_bernstein(target,tuple(right),tree.right)
        if not isinstance(tree,BernsteinLeaf) or len(tree.degrees)!=target.nvars:
            return False
        if any(type(d) is not int or d<0 for d in tree.degrees):
            return False
        expected = list(product(*(range(d+1) for d in tree.degrees)))
        if [k for k,_ in tree.coefficients] != expected:
            return False
        if any(not isinstance(c,Q) or c<0 for _,c in tree.coefficients):
            return False
        vs=[Poly.variable(target.nvars,i) for i in range(target.nvars)]
        acc=Poly.constant(target.nvars,0)
        # Work directly in original x coordinates, unlike discovery in t coordinates.
        for idx,c in tree.coefficients:
            term=Poly.constant(target.nvars,c)
            for i,(k,d) in enumerate(zip(idx,tree.degrees)):
                a,b=box[i]; w=b-a
                term *= comb(d,k) * (vs[i]-a)**k * (b-vs[i])**(d-k) * (Q(1)/w**d)
            acc += term
        return acc==target
    except (ValueError, TypeError, AttributeError, IndexError, ZeroDivisionError):
        return False
