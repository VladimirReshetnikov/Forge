"""Greatest bounded-degree pullback-stable invariant subspace.

Handles exact polynomial transitions and polynomially parameterized initial
states. Guards are deliberately ignored: all transitions may occur in any order.
This is an under-approximation of all polynomial invariants, NOT a general
ideal-invariant algorithm. High-degree pullback coefficients are never dropped.
"""
from __future__ import annotations
from dataclasses import dataclass
from exact import (Q, Poly, const, var, add, scale, mul, subst, monomials,
                   rref, nullspace, matmul, coordinates, vector, polynomial,
                   encode, encode_q, pretty)

@dataclass
class Problem:
    name: str
    n: int
    degree: int
    init_parameters: int
    init: list[Poly]
    transitions: list[list[Poly]]
    target: Poly

    def encoded(self):
        return dict(name=self.name, n=self.n, degree=self.degree,
                    init_parameters=self.init_parameters,
                    init=[encode(p) for p in self.init],
                    transitions=[[encode(p) for p in f] for f in self.transitions],
                    target=encode(self.target))


def stacked_coefficients(polys):
    """Columns correspond to polynomials. Includes EVERY occurring monomial."""
    keys=sorted(set().union(*(set(p) for p in polys))) if polys else []
    return [[p.get(m,Q(0)) for p in polys] for m in keys]


def discover(problem: Problem):
    n,d = problem.n,problem.degree
    mons=monomials(n,d)
    mon_ps=[{m:Q(1)} for m in mons]
    initial=[subst(p,problem.init,problem.init_parameters) for p in mon_ps]
    basis,_=rref(nullspace(stacked_coefficients(initial),len(mons)),len(mons))
    dimensions=[len(basis)]
    while basis:
        bps=[polynomial(row,mons) for row in basis]
        # For each pullback, compute its remainder modulo the current vector
        # space. Reduction applies to low-degree pivots but retains high terms.
        residual_blocks=[]
        piv=[next(i for i,x in enumerate(row) if x) for row in basis]
        for f in problem.transitions:
            remainders=[]
            for p in bps:
                rem=subst(p,f,n)
                for row,pivot,bp in zip(basis,piv,bps):
                    c=rem.get(mons[pivot],Q(0))
                    if c:
                        rem=add(rem,scale(-c,bp))
                remainders.append(rem)
            residual_blocks.extend(stacked_coefficients(remainders))
        coeffs=nullspace(residual_blocks,len(basis))
        new,_=rref(matmul(coeffs,basis),len(mons))
        if new==basis:
            break
        basis=new
        dimensions.append(len(basis))
    polys=[polynomial(row,mons) for row in basis]
    actions=[]
    for f in problem.transitions:
        matrix=[]
        for p in polys:
            image=subst(p,f,n)
            # Stable at the fixed point; vector() raises instead of truncating.
            c=coordinates(basis,vector(image,mons))
            assert c is not None
            matrix.append([encode_q(v) for v in c])
        actions.append(matrix)
    target_coeffs=None
    if set(problem.target).issubset(set(mons)):
        target_coeffs=coordinates(basis,vector(problem.target,mons))
    cert=dict(kind='pullback-space-v1',
              basis=[encode(p) for p in polys],
              actions=actions,
              target_coefficients=(None if target_coeffs is None else
                                   [encode_q(v) for v in target_coeffs]))
    return cert,dict(monomials=len(mons), dimensions=dimensions,
                     fixed_point_dimension=len(basis),
                     target_in_span=target_coeffs is not None,
                     basis_text=[pretty(p,[f'x{i}' for i in range(n)]) for p in polys])


def conserved_dimension(problem: Problem):
    """Ablation: impose p o F = p, plus the same initial condition."""
    mons=monomials(problem.n,problem.degree)
    ps=[{m:Q(1)} for m in mons]
    eqs=stacked_coefficients([subst(p,problem.init,problem.init_parameters) for p in ps])
    for f in problem.transitions:
        eqs += stacked_coefficients([add(subst(p,f,problem.n),scale(-1,p)) for p in ps])
    return len(nullspace(eqs,len(mons)))


def affine_dual_relations(problem: Problem):
    """Independent forward (reachable-feature-span) formulation for affine F.

    Returns a canonical row basis of all degree<=d polynomial relations.
    This routine does not call discover() or its preimage construction.
    """
    n=problem.n
    mons=monomials(n,problem.degree)
    ps=[{m:Q(1)} for m in mons]
    eval_init=[subst(p,problem.init,problem.init_parameters) for p in ps]
    span,_=rref(stacked_coefficients(eval_init),len(mons))
    # p_i(F(x)) = sum_j L_ij p_j(x); features are columns.
    lifts=[]
    for f in problem.transitions:
        if any(sum(m)>1 for p in f for m in p):
            raise ValueError('dual completeness test is affine-only')
        lifts.append([vector(subst(p,f,n),mons) for p in ps])
    while True:
        rows=list(span)
        for lift in lifts:
            for x in span:
                rows.append([sum(a*b for a,b in zip(row,x)) for row in lift])
        new,_=rref(rows,len(mons))
        if new==span:
            break
        span=new
    return rref(nullspace(span,len(mons)),len(mons))[0]


def coupled_example():
    x,y,z=[var(3,i) for i in range(3)]
    x2=mul(x,x)
    t=var(1,0)
    return Problem('coupled_nonconserved',3,2,1,[t,mul(t,t),scale(2,mul(t,t))],
        [[scale(2,x),add(scale(2,y),z),add(y,scale(3,z),x2)],
         [scale(-1,x),add(scale(2,x2),scale(-1,y)),add(y,z,scale(-1,x2))]],
         add(z,scale(-2,y)))
