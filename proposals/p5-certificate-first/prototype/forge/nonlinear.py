"""Untrusted cone discovery using LP; exact certificate checking is mandatory."""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import combinations_with_replacement
from math import isfinite, isqrt
from time import perf_counter
import numpy as np
import sympy as sp
from scipy.optimize import linprog
from .polynomial import Poly, monomials
from .checkers import ConeTerm, ConeCertificate, check_cone

@dataclass
class ConeResult:
    status: str  # proved / unknown; never use LP infeasibility as a counterexample
    certificate: ConeCertificate | None
    generators: int
    seconds: float
    reason: str = ''


def discover(target: Poly, nonnegative: tuple[Poly,...]=(),
             equal_zero: tuple[Poly,...]=(), *, degree: int=4,
             square_bases: tuple[Poly,...]=(), max_generators: int=4000) -> ConeResult:
    start=perf_counter(); n=target.nvars
    if degree < 0 or max_generators < 1:
        raise ValueError('invalid search budget')
    if target.degree > degree:
        return ConeResult('unknown',None,0,perf_counter()-start,'target exceeds degree cap')
    if any(p.nvars!=n for p in nonnegative+equal_zero+square_bases):
        raise ValueError('dimension mismatch')
    # Monomial squares plus optional affine/polynomial squares. This is a finite
    # cone, NOT a complete SOS search or a general semidefinite program.
    bases=[Poly.make(n,[(m,1)]) for m in monomials(n,degree//2)]
    bases=list(dict.fromkeys(bases+list(goal_square_bases(target))+list(square_bases)))
    products=[((),Poly.constant(n,1))]
    # Repeated factors allowed. Constant constraints are omitted from products:
    # zero adds nothing, positive can be absorbed by weights, negative is itself
    # retained as a linear generator so contradictions remain possible.
    for k in range(1,degree+1):
        for inds in combinations_with_replacement(range(len(nonnegative)),k):
            if any(nonnegative[i].degree<=0 for i in inds) and k>1:
                continue
            p=Poly.constant(n,1)
            for i in inds:
                p *= nonnegative[i]
            if p.terms and p.degree<=degree:
                products.append((inds,p))
            if len(products)>max_generators:
                return ConeResult('unknown',None,len(products),perf_counter()-start,'product budget')
    columns=[]; descriptors=[]; seen=set()
    for q in bases:
        for inds,p in products:
            col=q*q*p
            if not col.terms or col.degree>degree or col in seen:
                continue
            seen.add(col); columns.append(col); descriptors.append((q,inds))
            if len(columns)>max_generators:
                return ConeResult('unknown',None,len(columns),perf_counter()-start,'generator budget')
    cone_count=len(columns)
    ideal_desc=[]
    for j,e in enumerate(equal_zero):
        if not e.terms:
            continue
        for m in monomials(n,degree-e.degree):
            q=Poly.make(n,[(m,1)])
            columns.append(q*e); ideal_desc.append((j,q))
    if len(columns)>max_generators:
        return ConeResult('unknown',None,len(columns),perf_counter()-start,'ideal budget')
    if not columns:
        return ConeResult('unknown',None,0,perf_counter()-start,'empty basis')
    rows=sorted(set(m for p in columns+[target] for m,_ in p.terms))
    ds=[dict(p.terms) for p in columns]; td=dict(target.terms)
    exact=[[d.get(m,Q(0)) for d in ds] for m in rows]
    rhs=[td.get(m,Q(0)) for m in rows]
    A=np.array(exact,dtype=float); b=np.array(rhs,dtype=float)
    if not np.isfinite(A).all() or not np.isfinite(b).all():
        return ConeResult('unknown',None,len(columns),perf_counter()-start,'floating overflow')
    opt=linprog(np.r_[np.ones(cone_count),np.zeros(len(ideal_desc))], A_eq=A,b_eq=b,
                bounds=[(0,None)]*cone_count+[(None,None)]*len(ideal_desc),method='highs',
                options={'time_limit':10.0})
    if not opt.success or opt.x is None:
        return ConeResult('unknown',None,len(columns),perf_counter()-start,'LP found no candidate')
    # Floating weights are proposals only. Exact rational reconstruction followed
    # by a separate identity/sign check is the sole acceptance criterion.
    weights=[Q(float(v)).limit_denominator(10**7) for v in opt.x]
    def package(ws):
        terms=tuple(ConeTerm(ws[i],q,inds) for i,(q,inds) in enumerate(descriptors) if ws[i])
        hs=[Poly.constant(n,0) for _ in equal_zero]
        for i,(j,q) in enumerate(ideal_desc,cone_count):
            hs[j]+=ws[i]*q
        return ConeCertificate(terms,tuple(hs))
    cert=package(weights)
    if not check_cone(target,nonnegative,equal_zero,cert):
        # Solve the support exactly. This can fail or choose negative coefficients;
        # that is an unknown result, never a relaxed acceptance test.
        support=[i for i,v in enumerate(opt.x) if abs(v)>1e-9]
        try:
            mat=sp.Matrix([[sp.Rational(exact[r][i].numerator,exact[r][i].denominator)
                            for i in support] for r in range(len(rows))])
            vec=sp.Matrix([sp.Rational(v.numerator,v.denominator) for v in rhs])
            sol,params=mat.gauss_jordan_solve(vec)
            sol=sol.subs({p:0 for p in params})
            weights=[Q(0)]*len(columns)
            for i,v in zip(support,sol):
                weights[i]=Q(int(v.p),int(v.q))
            cert=package(weights)
        except (ValueError,TypeError,AttributeError):
            return ConeResult('unknown',None,len(columns),perf_counter()-start,'exact reconstruction failed')
    if not check_cone(target,nonnegative,equal_zero,cert):
        return ConeResult('unknown',None,len(columns),perf_counter()-start,'certificate rejected')
    return ConeResult('proved',cert,len(columns),perf_counter()-start)


def goal_square_bases(target: Poly, limit: int=200) -> tuple[Poly,...]:
    """Heuristic binomial-square roots inferred from positive even monomials.

    For a*m^2+b*n^2, try m +/- r*n when r^2=b/a is rational-square.
    Also try unit sums/differences and cross-coefficient completing squares.
    A finite dictionary, not complete SOS.
    """
    roots=[]
    for mon,c in target.terms:
        if c>0 and all(e%2==0 for e in mon):
            roots.append((Poly.make(target.nvars,[(tuple(e//2 for e in mon),1)]),c))
    out=[]
    coeffs=dict(target.terms)
    for i,(p,a) in enumerate(roots):
        for q,b in roots[i+1:]:
            ratios=[Q(1)]
            r=b/a; sn,sd=isqrt(r.numerator),isqrt(r.denominator)
            if sn*sn==r.numerator and sd*sd==r.denominator:
                ratios.append(Q(sn,sd))
            # A positive residual constant can hide the square-root ratio.
            # Complete each oriented pair using its cross coefficient instead.
            cross_mon=tuple(u+v for u,v in zip(p.terms[0][0],q.terms[0][0]))
            cross=coeffs.get(cross_mon,Q(0))
            if cross:
                out.extend([p+(cross/(2*a))*q,q+(cross/(2*b))*p])
            for ratio in ratios:
                out.extend([p+ratio*q,p-ratio*q])
                if len(out)>=limit: return tuple(dict.fromkeys(out[:limit]))
    return tuple(dict.fromkeys(out))
