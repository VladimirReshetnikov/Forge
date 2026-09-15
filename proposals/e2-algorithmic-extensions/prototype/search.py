"""Untrusted exact search. Uses SymPy, independently of checker.py.

No result from this module is a proof until replayed. Exhaustion is UNKNOWN
outside the explicitly fixed finite ansatz. Algorithms return serializable data.
"""
from __future__ import annotations
from itertools import product
from fractions import Fraction
import sympy as s


def enc(expr, xs):
    p = s.Poly(s.expand(expr), *xs, domain=s.QQ) if xs else None
    pairs = p.terms() if xs else [((), s.Rational(expr))]
    return [{'m': list(m), 'c': str(c)} for m,c in sorted(pairs) if c]

def monomials(xs, degree):
    exps = sorted((e for e in product(range(degree+1), repeat=len(xs)) if sum(e)<=degree), key=lambda e:(sum(e),e))
    return [s.prod(x**k for x,k in zip(xs,e)) for e in exps]

def coeffmatrix(exprs, xs):
    ps = [s.Poly(s.expand(e), *xs, domain=s.QQ) for e in exprs] if xs else None
    if not xs:
        return s.Matrix([[s.Rational(e) for e in exprs]])
    support = sorted({m for p in ps for m in p.monoms()})
    if not support:
        support = [(0,)*len(xs)]
    return s.Matrix([[p.coeff_monomial(m) for p in ps] for m in support])

def basiscols(M):
    cols = M.columnspace()
    return s.Matrix.hstack(*cols) if cols else s.zeros(M.rows,0)

def kernel(M):
    cols = M.nullspace()
    return s.Matrix.hstack(*cols) if cols else s.zeros(M.cols,0)

def substitute(e, xs, vals):
    return s.expand(e.subs(dict(zip(xs, vals)), simultaneous=True))

def solve_fixed(A,b):
    try:
        sol, params = A.gauss_jordan_solve(b)
    except ValueError:
        return None
    return sol.subs({z:0 for z in params})

def invariant(xs, params, initial, transitions, degree, target):
    features = monomials(xs, degree)
    N = len(features)
    if N > 256:
        raise ValueError('feature cap')
    C0 = coeffmatrix([substitute(e,xs,initial) for e in features], params)
    V = kernel(C0)
    dims = [V.cols]
    pulls = [[substitute(e,xs,t) for e in features] for t in transitions]
    # Include every pullback monomial, not just the original feature support.
    ambient = coeffmatrix(features + [e for group in pulls for e in group], xs)
    E = ambient[:,:N]
    Ps = [ambient[:,N*(i+1):N*(i+2)] for i in range(len(transitions))]
    for _ in range(N+1):
        k = V.cols
        if not k:
            break
        B = E*V
        # Columns of kernel(B.T) span all linear annihilators of span(B).
        annihilator = kernel(B.T).T
        constraints = s.Matrix.vstack(*[annihilator*P*V for P in Ps])
        W = V*kernel(constraints)
        W = basiscols(W)
        dims.append(W.cols)
        if W.cols == V.cols:
            V = W
            break
        V = W
    else:
        raise AssertionError('descending-chain dimension invariant violated')
    basis = [s.expand(sum(features[i]*V[i,j] for i in range(N))) for j in range(V.cols)]
    H = []
    for t in transitions:
        rows = []
        for b in basis:
            mat = coeffmatrix(basis + [substitute(b,xs,t)], xs)
            coeff = solve_fixed(mat[:,:len(basis)], mat[:,-1])
            if coeff is None:
                raise AssertionError('fixed point is not closed')
            rows.append([str(c) for c in coeff])
        H.append(rows)
    mat = coeffmatrix(basis+[target], xs)
    tc = solve_fixed(mat[:,:len(basis)],mat[:,-1])
    info = {'features':N,'dimensions':dims,'basis':[str(e) for e in basis],
            'target_in_span':tc is not None}
    if tc is None:
        return None, info
    p = {'kind':'invariant','arity':len(xs),'param_arity':len(params),
         'initial':[enc(e,params) for e in initial],
         'transitions':[[enc(e,xs) for e in t] for t in transitions],
         'target':enc(target,xs)}
    c = {'kind':'invariant','basis':[enc(e,xs) for e in basis],
         'matrices':H, 'target_coeffs':[str(q) for q in tc]}
    return (p,c),info

def gosper(A,B,k,denominators,max_degree=5):
    A,B = s.sympify(A),s.sympify(B)
    trials = 0
    for V in denominators:
        V = s.sympify(V)
        if s.expand(V)==0:
            continue
        for deg in range(max_degree+1):
            trials += 1
            coeffs = s.symbols('u:'+str(deg+1))
            U = sum(coeffs[i]*k**i for i in range(deg+1))
            residual = s.Poly(s.expand(A*U.subs(k,k+1)*V - B*U*V.subs(k,k+1) - B*V*V.subs(k,k+1)), k)
            M,b = s.linear_eq_to_matrix(residual.all_coeffs(),coeffs)
            sol = solve_fixed(M,b)
            if sol is not None:
                u = s.expand(U.subs(dict(zip(coeffs,sol))))
                p = {'kind':'gosper','A':enc(A,[k]),'B':enc(B,[k])}
                c = {'kind':'gosper','U':enc(u,[k]),'V':enc(V,[k])}
                return (p,c),{'trials':trials,'U':str(u),'V':str(V),'R':str(s.cancel(u/V))}
    return None, {'trials':trials,'status':'UNKNOWN'}

def binomial_square_telescoper():
    n,k = s.symbols('n k')
    An,Bn,Ak,Bk = (n+1)**2,(n-k+1)**2,(n-k)**2,(k+1)**2
    a,b,c,d,e,f = s.symbols('a b c d e f')
    c0,c1 = a*n+b,n+c
    U,V = k**2*(d*n+e*k+f),(n-k+1)**2
    residual = s.expand((c0*Bn+c1*An)*Bk*V*V.subs(k,k+1) - Bn*(Ak*U.subs(k,k+1)*V-Bk*U*V.subs(k,k+1)))
    M,rhs = s.linear_eq_to_matrix(s.Poly(residual,n,k).coeffs(),[a,b,c,d,e,f])
    sol = solve_fixed(M,rhs)
    if sol is None:
        return None
    inst = dict(zip([a,b,c,d,e,f],sol))
    c0,c1,U = [s.expand(p.subs(inst)) for p in [c0,c1,U]]
    problem = {'kind':'telescoper',**{key:enc(val,[n,k]) for key,val in zip(['An','Bn','Ak','Bk'],[An,Bn,Ak,Bk])}}
    cert = {'kind':'telescoper',**{key:enc(val,[n,k]) for key,val in zip(['c0','c1','U','V'],[c0,c1,U,V])}}
    return (problem,cert),{'unknowns':6,'coefficient_equations':M.rows,'c0':str(c0),'c1':str(c1),'U':str(U),'V':str(V),'rank':M.rank()}

# Separate noncommutative producer arithmetic; never imported by the checker.
def nc_clean(p):
    return {w:Fraction(c) for w,c in p.items() if c}

def nc_add(p,q):
    d=p.copy()
    for w,c in q.items(): d[w]=d.get(w,Fraction(0))+c
    return nc_clean(d)

def nc_scale(p,c): return nc_clean({w:v*c for w,v in p.items()})
def nc_mul(p,q):
    r={}
    for u,a in p.items():
        for v,b in q.items(): r[u+v]=r.get(u+v,Fraction(0))+a*b
    return nc_clean(r)
def nc_pow(p,n):
    r={():Fraction(1)}
    for _ in range(n): r=nc_mul(r,p)
    return r

def nc_enc(p): return [{'m':list(w),'c':str(c)} for w,c in sorted(p.items()) if c]

def two_sided(relations,target,alphabet,max_degree):
    """Sparse exact column elimination, recording a combination of input columns."""
    if not target:
        p={'kind':'two_sided','alphabet':alphabet,'relations':[nc_enc(r) for r in relations],'target':[]}
        return (p,{'kind':'two_sided','terms':[]}),{'columns':0,'rank':0,'terms':0,'degree_cap':max_degree}
    pivots={}
    contexts=[]
    stats={'columns':0,'rank':0,'degree_cap':max_degree}
    def reduce_col(vec,comb):
        vec=vec.copy(); comb=comb.copy()
        while vec:
            w=max(vec,key=lambda w:(len(w),w))
            if w not in pivots: return vec,comb,w
            base,rep=pivots[w]
            a=vec[w]
            for z,b in base.items():
                vec[z]=vec.get(z,Fraction(0))-a*b
                if not vec[z]: del vec[z]
            for i,b in rep.items():
                comb[i]=comb.get(i,Fraction(0))-a*b
                if not comb[i]: del comb[i]
        return vec,comb,None
    # All lower-degree contexts first; try target after each independent column.
    for budget in range(max_degree+1):
        for j,rel in enumerate(relations):
            rd=max(map(len,rel),default=0)
            extra=budget-rd
            if extra<0: continue
            for l in range(extra+1):
                for left in product(range(alphabet),repeat=l):
                    for right in product(range(alphabet),repeat=extra-l):
                        if len(contexts)>=15000:
                            return None,{**stats,'status':'UNKNOWN_COLUMN_CAP'}
                        idx=len(contexts); contexts.append((j,left,right))
                        stats['columns']+=1
                        col={left+w+right:c for w,c in rel.items()}
                        vec,comb,piv=reduce_col(col,{idx:Fraction(1)})
                        if piv is not None:
                            a=vec[piv]
                            pivots[piv]=({w:c/a for w,c in vec.items()},{i:c/a for i,c in comb.items()})
                            stats['rank']=len(pivots)
                            rem,neg,_=reduce_col(target,{})
                            if not rem:
                                terms=[]
                                for i,coef in sorted(neg.items()):
                                    r,u,v=contexts[i]
                                    terms.append({'relation':r,'left':list(u),'right':list(v),'coefficient':str(-coef)})
                                p={'kind':'two_sided','alphabet':alphabet,'relations':[nc_enc(r) for r in relations],'target':nc_enc(target)}
                                c={'kind':'two_sided','terms':terms}
                                stats['terms']=len(terms)
                                return (p,c),stats
    return None,{**stats,'status':'UNKNOWN'}

def conserved(xs,params,initial,transitions,degree,target):
    """Exact same-feature ablation restricted to p(T)=p."""
    features=monomials(xs,degree)
    rows=[coeffmatrix([substitute(e,xs,initial) for e in features],params)]
    for t in transitions:
        rows.append(coeffmatrix([substitute(e,xs,t)-e for e in features],xs))
    V=kernel(s.Matrix.vstack(*rows))
    bs=[s.expand(sum(features[i]*V[i,j] for i in range(len(features)))) for j in range(V.cols)]
    mat=coeffmatrix(bs+[target],xs)
    return solve_fixed(mat[:,:len(bs)],mat[:,-1]) is not None

def sympy_gosper_oracle(term,k):
    """Optional richer search adapter. Returns identities, not sequence proofs.

The tested SymPy gosper_term returns the rational multiplier of the summand.
The independent checker is authoritative about this convention.
"""
    from sympy.concrete.gosper import gosper_term
    ratio=s.hypersimp(term,k)
    if ratio is None:return None
    R=gosper_term(term,k)
    if R is None:return None
    A,B=s.fraction(s.cancel(ratio));U,V=s.fraction(s.cancel(R))
    if any(not e.is_polynomial(k) for e in [A,B,U,V]):return None
    return ({'kind':'gosper','A':enc(A,[k]),'B':enc(B,[k])},
            {'kind':'gosper','U':enc(U,[k]),'V':enc(V,[k])})
