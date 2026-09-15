"""Bounded exact linear search, not a general creative-telescoping algorithm."""
import math
from fractions import Fraction as Q
import sympy as s
from .exact import encpoly, encq
n,k=s.symbols('n k')

def poly(expr):
    return {m:Q(int(c.p),int(c.q)) for m,c in s.Poly(s.expand(expr),n,k).terms() if c}

def primitive(vec):
    den=math.lcm(*(int(x.q) for x in vec))
    ints=[int(x*den) for x in vec]
    g=math.gcd(*ints)
    return [s.Integer(x//g) for x in ints]

def attempt(power,weight,order,operator_degree,flux_degree):
    """A fixed ansatz, returning UNKNOWN (None) rather than a negative theorem."""
    q=s.Rational(Q(weight).numerator,Q(weight).denominator)
    r=order; p=power; cols=[]; tags=[]
    rn=[s.prod(n+h for h in range(1,i+1))**p *
        s.prod(n+h-k for h in range(i+1,r+1))**p for i in range(r+1)]
    for i in range(r+1):
        for a in range(operator_degree+1):
            cols.append(s.Poly(n**a*rn[i],n,k)); tags.append(('a',i,a,0))
    for j in range(r):
        rm=k**p*s.prod(n+h for h in range(1,j+1))**p*s.prod(n+h-k for h in range(j+2,r+1))**p
        for a in range(flux_degree+1):
            for b in range(flux_degree+1-a):
                cols.append(s.Poly(-q*n**a*(k+1)**b*rn[j]+n**a*k**b*rm,n,k))
                tags.append(('P',j,a,b))
    mons=sorted(set().union(*(set(c.monoms()) for c in cols)))
    ds=[c.as_dict() for c in cols]
    rows=[[d.get(m,0) for d in ds] for m in mons]
    def choose_tail(j,t):
        degree=j-t
        if degree<0: return s.Integer(0)
        return s.Rational(1,math.factorial(degree))*s.prod(n+j-h for h in range(degree))
    # Include every boundary equation in the linear search as well as replay.
    # Filtering only individual interior-nullspace basis vectors could miss a
    # linear combination satisfying the boundary constraints.
    boundary_rows=0
    for t in range(1,r+1):
        bcols=[]
        for typ,j,a,b in tags:
            if typ=='a': expr=n**a*choose_tail(j,t)**p
            else:
                expr=(-q*n**a*(n+t+1)**b*choose_tail(j,t)**p
                      +n**a*(n+t)**b*choose_tail(j,t-1)**p)
            bcols.append(s.Poly(expr,n))
        powers=sorted(set(e[0] for col in bcols for e,c in col.terms() if c))
        rows.extend([[col.nth(e) for col in bcols] for e in powers])
        boundary_rows+=len(powers)
    matrix=s.Matrix(rows)
    if not all(x.is_Rational for x in matrix): raise TypeError("search matrix must be exact rational")
    nullspace=matrix.nullspace()
    stats={'order':r,'operator_degree':operator_degree,'flux_degree':flux_degree,
           'rows':matrix.rows,'boundary_rows':boundary_rows,'columns':matrix.cols,'nullity':len(nullspace)}
    # The independent boundary checker remains mandatory after exact search.
    from .check import telescoper
    for vec in nullspace:
        aa=[s.expand(sum(x*n**a for x,t in zip(vec,tags) for typ,j,a,b in [t]
                            if typ=='a' and j==i)) for i in range(r+1)]
        if aa[-1]==0: continue
        vv=primitive(list(vec))
        aa=[s.expand(sum(x*n**a for x,t in zip(vv,tags) for typ,j,a,b in [t]
                            if typ=='a' and j==i)) for i in range(r+1)]
        if s.Poly(aa[-1],n).LC()<0: vv=[-x for x in vv]; aa=[-a for a in aa]
        ps=[s.expand(sum(x*n**a*k**b for x,t in zip(vv,tags) for typ,h,a,b in [t]
                            if typ=='P' and h==j)) for j in range(r)]
        problem={'kind':'binomial-power-sum','power':p,'weight':encq(Q(weight))}
        cert={'kind':'shifted-binomial-telescoper','operator':[encpoly(poly(a)) for a in aa],
              'flux':[encpoly(poly(a)) for a in ps]}
        if telescoper(problem,cert): return cert,stats
    return None,stats
