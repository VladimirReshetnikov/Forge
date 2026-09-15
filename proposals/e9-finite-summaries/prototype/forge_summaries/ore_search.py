"""Small bounded common-left-multiple search and complete natural-root covers."""
import math
import sympy as s
from fractions import Fraction as Q
from .exact import *
from .telescoping_search import n,k,poly,primitive

def _expr(p): return s.sympify(sum(s.Rational(c.numerator,c.denominator)*n**i for (i,j),c in p.items()))

def common_left_multiple(a,b,multiplier_order,multiplier_degree):
    a=[_expr(x) for x in a]; b=[_expr(x) for x in b]
    tags=[]; cols=[]; out_order=multiplier_order+max(len(a),len(b))-1
    for side,op,sgn in [('u',a,1),('v',b,-1)]:
        for i in range(multiplier_order+1):
            for d in range(multiplier_degree+1):
                col=[s.Integer(0)]*(out_order+1)
                for j,aj in enumerate(op): col[i+j]=s.expand(sgn*n**d*aj.subs(n,n+i))
                cols.append(col); tags.append((side,i,d))
    positions=sorted(set((j,e[0]) for col in cols for j,c in enumerate(col)
                         for e,val in s.Poly(c,n).terms() if val))
    m=s.Matrix([[s.Poly(col[j],n).nth(d) for col in cols] for j,d in positions])
    for vv in m.nullspace():
        vv=primitive(vv)
        ops=[]
        for side in ['u','v']:
            op=[poly(sum(x*n**d for x,t in zip(vv,tags) for typ,j,d in [t]
                         if typ==side and j==i)) for i in range(multiplier_order+1)]
            while op and not op[-1]: op.pop()
            ops.append(op)
        if not all(ops): continue
        u,v=ops; l=ore_mul(u,[poly(x) for x in a])
        cert={'kind':'ore-multiple','common':[encpoly(x) for x in l],
              'left_multiplier':[encpoly(x) for x in u],'right_multiplier':[encpoly(x) for x in v]}
        return cert,{'rows':m.rows,'columns':m.cols,'multiplier_order':multiplier_order,'multiplier_degree':multiplier_degree}
    return None,{'rows':m.rows,'columns':m.cols,'multiplier_order':multiplier_order,'multiplier_degree':multiplier_degree}

def singularity_cover(operator):
    r=len(operator)-1; lead=operator[-1]; degree=max(i for i,j in lead)
    if degree==0: bound=0
    else:
        top=lead[(degree,0)]
        rho=1+max(abs(lead.get((i,0),0)/top) for i in range(degree))
        bound=math.ceil(rho)
    if bound>100000: return None
    roots=[i for i in range(bound+1) if evalp(lead,i)==0]
    return {'kind':'singularity-cover','bound':bound,'singular_indices':roots,
            'seed_indices':sorted(set(range(r))|{i+r for i in roots})}
