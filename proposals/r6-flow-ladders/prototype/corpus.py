"""Deterministic mathematical fixtures. Counts are not Lean benchmarks."""
from fractions import Fraction as F
from math import factorial,comb
from forge_flow.model import ExpPoly as E

RATES=(F(1,3),F(1),F(3,2),F(2))

def scaled_argument(f,r):
    return E.make({s*r:[a*r**j for j,a in enumerate(p)] for s,p in f.terms})

def positives():
    cases=[]
    for r in RATES:
        for n in range(16):
            p=[r**j/F(factorial(j)) for j in range(n+1)]
            cases.append((f'exp_taylor_r{r}_n{n}',E.make({r:[1],0:[-a for a in p]})))
            p=[(-r)**j/F(factorial(j)) for j in range(n+1)]
            f=E.make({-r:[1],0:[-a for a in p]}).scale((-1)**(n+1))
            cases.append((f'exp_alternating_r{r}_n{n}',f))
        for n in range(1,13):
            p=[F(comb(n,j))*(r/n)**j for j in range(n+1)]
            cases.append((f'exp_binomial_r{r}_n{n}',E.make({r:[1],0:[-a for a in p]})))
    S=E.make({1:[F(1,2)],-1:[F(-1,2)]});C=E.make({1:[F(1,2)],-1:[F(1,2)]})
    X=E.make({0:[0,1]});one=E.make({0:[1]})
    special={
        'hyperbolic_cusa':X*(C+one.scale(2))-S.scale(3),
        'hyperbolic_wilker':S*S*C+X*S-(X*X*C).scale(2),
        'hyperbolic_lazarevic':S*S*S-X*X*X*C,
        'exp_symmetric':E.make({2:[1],1:[-2,0,-1],0:[1]}),
        'exp_pade':E.make({1:[-2,1],0:[2,1]})}
    for name,f in special.items():
        for r in RATES: cases.append((f'{name}_r{r}',scaled_argument(f,r)))
    return cases

def systems():
    out=[]
    for r in RATES:
        for n in range(10):
            odd=[F(0)]*(2*n+2);even=[F(0)]*(2*n+1)
            for j in range(1,len(odd),2): odd[j]=-r**j/F(factorial(j))
            for j in range(0,len(even),2): even[j]=-r**j/F(factorial(j))
            H=[E.make({r:[F(1,2)],-r:[F(-1,2)],0:odd}),
               E.make({r:[F(1,2)],-r:[F(1,2)],0:even})]
            out.append((f'coupled_r{r}_n{n}',r,H))
    return out

def false_cases():
    out=[]
    for r in RATES:
        for c in (F(3,2),F(2),F(3)):
            out.append((f'false_tangent_r{r}_c{c}',E.make({r:[1],0:[-1,-c*r]})))
        for n in range(1,9):
            out.append((f'false_taylor_r{r}_n{n}',E.make({r:[-1],0:[r**j/F(factorial(j)) for j in range(n+1)]})))
    return out

def true_outside():
    return [(f'outside_q{q}_e{e}',E.make({2:[1],1:[-2*q],0:[q*q+e]}))
            for q in (F(3,2),F(2),F(3),F(4)) for e in (F(0),F(1,10000))]

def roots():
    specs=[(F(1,8),F(0),F(1,4)),(F(1,4),F(0),F(1,2)),
           (F(1,2),F(1,4),F(1,2)),(F(1),F(1,2),F(3,5)),
           (F(2),F(3,4),F(1)),(F(3),F(1),F(5,4)),
           (F(4),F(1),F(3,2)),(F(8),F(3,2),F(2))]
    out=[(f'lambert_{q}',E.make({1:[0,1],0:[-q]}),a,b) for q,a,b in specs]
    for q,a,b in [(2,0,1),(3,1,F(3,2)),(5,F(3,2),2),(10,2,F(5,2))]:
        out.append((f'exp_equals_{q}',E.make({1:[1],0:[-q]}),F(a),F(b)))
    out.extend([
        ('exp_3x_left',E.make({1:[1],0:[0,-3]}),F(1,2),F(1)),
        ('exp_3x_right',E.make({1:[1],0:[0,-3]}),F(3,2),F(2)),
        ('exp_2x_plus_1',E.make({1:[1],0:[-1,-2]}),F(1),F(3,2)),
        ('exp_negative_equals_x',E.make({-1:[1],0:[0,-1]}),F(1,2),F(3,5))])
    return out
