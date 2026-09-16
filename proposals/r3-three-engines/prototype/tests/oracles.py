"""Small independent oracles, intentionally not used by acceptance checkers."""
from fractions import Fraction as F
from itertools import combinations

def linear_solution(matrix,rhs):
    n=len(rhs); a=[list(row)+[b] for row,b in zip(matrix,rhs)]
    for j in range(n):
        pivot=next((i for i in range(j,n) if a[i][j]),None)
        if pivot is None: return None
        a[j],a[pivot]=a[pivot],a[j]
        d=a[j][j]; a[j]=[v/d for v in a[j]]
        for i in range(n):
            if i!=j:
                d=a[i][j]; a[i]=[v-d*w for v,w in zip(a[i],a[j])]
    return [row[-1] for row in a]

def bounded_feasible(rows,n):
    """Vertex enumeration with a common strict slack in [0,1].

Call only when rows bound all original variables. The augmented polyhedron
is then compact, so any feasible strict slack attains its maximum at a vertex.
"""
    constraints=[]
    for r in rows:
        a=[F(v) for v in r['a']]
        constraints.append(a[:-1]+[F(-int(r['strict'])),a[-1]])
    constraints += [[F(0)]*n+[F(1),F(0)], [F(0)]*n+[F(-1),F(1)]]
    d=n+1; strict=any(r['strict'] for r in rows)
    for ix in combinations(range(len(constraints)),d):
        selected=[constraints[i] for i in ix]
        x=linear_solution([r[:-1] for r in selected],[-r[-1] for r in selected])
        if x is not None and all(sum((a*b for a,b in zip(r[:-1],x)),r[-1])>=0 for r in constraints):
            if not strict or x[-1]>0: return True
    return False

def weyl_action(word,degree):
    """Act on x^degree, rightmost operator first, without truncation."""
    c=1
    for letter in reversed(word):
        if letter==0: degree+=1
        else:
            c*=degree
            if not c: return 0,0
            degree-=1
    return c,degree

def weyl_zero(poly,degree):
    values={}
    for w,c in poly.items():
        k,d=weyl_action(w,degree)
        values[d]=values.get(d,F(0))+c*k
    return all(v==0 for v in values.values())
