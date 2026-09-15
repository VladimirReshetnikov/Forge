"""Exact reachable-space search for rational weighted representations."""
from __future__ import annotations
from collections import deque
import sympy as s
from .encode import vector,matrix

def encode_problem(alpha,matrices,beta):
    return {'kind':'weighted_problem_v1','dimension':alpha.cols,
            'alphabet':list(matrices),'alpha':vector(list(alpha)),
            'beta':vector(list(beta)), 'matrices':{a:matrix(m) for a,m in matrices.items()}}

def difference(a,b):
    al,ml,bl=a; ar,mr,br=b
    if set(ml)!=set(mr):
        raise ValueError('alphabet mismatch')
    return al.row_join(ar), {a:s.diag(ml[a],mr[a]) for a in ml}, bl.col_join(-br)

def coordinates(rows,v):
    if not rows:
        return [] if v == s.zeros(1,v.cols) else None
    b=s.Matrix.vstack(*rows)
    try:
        sol,params=b.T.gauss_jordan_solve(v.T)
    except ValueError:
        return None
    if params.rows:
        raise AssertionError('search basis unexpectedly dependent')
    return list(sol)

def discover(alpha,matrices,beta,max_vectors=10000):
    n=alpha.cols
    problem=encode_problem(alpha,matrices,beta)
    queue=deque([(alpha,[])])
    rows=[]; words=[]; examined=0
    while queue:
        v,w=queue.popleft(); examined+=1
        if examined>max_vectors:
            return None,{'reason':'vector_budget','examined':examined}
        if (v*beta)[0] != 0:
            return (problem,{'kind':'distinguishing_word_v1','word':w}), {'examined':examined,'word_length':len(w),'basis_rows':len(rows)}
        if coordinates(rows,v) is not None:
            continue
        rows.append(v); words.append(w)
        for a,m in matrices.items():
            queue.append((v*m,w+[a]))
    r=len(rows)
    cert={'kind':'weighted_closure_v1','rank':r,
          'basis':matrix(s.Matrix.vstack(*rows)) if rows else [],
          'initial_coordinates':vector(coordinates(rows,alpha)),
          'closure':{a:[vector(coordinates(rows,v*m)) for v in rows] for a,m in matrices.items()}}
    return (problem,cert),{'examined':examined,'basis_rows':r,'ambient_dimension':n,'basis_words':words}

def subsequence_identity():
    # Left state: [1, #a, #b, #ab, #ba], row-vector convention.
    ma=s.eye(5); ma[0,1]=1; ma[2,4]=1
    mb=s.eye(5); mb[0,2]=1; mb[1,3]=1
    left=(s.Matrix([[1,0,0,0,0]]),{'a':ma,'b':mb},s.Matrix([0,0,0,1,1]))
    inc=s.Matrix([[1,1],[0,1]]); ident=s.eye(2)
    right=(s.kronecker_product(s.Matrix([[1,0]]),s.Matrix([[1,0]])),
           {'a':s.kronecker_product(inc,ident),'b':s.kronecker_product(ident,inc)},
           s.kronecker_product(s.Matrix([0,1]),s.Matrix([0,1])))
    return difference(left,right)
