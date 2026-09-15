"""Exact rational PSD decomposition of a global quadratic polynomial.

For z=(1,x_1,...,x_n), form p=z^T H z. Symmetric diagonal pivoting
writes H as a sum v v^T / pivot. Accepted answers are replayed by the
same general cone checker; a failed pivot is UNKNOWN in this API.
This path uses neither floating point nor an external optimization library.
"""
from __future__ import annotations
from fractions import Fraction as Q
from polynomial import Poly
from cone import Atom, ConeCertificate, check_cone


def solve_quadratic(p: Poly) -> tuple[ConeCertificate|None,dict]:
    if p.degree()>2:
        return None,{'status':'unsupported_degree'}
    size=p.n+1
    H=[[Q(0) for _ in range(size)] for _ in range(size)]
    for m,c in p.terms:
        ix=[i+1 for i,e in enumerate(m) for _ in range(e)]
        if not ix: H[0][0]+=c
        elif len(ix)==1:
            i=ix[0];H[0][i]+=c/2;H[i][0]+=c/2
        else:
            i,j=ix
            if i==j: H[i][i]+=c
            else: H[i][j]+=c/2;H[j][i]+=c/2
    z=[Poly.const(p.n,1)]+[Poly.var(p.n,i) for i in range(p.n)]
    out=[]
    while any(c for row in H for c in row):
        if any(H[i][i]<0 for i in range(size)):
            return None,{'status':'unknown_non_psd','pivots':len(out)}
        k=next((i for i in range(size) if H[i][i]>0),None)
        if k is None:
            return None,{'status':'unknown_non_psd','pivots':len(out)}
        d=H[k][k]
        v=H[k][:]
        s=sum((a*b for a,b in zip(v,z)),Poly.const(p.n,0))
        out.append((1/d,Atom(s)))
        H=[[H[i][j]-v[i]*v[j]/d for j in range(size)] for i in range(size)]
    c=ConeCertificate(tuple(out))
    if not check_cone(p,(),c):
        return None,{'status':'reconstruction_rejected'}
    return c,{'status':'checked_python','pivots':len(out),'certificate_terms':len(out)}
