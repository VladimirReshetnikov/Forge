"""Untrusted searches using SymPy 1.14.0; no producer result is authoritative."""
from __future__ import annotations
from typing import Any
from sympy import Matrix, zeros, eye, ZZ
from sympy.polys.matrices import DomainMatrix
from sympy.polys.matrices.normalforms import smith_normal_decomp

class SearchLimit(RuntimeError):
    """A resource refusal means UNKNOWN, not a negative mathematical verdict."""

def pack(M: Matrix) -> dict[str,Any]:
    if any(x.is_Integer is not True for x in M):
        raise ValueError('non-integral matrix from producer')
    return dict(rows=M.rows,cols=M.cols,data=[int(x) for x in M])

def unpack(x: dict[str,Any]) -> Matrix:
    return Matrix(x['rows'],x['cols'],x['data'])

def smith(M: Matrix) -> tuple[dict[str,Any],dict[str,Any]]:
    if M.rows>256 or M.cols>256:
        raise SearchLimit('matrix dimension cap')
    if not M.rows or not M.cols:
        S,U,V=zeros(M.rows,M.cols),eye(M.rows),eye(M.cols)
    else:
        S,U,V=[x.to_Matrix() for x in smith_normal_decomp(
            DomainMatrix.from_Matrix(M).convert_to(ZZ))]
    for i in range(min(S.shape)):
        if S[i,i]<0:
            S.row_op(i,lambda x,j:-x); U.row_op(i,lambda x,j:-x)
    Ui,Vi=U.inv(),V.inv()
    cert=dict(S=pack(S),U=pack(U),Uinv=pack(Ui),V=pack(V),Vinv=pack(Vi))
    rank=sum(S[i,i]!=0 for i in range(min(S.shape)))
    return cert,dict(S=S,U=U,V=V,Ui=Ui,Vi=Vi,rank=rank)

def homology(A: Matrix,B: Matrix) -> tuple[dict[str,Any],dict[str,Any]]:
    if B.cols!=A.rows or B*A!=zeros(B.rows,A.cols):
        raise ValueError('not a chain segment')
    cb,b=smith(B); r=b['rank']; n=A.rows; k=n-r
    K=b['V'][:,r:n]; L=b['Vi'][r:n,:]
    cc,c=smith(L*A); s=c['rank']
    cert=dict(kind='homology',normalB=cb,normalC=cc,free_rank=k-s,
              torsion=[int(c['S'][i,i]) for i in range(s) if c['S'][i,i]>1])
    return cert,dict(b=b,c=c,K=K,L=L,X=c['U']*L,R=K*c['Ui'])

def cycle(A: Matrix,B: Matrix,z: Matrix) -> dict[str,Any]:
    if B*z!=zeros(B.rows,1): raise ValueError('not a cycle')
    _,h=homology(A,B); y=h['X']*z; c=h['c']; s=c['rank']
    for i in range(y.rows):
        modulus=int(c['S'][i,i]) if i<s else 0
        bad=(int(y[i])%modulus!=0) if modulus else (y[i]!=0)
        if bad:
            return dict(kind='obstruction',phi=pack(h['X'][i:i+1,:]),modulus=modulus)
    t=zeros(A.cols,1)
    for i in range(s): t[i]=y[i]/c['S'][i,i]
    return dict(kind='fill',w=pack(c['V']*t))

def chain_pack(degrees: list[int],d: Matrix) -> dict[str,Any]:
    return dict(degrees=degrees,d=pack(d))

def reduction(degrees: list[int],D: Matrix,max_steps: int=128) -> tuple[dict[str,Any],dict[str,int]]:
    """Greedy unit cancellation. No promise of a smallest reduced complex."""
    n=D.rows; ds=list(degrees); d=D.copy()
    f,g,H=eye(n),eye(n),zeros(n,n); steps=0
    while True:
        candidates=[]
        for i in range(d.rows):
            for j in range(d.cols):
                if abs(d[i,j])==1:
                    cost=(sum(d[i,k]!=0 for k in range(d.cols))-1)*(sum(d[k,j]!=0 for k in range(d.rows))-1)
                    candidates.append((cost,i,j))
        if not candidates: break
        if steps>=max_steps: break # partial reductions remain valid certificates
        _,i,j=min(candidates); size=d.rows
        h=zeros(size,size); h[j,i]=d[i,j] # inverse of +1 or -1
        keep=[k for k in range(size) if k not in (i,j)]
        emb=eye(size)[:,keep]; pr=emb.T
        ff=pr*(eye(size)-d*h); gg=(eye(size)-h*d)*emb
        dd=pr*(d-d*h*d)*emb
        H=H+g*h*f; f=ff*f; g=g*gg
        d=dd; ds=[ds[k] for k in keep]; steps+=1
    return dict(kind='reduction',reduced=chain_pack(ds,d),f=pack(f),g=pack(g),h=pack(H)),dict(steps=steps,before=n,after=len(ds))

def solve_integer(M: Matrix,b: Matrix) -> tuple[str,Matrix,int]:
    """Internal reuse of ordinary Smith/lattice solving, not a new Forge idea."""
    _,s=smith(M); y=s['U']*b; r=s['rank']
    for i in range(M.rows):
        m=int(s['S'][i,i]) if i<r else 0
        if (int(y[i])%m!=0) if m else (y[i]!=0):
            return 'obstruction',s['U'][i:i+1,:],m
    z=zeros(M.cols,1)
    for i in range(r): z[i]=y[i]/s['S'][i,i]
    return 'solution',s['V']*z,0

def homotopy(sd: list[int],dC: Matrix,td: list[int],dD: Matrix,F: Matrix,G: Matrix,
             max_variables: int=256) -> tuple[dict[str,Any],dict[str,int]]:
    """Solve one coupled integer system, including zero-dimensional cases."""
    equations=[(i,j) for i in range(len(td)) for j in range(len(sd)) if td[i]==sd[j]]
    variables=[(i,j) for i in range(len(td)) for j in range(len(sd)) if td[i]==sd[j]+1]
    if len(variables)>max_variables or len(equations)>256:
        raise SearchLimit('homotopy equation/variable cap')
    T=F-G; b=Matrix(len(equations),1,[T[i,j] for i,j in equations])
    L=zeros(len(equations),len(variables))
    # Search-side vectorization. Checker uses the matrix adjoint instead.
    for col,(a,bj) in enumerate(variables):
        for row,(i,j) in enumerate(equations):
            L[row,col]=(dD[i,a] if j==bj else 0)+(dC[bj,j] if i==a else 0)
    outcome,v,m=solve_integer(L,b)
    result=zeros(len(td),len(sd))
    if outcome=='solution':
        for t,(i,j) in zip(v,variables): result[i,j]=t
        cert=dict(kind='homotopy',H=pack(result))
    else:
        for t,(i,j) in zip(v,equations): result[i,j]=t
        cert=dict(kind='no_homotopy',W=pack(result),modulus=m)
    return cert,dict(equations=len(equations),variables=len(variables))

def induced(A: Matrix,B: Matrix,At: Matrix,Bt: Matrix,F: Matrix) -> dict[str,Any]:
    cs,hs=homology(A,B); ct,ht=homology(At,Bt)
    return dict(kind='induced',source_homology=cs,target_homology=ct,M=pack(ht['X']*F*hs['R']))

def transport_homotopy(Cred: dict[str,Any],Dred: dict[str,Any],T: Matrix,Hbar: Matrix) -> Matrix:
    """Lift a homotopy for f_D T g_C through checked deformation retracts."""
    fC,gC,hC=[unpack(Cred[k]) for k in ('f','g','h')]
    fD,gD,hD=[unpack(Dred[k]) for k in ('f','g','h')]
    return hD*T+gD*Hbar*fC+gD*fD*T*hC
