"""Independent, standard-library-only arithmetic replay.

This module imports neither the producer nor a computer algebra package.
A successful return establishes only this Python implementation's verdict,
not a Lean-kernel proof. The source problem is a separate argument.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Any
import json

MAX_DIM = 256
MAX_BITS = 16384

class Rejected(ValueError):
    """Malformed input, unsupported domain, or an invalid certificate."""

def need(condition: bool, message: str) -> None:
    if not condition:
        raise Rejected(message)

def keys(x: Any, expected: set[str]) -> None:
    need(type(x) is dict and set(x) == expected, f"expected keys {sorted(expected)}")

def integer(x: Any, name: str = "integer") -> int:
    need(type(x) is int, f"{name}: exact integer required (bool/float rejected)")
    need(x.bit_length() <= MAX_BITS, f"{name}: bit bound exceeded")
    return x

@dataclass(frozen=True)
class Mat:
    r: int
    c: int
    a: tuple[int, ...]
    def at(self, i: int, j: int) -> int:
        return self.a[i * self.c + j]
    def __add__(self, other: Mat) -> Mat:
        need((self.r,self.c)==(other.r,other.c), "addition shape")
        return Mat(self.r,self.c,tuple(x+y for x,y in zip(self.a,other.a)))
    def __neg__(self) -> Mat:
        return Mat(self.r,self.c,tuple(-x for x in self.a))
    def __sub__(self, other: Mat) -> Mat:
        return self + (-other)
    def __matmul__(self, other: Mat) -> Mat:
        need(self.c==other.r, "multiplication shape")
        # Arithmetic deliberately independent of SymPy and the producer.
        return Mat(self.r,other.c,tuple(
            sum(self.at(i,k)*other.at(k,j) for k in range(self.c))
            for i in range(self.r) for j in range(other.c)))
    def transpose(self) -> Mat:
        return Mat(self.c,self.r,tuple(self.at(i,j)
                   for j in range(self.c) for i in range(self.r)))
    def select(self, rows: list[int], cols: list[int]) -> Mat:
        return Mat(len(rows),len(cols),tuple(self.at(i,j) for i in rows for j in cols))
    def is_zero(self) -> bool:
        return all(x==0 for x in self.a)

def zero(r: int,c: int) -> Mat:
    return Mat(r,c,(0,)*(r*c))

def eye(n: int) -> Mat:
    return Mat(n,n,tuple(int(i==j) for i in range(n) for j in range(n)))

def matrix(x: Any, shape: tuple[int,int] | None = None) -> Mat:
    keys(x,{"rows","cols","data"})
    r,c=integer(x['rows']),integer(x['cols'])
    need(0<=r<=MAX_DIM and 0<=c<=MAX_DIM,"matrix dimension bound")
    need(type(x['data']) is list and len(x['data'])==r*c,"matrix storage shape")
    a=tuple(integer(v) for v in x['data'])
    if shape is not None:
        need((r,c)==shape,f"matrix shape expected {shape}, got {(r,c)}")
    return Mat(r,c,a)

def smith(M: Mat, cert: Any) -> dict[str,Any]:
    keys(cert,{"S","U","Uinv","V","Vinv"})
    S=matrix(cert['S'],(M.r,M.c))
    U=matrix(cert['U'],(M.r,M.r)); Ui=matrix(cert['Uinv'],(M.r,M.r))
    V=matrix(cert['V'],(M.c,M.c)); Vi=matrix(cert['Vinv'],(M.c,M.c))
    need(U@Ui==eye(M.r) and Ui@U==eye(M.r),"left change is not integrally invertible")
    need(V@Vi==eye(M.c) and Vi@V==eye(M.c),"right change is not integrally invertible")
    need(U@M@V==S,"Smith identity")
    need(all(S.at(i,j)==0 for i in range(S.r) for j in range(S.c) if i!=j),"not diagonal")
    ds=[S.at(i,i) for i in range(min(S.r,S.c))]
    rank=sum(x!=0 for x in ds)
    need(all(x>0 for x in ds[:rank]) and all(x==0 for x in ds[rank:]),"Smith sign/order")
    need(all(ds[i+1]%ds[i]==0 for i in range(rank-1)),"Smith divisibility")
    return dict(S=S,U=U,Ui=Ui,V=V,Vi=Vi,rank=rank,diag=ds[:rank])

def segment(A: Mat,B: Mat) -> None:
    need(B.c==A.r,"segment middle dimensions")
    need((B@A).is_zero(),"differential does not square to zero")

def homology(A: Mat,B: Mat,cert: Any) -> dict[str,Any]:
    keys(cert,{"kind","normalB","normalC","free_rank","torsion"})
    need(cert['kind']=='homology',"homology certificate tag")
    segment(A,B)
    b=smith(B,cert['normalB']); r=b['rank']; n=A.r; k=n-r
    K=b['V'].select(list(range(n)),list(range(r,n)))
    L=b['Vi'].select(list(range(r,n)),list(range(n)))
    C=L@A
    need(K@C==A,"boundary inclusion in the integral kernel")
    c=smith(C,cert['normalC']); s=c['rank']
    free=integer(cert['free_rank'])
    tors=cert['torsion']; need(type(tors) is list,"torsion list")
    tors=[integer(x) for x in tors]
    need(free==k-s and tors==[x for x in c['diag'] if x>1],"wrong homology invariants")
    X=c['U']@L; R=K@c['Ui']
    need(X@R==eye(k),"coordinate inverse")
    need((B@R).is_zero() and A@c['V']==R@c['S'],"representative relations")
    return dict(b=b,c=c,K=K,L=L,X=X,R=R,free_rank=free,torsion=tors)

def chain(obj: Any) -> tuple[list[int],Mat]:
    keys(obj,{"degrees","d"})
    need(type(obj['degrees']) is list,"degree list")
    degrees=[integer(v) for v in obj['degrees']]
    n=len(degrees); need(n<=MAX_DIM,"chain size bound")
    d=matrix(obj['d'],(n,n))
    graded(d,degrees,degrees,-1)
    need((d@d).is_zero(),"chain square-zero law")
    return degrees,d

def graded(M: Mat, target: list[int], source: list[int], shift: int) -> None:
    need((M.r,M.c)==(len(target),len(source)),"graded map shape")
    need(all(M.at(i,j)==0 or target[i]==source[j]+shift
             for i in range(M.r) for j in range(M.c)),"grading violation")

def annihilates(values: tuple[int,...], modulus: int) -> bool:
    return all(v==0 for v in values) if modulus==0 else all(v%modulus==0 for v in values)

def nonzero(value: int,modulus: int) -> bool:
    return value!=0 if modulus==0 else value%modulus!=0

def check(problem: Any, cert: Any) -> dict[str,Any]:
    need(type(problem) is dict and problem.get('domain')=='Z',"only the exact integer domain is supported")
    need(type(cert) is dict, 'certificate object required')
    kind=problem.get('kind')
    if kind=='homology':
        keys(problem,{"kind","domain","A","B"})
        A,B=matrix(problem['A']),matrix(problem['B'])
        h=homology(A,B,cert)
        return dict(kind='homology',free_rank=h['free_rank'],torsion=h['torsion'])
    if kind=='cycle':
        keys(problem,{"kind","domain","A","B","z"})
        A,B=matrix(problem['A']),matrix(problem['B']); segment(A,B)
        z=matrix(problem['z'],(A.r,1))
        need((B@z).is_zero(),"the supplied vector is not a cycle")
        need(type(cert) is dict,"cycle certificate object")
        if cert.get('kind')=='fill':
            keys(cert,{"kind","w"})
            w=matrix(cert['w'],(A.c,1)); need(A@w==z,"incorrect filler")
            return dict(kind='fill')
        keys(cert,{"kind","phi","modulus"})
        need(cert['kind']=='obstruction',"cycle outcome tag")
        phi=matrix(cert['phi'],(1,A.r)); m=integer(cert['modulus'])
        need(m==0 or m>=2,"invalid obstruction modulus")
        need(annihilates((phi@A).a,m),"functional does not annihilate boundaries")
        need(nonzero((phi@z).at(0,0),m),"functional does not separate cycle")
        return dict(kind='obstruction',modulus=m)
    if kind=='reduction':
        keys(problem,{"kind","domain","source"})
        keys(cert,{"kind","reduced","f","g","h"})
        need(cert['kind']=='reduction',"reduction certificate tag")
        sd,D=chain(problem['source']); td,d=chain(cert['reduced'])
        f=matrix(cert['f'],(len(td),len(sd)))
        g=matrix(cert['g'],(len(sd),len(td)))
        h=matrix(cert['h'],(len(sd),len(sd)))
        graded(f,td,sd,0); graded(g,sd,td,0); graded(h,sd,sd,1)
        need(f@D==d@f and D@g==g@d,"reduction chain-map laws")
        need(f@g==eye(len(td)),"retraction law")
        need(g@f==eye(len(sd))-D@h-h@D,"reduction homotopy law")
        return dict(kind='reduction',before=len(sd),after=len(td))
    if kind=='homotopy':
        keys(problem,{"kind","domain","source","target","F","G"})
        sd,dC=chain(problem['source']); td,dD=chain(problem['target'])
        F=matrix(problem['F'],(len(td),len(sd)))
        G=matrix(problem['G'],(len(td),len(sd)))
        for M in (F,G):
            graded(M,td,sd,0)
            need(dD@M==M@dC,"candidate is not a chain map")
        if cert.get('kind')=='homotopy':
            keys(cert,{"kind","H"}); H=matrix(cert['H'],(len(td),len(sd)))
            graded(H,td,sd,1)
            need(F-G==dD@H+H@dC,"homotopy equation")
            return dict(kind='homotopy')
        keys(cert,{"kind","W","modulus"})
        need(cert['kind']=='no_homotopy',"homotopy outcome tag")
        W=matrix(cert['W'],(len(td),len(sd))); graded(W,td,sd,0)
        m=integer(cert['modulus']); need(m==0 or m>=2,"invalid obstruction modulus")
        # Adjoint replay, NOT reconstruction of the producer's vectorized system.
        adjoint=dD.transpose()@W+W@dC.transpose()
        need(annihilates(adjoint.a,m),"adjoint does not vanish")
        pairing=sum(x*y for x,y in zip(W.a,(F-G).a))
        need(nonzero(pairing,m),"homotopy obstruction does not separate")
        return dict(kind='no_homotopy',modulus=m)
    if kind=='induced':
        keys(problem,{"kind","domain","A","B","At","Bt","F","E","G"})
        keys(cert,{"kind","source_homology","target_homology","M"})
        need(cert['kind']=='induced',"induced-map tag")
        A,B,At,Bt=(matrix(problem[k]) for k in ('A','B','At','Bt'))
        hs=homology(A,B,cert['source_homology']); ht=homology(At,Bt,cert['target_homology'])
        F=matrix(problem['F'],(At.r,A.r)); E=matrix(problem['E'],(Bt.r,B.r))
        G=matrix(problem['G'],(At.c,A.c))
        need(Bt@F==E@B and F@A==At@G,"map of source segments")
        M=matrix(cert['M'],(ht['X'].r,hs['R'].c))
        need(M==ht['X']@F@hs['R'],"wrong map in homology coordinates")
        T=ht['c']['Vi']@G@hs['c']['V']
        need(M@hs['c']['S']==ht['c']['S']@T,"quotient relation descent")
        return dict(kind='induced',rows=M.r,cols=M.c)
    raise Rejected(f"unsupported problem kind: {kind}")

def strict_loads(text: str) -> Any:
    def pairs(xs: list[tuple[str,Any]]) -> dict[str,Any]:
        out={}
        for k,v in xs:
            if k in out: raise Rejected(f'duplicate JSON key {k}')
            out[k]=v
        return out
    def reject_float(x: str) -> Any:
        raise Rejected(f'noninteger JSON number: {x}')
    return json.loads(text,object_pairs_hook=pairs,parse_float=reject_float,
                      parse_constant=reject_float)
