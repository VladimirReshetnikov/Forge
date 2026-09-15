"""Deterministic synthetic problems; no source programs are mined from a corpus.

Expectations come from the explicit constructions below, not the search result.
The seed controls affine coordinate changes only. Positive cases are still
accepted solely after exact certificate replay.
"""
from dataclasses import dataclass
import random
import sympy as s
from search import System, Edge

SEED=20260915

@dataclass
class Case:
    family: str
    expected: str
    system: System


def corpus():
    x,y,z,u,v,t=s.symbols('x y z u v t')
    out=[]
    for k in range(8):
        a=k+2
        P=System(f'scaled_graph_{k:02}',(x,y),(t,),1,[(0,(t,t*t))],
                 [Edge(0,0,(u,),(x+u,a*y-(a-1)*x*x+2*x*u+u*u))],[(0,y-x*x)])
        out.append(Case('scaled graph','proved',P))
    for k in range(8):
        c=k+1
        P=System(f'coupled_graph_{k:02}',(x,y,z),(t,),1,[(0,(t,t*t,t**3))],
                 [Edge(0,0,(u,),(x+u,(x+u)**2+z-x**3,
                        (x+u)**3+(x+u+c)*(y-x*x)))],[(0,y-x*x)])
        out.append(Case('coupled nonlinear','proved',P))
    for k in range(8):
        a=k+1; b=k%3
        P=System(f'nonlinear_equivalence_{k:02}',(z,x,y),(t,),1,[(0,(t,t,t*t))],
                 [Edge(0,0,(u,),(z*z+a*u+b,y+a*u+b,(y+a*u+b)**2))],[(0,z-x)])
        out.append(Case('nonlinear equivalence','proved',P))
        P=System(f'nonlinear_mutant_{k:02}',(z,x,y),(t,),1,[(0,(t,t,t*t))],
                 [Edge(0,0,(u,),(z*z+a*u+b,y+a*u+b,(y+a*u+b)**2+(k+1)))],[(0,z-x)])
        out.append(Case('nonlinear mutant','refuted',P))
    rng=random.Random(SEED)
    for k in range(12):
        n=2+k%2
        xs=s.symbols(f'a0:{n}'); ys=s.symbols(f'b0:{n}'); ts=s.symbols(f't0:{n}')
        U=s.eye(n)
        for i in range(n):
            for j in range(i): U[i,j]=rng.randint(-2,2)
        inv=U.inv()
        # Sparse, noncommuting transitions. A shift eventually exposes every coordinate.
        A=s.zeros(n)
        for i in range(n-1): A[i,i+1]=1
        A[n-1,0]=1+k%2
        D=s.diag(*range(1,n+1))
        edges=[]
        for M in (A,D):
            h=s.Matrix([rng.randint(-2,2) for _ in range(n)])
            fx=M*s.Matrix(xs)+h*u
            fy=U*M*inv*s.Matrix(ys)+U*h*u
            edges.append(Edge(0,0,(u,),tuple(map(s.expand,(*fx,*fy)))))
        initial=tuple((*ts,*(U*s.Matrix(ts))))
        target=xs[0]-(inv*s.Matrix(ys))[0]
        P=System(f'affine_equivalence_{k:02}',xs+ys,ts,1,[(0,initial)],edges,[(0,target)])
        out.append(Case('affine equivalence','proved',P))
        if k<6:
            changed=list(edges[0].update)
            perturb=U*s.Matrix([0]*(n-1)+[1])
            for i in range(n): changed[n+i]+=perturb[i]
            mutant=[Edge(0,0,(u,),tuple(changed)),edges[1]]
            P=System(f'affine_mutant_{k:02}',xs+ys,ts,1,[(0,initial)],mutant,[(0,target)])
            out.append(Case('affine mutant','refuted',P))
    for k in range(4):
        c=k+1
        edges=[Edge(0,1,(u,),(x+u,y+u+c)),Edge(1,0,(v,),(x+v,y+v-c))]
        P=System(f'control_locations_{k:02}',(x,y),(t,),2,[(0,(t,t))],edges,[(1,y-x-c)])
        out.append(Case('control flow','proved',P))
    out.extend([
        Case('boundary controls','refuted',System('sampling_trap',(x,),(),1,[(0,(0,))],
             [Edge(0,0,(u,),(x+u*(u-1)*(u-2),))],[(0,x)])),
        Case('boundary controls','refuted',System('initial_parameter_trap',(x,),(t,),1,[(0,(t,))],
             [],[(0,x*(x-1)*(x-2))])),
        Case('boundary controls','proved',System('simultaneous_swap',(x,y,z),(t,),1,[(0,(t,t+1,t))],
             [Edge(0,0,(),(y,x,z))],[(0,x+y-2*z-1)])),
        Case('boundary controls','proved',System('two_fresh_inputs',(x,y),(t,),1,[(0,(t,t*t))],
             [Edge(0,0,(u,v),(x+u*v,(x+u*v)**2+2*(y-x*x)))],[(0,y-x*x)])),
        Case('boundary controls','proved',System('unreachable_observation',(x,),(),2,[(0,(0,))],
             [Edge(0,0,(),(x+1,))],[(1,s.Integer(1))])),
        Case('boundary controls','proved',System('rational_scaling',(x,y),(t,),1,[(0,(t,t*t))],
             [Edge(0,0,(u,),(x+u,s.Rational(2,3)*(y-x*x)+(x+u)**2))],[(0,y-x*x)])),
        Case('boundary controls','proved',System('multiple_targets',(x,y,z),(t,),1,[(0,(t,t,t))],
             [Edge(0,0,(u,),(x+u,y+u,z+u))],[(0,x-y),(0,y-z)])),
        Case('boundary controls','refuted',System('ordered_trace',(x,),(),3,[(0,(0,))],
             [Edge(0,1,(),(x+1,)),Edge(1,2,(),(2*x,))],[(2,x-1)])),
    ])
    return out

if __name__=='__main__':
    from collections import Counter
    print(len(corpus()),dict(Counter(c.family for c in corpus())))
