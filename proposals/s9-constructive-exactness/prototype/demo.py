#!/usr/bin/env python3
"""Run the three small examples discussed in the article."""
from sympy import Matrix, zeros
from exactness import producer as p
from exactness.checker import check
import json

def segment(kind,A,B,**more):
    return dict(kind=kind,domain='Z',A=p.pack(A),B=p.pack(B),**more)

B=Matrix([[-1,-1,0],[1,0,-1],[0,1,1]])
z=Matrix([1,-1,1]); A=2*z
hc,_=p.homology(A,B)
print('Doubled face:',check(segment('homology',A,B),hc))
for scale in [1,2]:
    problem=segment('cycle',A,B,z=p.pack(scale*z)); cert=p.cycle(A,B,scale*z)
    print('Cycle multiple',scale,check(problem,cert),json.dumps(cert))
d=Matrix([[0,2],[0,0]]); F=Matrix([[0,1],[0,0]])
problem=dict(kind='homotopy',domain='Z',source=p.chain_pack([0,1],d),
             target=p.chain_pack([1,2],d),F=p.pack(F),G=p.pack(zeros(2)))
cert,_=p.homotopy([0,1],d,[1,2],d,F,zeros(2))
print('Equal induced homology maps, no chain homotopy:',check(problem,cert))
print(json.dumps(cert,indent=2))
