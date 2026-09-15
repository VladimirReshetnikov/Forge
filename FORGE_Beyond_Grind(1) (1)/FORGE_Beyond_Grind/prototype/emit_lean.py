#!/usr/bin/env python3
"""Emit candidate Lean replay scripts. NOT compiled in the authoring environment."""
from __future__ import annotations
from fractions import Fraction as Q
from math import comb
from pathlib import Path
from forge.poly import Poly
from forge.search import quadratic_sos,bernstein_search
from forge.certificates import *
from forge.synthesis import synthesize_recurrence,synthesize_affine_witness

ROOT=Path(__file__).resolve().parents[1]/'lean'
HEADER='''/-
GENERATED CANDIDATE PROOF SCRIPTS: not compiled in the authoring environment.
No theorem here is claimed to have passed Lean until `lake build` succeeds.
Generated from exact Python certificates; no `sorry` or oracle axioms inserted.
-/
import Mathlib

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace ForgeReplay
'''


def number(c):
    return str(c.numerator) if c.denominator==1 else f'({c.numerator} / {c.denominator})'


def cone_expression(cert,names):
    return ' + '.join(f'({number(t.weight)}) * ({t.square.lean(names)}) ^ 2' for t in cert.terms) or '0'


def interval_basis(p,box,names):
    bs=bernstein_coefficients(p,box)
    degrees=[max(e[i] for e in bs) for i in range(p.n)]
    terms=[]
    for beta,c in bs.items():
        if not c:continue
        factors=[]
        for v,k,d,(l,u) in zip(names,beta,degrees,box):
            c*=Q(comb(d,k))/(u-l)**d
            if k:factors.append(f'({v} - ({number(l)})) ^ {k}')
            if d-k:factors.append(f'(({number(u)}) - {v}) ^ {d-k}')
        terms.append(f'({number(c)})' + ''.join(' * '+s for s in factors))
    return ' +\n      '.join(terms) or '0'


def branch_proof(p,box,tree,names,level=0,path='r'):
    pad='  '*level
    if isinstance(tree,BernsteinSplit):
        v=names[tree.axis]; s=number(tree.point)
        left,right=split_box(box,tree.axis,tree.point)
        text=pad+f'rcases le_total {v} ({s}) with hs_{path} | hs_{path}\n'
        text+=pad+'·\n'+branch_proof(p,left,tree.left,names,level+1,path+'l')
        text+=pad+'·\n'+branch_proof(p,right,tree.right,names,level+1,path+'r')
        return text
    lines=[]
    for i,(v,(l,u)) in enumerate(zip(names,box)):
        lines.append(pad+f'have lo_{path}_{i} : 0 ≤ {v} - ({number(l)}) := by linarith')
        lines.append(pad+f'have hi_{path}_{i} : 0 ≤ ({number(u)}) - {v} := by linarith')
    expr=interval_basis(p,box,names).replace('\n','\n'+pad)
    target=p.lean(names)
    lines.append(pad+'calc')
    lines.append(pad+f'  0 ≤ {expr} := by positivity')
    lines.append(pad+f'  _ = {target} := by ring')
    return '\n'.join(lines)+'\n'


def main():
    ROOT.mkdir(exist_ok=True)
    x,y=Poly.var(2,0),Poly.var(2,1)
    p=3*(x-2*y+1)**2+2*(2*x+y-3)**2+Q(1,7)*(x+y)**2
    cert=quadratic_sos(p);assert check_cone(p,[],[],cert)
    out=HEADER+'\n/-- Exact Schur-complement certificate; expanded target. -/\n'
    out+=f'theorem hidden_quadratic (x y : ℝ) : 0 ≤ {p.lean(["x","y"])} := by\n'
    out+=f'  calc\n    0 ≤ {cone_expression(cert,["x","y"])} := by positivity\n'
    out+=f'    _ = {p.lean(["x","y"])} := by ring\n\n'
    n=Poly.var(1,0)
    for power in range(7):
        step=n**power;f=synthesize_recurrence(step,Poly.const(1,0),power+1)
        out+=f'def powerSum{power} : ℕ → ℚ\n  | 0 => 0\n  | n + 1 => powerSum{power} n + ({step.lean(["(n : ℚ)"])})\n\n'
        out+=f'theorem powerSum{power}_formula (n : ℕ) :\n    powerSum{power} n = {f.lean(["(n : ℚ)"])} := by\n'
        out+=f'  induction n with\n  | zero => norm_num [powerSum{power}]\n'
        out+=f'  | succ n ih =>\n    rw [powerSum{power}, ih] <;> push_cast <;> ring\n\n'
    a=[[1,2],[0,1]];b=[[3,-1],[2,4]];c=[5,-3]
    w=synthesize_affine_witness(a,b,c,True)
    u=w.offset[0]+w.linear[0][0]*x+w.linear[0][1]*y
    v=w.offset[1]+w.linear[1][0]*x+w.linear[1][1]*y
    out+='theorem affine_witness (x y : ℤ) :\n    ∃ u v : ℤ, u + 2*v = 3*x-y+5 ∧ v = 2*x+4*y-3 := by\n'
    out+=f'  refine ⟨{u.lean(["x","y"])}, {v.lean(["x","y"])}, ?_⟩\n  constructor <;> ring\n\n'
    out+='end ForgeReplay\n\n#print axioms ForgeReplay.hidden_quadratic\n#print axioms ForgeReplay.powerSum6_formula\n'
    (ROOT/'GeneratedReplay.lean').write_text(out)
    p=x**4*y**2+x**2*y**4-3*x*x*y*y+1+Q(1,16)
    box=((Q(-2),Q(2)),)*2;tree=bernstein_search(p,box,max_depth=14)
    assert check_bernstein(p,box,tree)
    out=HEADER+'\n/-- 32 exact covering leaves; bounded Motzkin polynomial plus 1/16. -/\n'
    out+=f'theorem motzkin_box (x y : ℝ) (hxl : -2 ≤ x) (hxu : x ≤ 2)\n    (hyl : -2 ≤ y) (hyu : y ≤ 2) : 0 ≤ {p.lean(["x","y"])} := by\n'
    out+=branch_proof(p,box,tree,['x','y'],1)
    out+='\nend ForgeReplay\n\n#print axioms ForgeReplay.motzkin_box\n'
    (ROOT/'BernsteinReplay.lean').write_text(out)
    print('Generated uncompiled Lean candidate scripts:',ROOT)


if __name__=='__main__':main()
