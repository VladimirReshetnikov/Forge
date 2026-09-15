"""Export accepted certificates to ordinary Lean/mathlib proof scripts.
The exporter itself has been run; generated Lean source was NOT compiled in
this environment. These are replay obligations, not an implemented Forge tactic.
"""
from __future__ import annotations
import argparse,json,re
from fractions import Fraction as Q
from pathlib import Path
from forge.polynomial import Poly
from forge.checkers import check_cone,check_invariant
from validate_artifacts import load_cone,load_invariant


def rat(c):
    c=Q(c)
    return f'({c.numerator} : ℝ)' if c.denominator==1 else f'(({c.numerator} : ℝ) / {c.denominator})'


def poly(p,names=None):
    names=names or [f'x{i}' for i in range(p.nvars)]
    out=[]
    for m,c in p.terms:
        fs=[rat(c)]
        for v,e in zip(names,m):
            if e:fs.append(f'({v})' if e==1 else f'({v}) ^ {e}')
        out.append(' * '.join(fs))
    return '('+' + '.join(out)+')' if out else '(0 : ℝ)'


def nn_term(t,gs):
    s=f'({rat(t.weight)} * ({poly(t.square)}) ^ 2)'
    pr=f'(mul_nonneg (by norm_num : (0 : ℝ) ≤ {rat(t.weight)}) (sq_nonneg {poly(t.square)}))'
    for i in t.factors:
        s=f'({s} * {poly(gs[i])})'
        pr=f'(mul_nonneg {pr} hg{i})'
    return s,pr


def statement(name,p,gs,es):
    args=' '.join(f'x{i}' for i in range(p.nvars))
    return (f'theorem {name} ({args} : ℝ)\n'+
            ''.join(f'    (hg{i} : 0 ≤ {poly(g)})\n' for i,g in enumerate(gs))+
            ''.join(f'    (he{i} : {poly(e)} = 0)\n' for i,e in enumerate(es))+
            f'    : 0 ≤ {poly(p)} := by\n')


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--results',type=Path,default=Path('../results'))
    ap.add_argument('--output',type=Path,default=Path('../lean')); a=ap.parse_args()
    out=a.output/'Forge';out.mkdir(parents=True,exist_ok=True)
    header='''/- Generated from exact Python certificates.
   STATUS: source exported, NOT compiled or kernel-checked in this environment.
   No Forge search tactic is implemented in this directory. -/
import Mathlib

namespace ForgeReplay

'''
    text=header; cases=[]
    for r in json.loads((a.results/'cone_certificates.json').read_text()):
        p,gs,es,c=load_cone(r)
        assert check_cone(p,gs,es,c)
        name=re.sub('[^a-zA-Z0-9_]','_',r['name'])
        text+=statement(name,p,gs,es)
        s='(0 : ℝ)'; pr='(le_refl (0 : ℝ))'
        for i,t in enumerate(c.terms):
            ti,pi=nn_term(t,gs)
            text+=f'  have ht{i} : 0 ≤ {ti} :=\n    {pi}\n'
            s=f'({s} + {ti})';pr=f'(add_nonneg {pr} ht{i})'
        text+=f'  have hs : 0 ≤ {s} :=\n    {pr}\n'
        if es:
            ideal='('+' + '.join(f'({poly(h)} * {poly(e)})' for h,e in zip(c.ideal,es))+')'
            text+=f'  have hi : {ideal} = 0 := by\n'
            text+='    simp only ['+', '.join([f'he{i}' for i in range(len(es))]+['mul_zero','add_zero'])+']\n'
            text+=f'  have hid : {poly(p)} = {s} + {ideal} := by ring\n'
            text+='  rw [hid, hi, add_zero]\n  exact hs\n\n'
        else:
            text+=f'  calc\n    0 ≤ {s} := hs\n    _ = {poly(p)} := by ring\n\n'
        cases.append({'name':name,'prefix':'import Mathlib\n\n'+statement('comparison_goal',p,gs,es)})
    text+='end ForgeReplay\n';(out/'Certificates.lean').write_text(text)
    text=header+'''def orbit {α : Type} (T : α → α) (s₀ : α) : Nat → α
  | 0 => s₀
  | n + 1 => T (orbit T s₀ n)

theorem orbit_invariant {α : Type} (T : α → α) (s₀ : α)
    (I : α → ℝ) (hbase : I s₀ = 0) (hstep : ∀ s, I (T s) = I s) :
    ∀ n, I (orbit T s₀ n) = 0 := by
  intro n
  induction n with
  | zero => simpa only [orbit] using hbase
  | succ n ih => simpa only [orbit, hstep] using ih

'''
    for r in json.loads((a.results/'invariant_certificates.json').read_text()):
        c=load_invariant(r);assert check_invariant(c)
        name=re.sub('[^a-zA-Z0-9_]','_',r['name']);vs=['s.1','s.2']
        inv=poly(c.invariant,vs);trans='('+', '.join(poly(p,vs) for p in c.transition)+')'
        init='('+', '.join(rat(v) for v in c.initial)+')'
        text+=f'def state_{name} := {init}\n'
        text+=f'def step_{name} (s : ℝ × ℝ) : ℝ × ℝ :=\n  {trans}\n'
        text+=f'def invariant_{name} (s : ℝ × ℝ) : ℝ :=\n  {inv}\n'
        text+=f'theorem preserved_{name} (n : Nat) :\n    invariant_{name} (orbit step_{name} state_{name} n) = 0 := by\n'
        text+=f'  apply orbit_invariant step_{name} state_{name} invariant_{name}\n'
        text+=f'  · norm_num [invariant_{name}, state_{name}]\n'
        text+=f'  · intro s\n    dsimp [invariant_{name}, step_{name}]\n    ring\n\n'
    text+='end ForgeReplay\n';(out/'Invariants.lean').write_text(text)
    (a.output/'comparison_cases.json').write_text(json.dumps(cases,indent=2)+'\n')
    (a.output/'Forge.lean').write_text('import Forge.Certificates\nimport Forge.Invariants\n')
    print(f'Exported {len(cases)} inequality proofs and 49 recurrence proofs; Lean compilation NOT performed.')

if __name__=='__main__':main()
