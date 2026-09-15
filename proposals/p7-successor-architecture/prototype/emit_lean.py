"""Emit ordinary Mathlib proof scripts from verified exact certificates.

Generation was exercised; compilation requires a compatible Mathlib project.
The supplied environment did not have Lean. No emitted file is labelled tested.
"""
from __future__ import annotations
from fractions import Fraction as Q
import json
from pathlib import Path
from polynomial import Poly
from verify_artifacts import load_sos, verify

ROOT = Path(__file__).resolve().parents[1]
HEADER = '''/-
Generated from exact certificates that passed the Python checker.
STATUS: NOT COMPILED IN THE AUTHORING ENVIRONMENT.
No `sorry`, extra axiom, `native_decide`, or external solver is used here.
Compilation with the reader's compatible Lean/Mathlib installation is required.
-/
import Mathlib

namespace ForgeArtifacts

'''


def scalar(c, field):
    sign = '-' if c < 0 else ''
    c = abs(c)
    numerator = f'({sign}{c.numerator} : {field})'
    return numerator if c.denominator == 1 else f'({numerator} / {c.denominator})'


def poly(p, names, field='ℝ'):
    terms = []
    for m,c in p.terms:
        fs = [scalar(c,field)]
        fs += [f'({v})' if k == 1 else f'({v}) ^ {k}' for v,k in zip(names,m) if k]
        terms.append('('+' * '.join(fs)+')')
    return '('+' + '.join(terms)+')' if terms else f'(0 : {field})'


def emit_sos():
    out = [HEADER]
    for path in sorted((ROOT/'results/certificates').glob('sos_*.json')):
        obj = json.loads(path.read_text()); p,c = load_sos(obj)
        if not verify(obj): raise ValueError(path)
        names = [f'x{i}' for i in range(p.target.n)]
        name = path.stem
        out.append(f'theorem {name} ({" ".join(names)} : ℝ)\n')
        for i,g in enumerate(p.ge): out.append(f'    (hge{i} : 0 ≤ {poly(g,names)})\n')
        for i,e in enumerate(p.eq): out.append(f'    (heq{i} : {poly(e,names)} = 0)\n')
        out.append(f'    : 0 ≤ {poly(p.target,names)} := by\n')
        terms=[]
        for k,(weight,atom) in enumerate(c.positive):
            q = poly(atom.square,names); value=f'({q}) ^ 2'
            out.append(f'  have hp{k}_0 : 0 ≤ {value} := sq_nonneg _\n')
            for j,i in enumerate(atom.assumptions):
                value=f'({value} * {poly(p.ge[i],names)})'
                out.append(f'  have hp{k}_{j+1} : 0 ≤ {value} := mul_nonneg hp{k}_{j} hge{i}\n')
            term=f'({scalar(weight,"ℝ")} * {value})';terms.append(term)
            out.append(f'  have ht{k} : 0 ≤ {term} := mul_nonneg (by norm_num) hp{k}_{len(atom.assumptions)}\n')
        positive='(0 : ℝ)'; proof='(le_refl (0 : ℝ))'
        for k,t in enumerate(terms):
            positive=f'({positive} + {t})';proof=f'(add_nonneg {proof} ht{k})'
        out.append(f'  have hpos : 0 ≤ {positive} := {proof}\n')
        ideal='(0 : ℝ)'; zeros=[]
        for j,(i,m) in enumerate(c.ideal):
            term=f'({poly(m,names)} * {poly(p.eq[i],names)})'
            out.append(f'  have hz{j} : {term} = 0 := by\n    rw [heq{i}] <;> ring\n')
            ideal=f'({ideal} + {term})';zeros.append(f'hz{j}')
        out.append(f'  have hid : {poly(p.target,names)} = {positive} + {ideal} := by ring\n')
        out.append('  calc\n')
        out.append(f'    0 ≤ {positive} := hpos\n')
        out.append(f'    _ = {positive} + {ideal} := by\n')
        if zeros: out.append('      rw ['+', '.join(zeros)+'] <;> ring\n')
        else: out.append('      ring\n')
        out.append(f'    _ = {poly(p.target,names)} := hid.symm\n\n')
    out.append('end ForgeArtifacts\n')
    (ROOT/'lean/GeneratedSOS.lean').write_text(''.join(out),encoding='utf-8')


def emit_induction():
    out=[HEADER]
    for path in sorted((ROOT/'results/certificates').glob('induction_*.json')):
        obj=json.loads(path.read_text())
        if not verify(obj): raise ValueError(path)
        r=Poly.from_json(obj['increment']);F=Poly.from_json(obj['certificate']['invariant'])
        name=path.stem.removeprefix('induction_');func='acc_'+name
        rv=poly(r,['(n : ℚ)','a'],'ℚ'); fv=poly(F,['(n : ℚ)','a'],'ℚ')
        out.append(f'def {func} : ℕ → ℚ → ℚ\n  | 0, a => a\n  | n + 1, a => {func} n (a + {rv})\n\n')
        out.append(f'theorem invariant_{name} (n : ℕ) (a : ℚ) :\n    {func} n a = {fv} := by\n')
        out.append(f'  induction n generalizing a with\n  | zero => norm_num [{func}]\n')
        out.append(f'  | succ n ih =>\n    rw [{func}, ih]\n    push_cast <;> ring\n\n')
    out.append('end ForgeArtifacts\n')
    (ROOT/'lean/GeneratedInduction.lean').write_text(''.join(out),encoding='utf-8')

if __name__=='__main__':
    emit_sos();emit_induction()
    print('Emitted two Lean files. Lean compilation NOT performed.')
