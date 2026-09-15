"""Emit ordinary noncomm_ring replay candidates from already stored certificates.

Generation is NOT Lean checking. Output files are explicitly marked NOT_COMPILED.
Only integral coefficients are emitted into the generic Ring theorem.
"""
from pathlib import Path
from fractions import Fraction
import json

ROOT=Path(__file__).resolve().parents[1]

def word(w): return '('+' * '.join('ab'[i] for i in w)+')' if w else '(1 : R)'
def linear_sum(ts):return '('+' + '.join(ts)+')' if ts else '(0 : R)'
def coefficient(c,e):
    q=Fraction(c)
    if q.denominator!=1:raise ValueError('generic Ring replay requires integral coefficients')
    if q==1:return e
    if q==-1:return f'(-{e})'
    return f'(({q.numerator} : R) * {e})'
def poly(p):return linear_sum([coefficient(t['c'],word(t['m'])) for t in p])

def main():
    ps=json.loads((ROOT/'results/problems.json').read_text())
    cs=json.loads((ROOT/'results/certificates.json').read_text())
    lines=['/- Generated ordinary proof scripts. NOT_COMPILED in this run. -/',
           'import Mathlib', 'set_option autoImplicit false','namespace ForgeExtensions','']
    names=[]
    for name in ['commuting_idempotent_join','weyl_commutator_4']:
        p,c=ps[name],cs[name]
        rhs=[]
        rels=[poly(r) for r in p['relations']]
        for t in c['terms']:
            e=f"({word(t['left'])} * {rels[t['relation']]} * {word(t['right'])})"
            rhs.append(coefficient(t['coefficient'],e))
        lines += [f'theorem {name} {{R : Type*}} [Ring R] (a b : R)']
        lines += [f'    (h{i} : {r} = 0)' for i,r in enumerate(rels)]
        lines += [f'    : {poly(p["target"])} = 0 := by','  calc',
                  f'    _ = {linear_sum(rhs)} := by noncomm_ring',
                  '    _ = 0 := by simp only ['+', '.join(f'h{i}' for i in range(len(rels)))+', mul_zero, zero_mul, add_zero, zero_add, neg_zero]','']
        names.append(name)
    lines += ['end ForgeExtensions']+[f'#print axioms ForgeExtensions.{n}' for n in names]
    (ROOT/'lean/ForgeExtensions/GeneratedNC.lean').write_text('\n'.join(lines)+'\n')
    (ROOT/'lean/ForgeExtensions.lean').write_text('import ForgeExtensions.Reachability\nimport ForgeExtensions.ReplayExamples\nimport ForgeExtensions.GeneratedNC\n')
    print('Generated two integral noncommutative replays; Lean status remains NOT_COMPILED.')

if __name__=='__main__':main()
