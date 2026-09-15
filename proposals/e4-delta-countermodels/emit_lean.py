#!/usr/bin/env python3
"""Emit LOCAL certificate identity obligations. Output is not compiled here.

These theorems do not themselves connect the original Lean source program to
machine semantics. Reachability.lean illustrates the separate induction bridge.
"""
from pathlib import Path
import json
from fractions import Fraction as Q
from forge_delta.checker import verify_positive


def number(raw):
    a,b=raw
    return f'({a} : ℚ)' if b==1 else f'(({a} : ℚ) / {b})'


def polynomial(raw,variables):
    terms=[]
    for m,c in raw:
        factors=[number(c)]
        factors += [f'({v})' if e==1 else f'({v})^{e}' for v,e in zip(variables,m,strict=True) if e]
        terms.append(' * '.join(factors))
    return '(0 : ℚ)' if not terms else '('+' + '.join(terms)+')'


def combination(ps,coords,variables):
    terms=[f'{number(c)} * {polynomial(p,variables)}' for p,c in zip(ps,coords,strict=True) if c[0]]
    return '(0 : ℚ)' if not terms else '('+' + '.join(terms)+')'


def main():
    root=Path(__file__).resolve().parent
    corpus=json.loads((root/'results/corpus.json').read_text())
    out=['/- Generated local identities only. NOT COMPILED. See lean/STATUS.md. -/',
         'import Mathlib','set_option autoImplicit false','namespace ForgeDeltaGenerated']
    theorem_names=[]
    def theorem(name,variables,left,right,tactic='ring'):
        bind=' ('+' '.join(variables)+' : ℚ)' if variables else ''
        out.extend([f'theorem {name}{bind} :',f'    {left} = {right} := by',f'  {tactic}',''])
        theorem_names.append(name)
    for item in corpus:
        if item['result']['status']!='proved':continue
        p=item['problem'];c=item['result']['certificate'];assert verify_positive(p,c)
        stem=item['name'];xs=[f'x{i}' for i in range(p['state_dim'])];us=[f'u{i}' for i in range(p['input_dim'])]
        for i,b in enumerate(c['basis'][p['initial']['node']]):
            theorem(f'{stem}_init_{i}',[],polynomial(b,[number(v) for v in p['initial']['state']]),'(0 : ℚ)','norm_num')
        for node,gs in enumerate(p['goals']):
            for j,g in enumerate(gs):
                theorem(f'{stem}_goal_{node}_{j}',xs,polynomial(g,xs),
                        combination(c['basis'][node],c['goal_coordinates'][node][j],xs))
        for ei,e in enumerate(p['edges']):
            fs=[polynomial(f,xs+us) for f in e['update']]
            for j,b in enumerate(c['basis'][e['dst']]):
                terms=[]
                for entry in c['edge_coordinates'][ei][j]:
                    mon=' * '.join(f'({v})^{k}' for v,k in zip(us,entry['input_exponent'],strict=True) if k) or '(1 : ℚ)'
                    terms.append(f'({mon}) * {combination(c["basis"][e["src"]],entry["coordinates"],xs)}')
                rhs=' + '.join(terms) or '(0 : ℚ)'
                theorem(f'{stem}_edge_{ei}_{j}',xs+us,polynomial(b,fs),'('+rhs+')')
    out+=['-- Audit these after a successful compilation.']+[f'#print axioms {n}' for n in theorem_names]
    out+=['end ForgeDeltaGenerated']
    target=root/'lean/GeneratedIdentities.lean';target.write_text('\n'.join(out)+'\n')
    (root/'results/lean-generation.json').write_text(json.dumps({'status':'GENERATED_NOT_COMPILED',
         'identity_theorems':len(theorem_names),'file':'lean/GeneratedIdentities.lean',
         'original_source_semantics_bridge':False},indent=2)+'\n')
    print(f'{len(theorem_names)} local identity obligations emitted; not compiled.')

if __name__=='__main__':main()
