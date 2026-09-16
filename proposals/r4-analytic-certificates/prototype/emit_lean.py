#!/usr/bin/env python3
"""Emit nonnegativity replay candidates for four origin-anchored receipts.

These are candidates, not compiler receipts. The emitter intentionally lowers
strict Python conclusions only to a plainly labelled nonnegativity theorem;
it never advertises those weaker Lean statements as closing the strict goals.
"""
import json
from pathlib import Path
from fractions import Fraction as Q
from forge_analytic.core import decode
from forge_analytic.check import verify_goal


def qlit(q):
    q=Q(q)
    return f'(({q.numerator} : ℝ) / {q.denominator})'


def expr(poly):
    terms=[f'({qlit(c)} * x ^ {k} * Real.exp ({qlit(r)} * x))'
           for (r,k),c in sorted(poly.items())]
    return ' + '.join(terms) if terms else '(0 : ℝ)'


def derivative(poly):
    terms=[f'(((((hasDerivAt_id x).pow {k}).const_mul {qlit(c)}).mul '
           f'(((hasDerivAt_id x).const_mul {qlit(r)}).exp)))'
           for (r,k),c in sorted(poly.items())]
    if not terms:
        return 'hasDerivAt_const x (0 : ℝ)'
    out=terms[0]
    for t in terms[1:]: out=f'({out}).add ({t})'
    return out


def main():
    root=Path(__file__).resolve().parents[1]
    problems=json.loads((root/'results/problems.json').read_text())
    receipts={r['problem_id']:r['certificate'] for r in
              json.loads((root/'results/certificates.json').read_text())}
    names=['taylor_04','entropy_positive_chart','log_lower_rational_chart','ghost_eps_1']
    output=[]
    for name in names:
        c=receipts[name]; p=problems[name]
        assert c['anchor']=='0' and verify_goal(p,c)
        polynomials=[decode(s['polynomial']) for s in c['steps']]+[{}]
        lines=['/- GENERATED / NOT COMPILED. See lean/STATUS.md. -/',
               'import LadderBridge','',f'namespace ForgeAnalytic.Generated.{name}']
        for j,poly in enumerate(polynomials):
            lines.append(f'private noncomputable def q{j} (x : ℝ) : ℝ := {expr(poly)}')
        n=len(c['steps'])
        lines+=['',f'private theorem h{n} (x : ℝ) (_hx : 0 ≤ x) : 0 ≤ q{n} x := by',
                f'  simp [q{n}]']
        for j in range(n-1,-1,-1):
            rho=qlit(c['steps'][j]['rho'])
            lines += ['',f'private theorem h{j} (x : ℝ) (hx : 0 ≤ x) : 0 ≤ q{j} x := by',
                      f'  apply ladder_step (f := q{j}) (g := q{j+1}) (a := 0) (rho := {rho})',
                      '  · intro x',f'    convert {derivative(polynomials[j])} using 1 <;>',
                      f'      dsimp [q{j}, q{j+1}] <;> norm_num <;> ring',
                      f'  · norm_num [q{j}]',f'  · exact h{j+1}','  · exact hx']
        lines+=['',f'theorem nonnegative (x : ℝ) (hx : 0 ≤ x) :',
                f'    0 ≤ {expr(polynomials[0])} := h0 x hx',
                '', '#print axioms nonnegative',f'end ForgeAnalytic.Generated.{name}','']
        path=root/'lean'/f'{name}.lean'
        path.write_text('\n'.join(lines),encoding='utf-8')
        output.append({'file':path.name,'source_problem':name,
                       'source_checked_in_python':True,'lean_status':'GENERATED_NOT_COMPILED',
                       'conclusion':'nonnegative on the closed ray [0,infinity)',
                       'strict_python_goal_not_claimed_closed':True})
    (root/'results/lean-emission.json').write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps(output,indent=2))

if __name__=='__main__': main()
