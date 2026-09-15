"""Emission of candidate Lean/mathlib replay scripts from accepted certificates.

PROVENANCE
  BASE  p5-certificate-first/prototype/export_lean.py -- theorem statements with
        named hypotheses, equality-ideal handling (rewrite by he_i, then ring),
        and the `orbit` induction scaffolding for conserved invariants.
  FOLD  p1-structural-search/prototype/emit_lean.py -- the Bernstein branch
        emitter that turns a split tree into nested `rcases le_total ...` cases,
        each closed by `positivity` + `ring`.
  FOLD  p7-successor-architecture/prototype/emit_lean.py -- `induction n
        generalizing a` for accumulator invariants.
  FOLD  p3-planner-certificate-layer -- the guard is a RAISE, not an assert,
        because asserts vanish under `python -O`.

STATUS: this module emits source text. Nothing here compiles or kernel-checks
Lean, and no Forge tactic is implemented. Emitted theorems are replay
obligations, not proved results.
"""
from __future__ import annotations
from fractions import Fraction as Q
from typing import Sequence
from ..poly import Poly, Box
from ..certificates import (ConeCertificate, check_cone, InvariantCertificate,
                            check_invariant, BernsteinLeaf, BernsteinSplit,
                            BernsteinTree, check_bernstein, bernstein_coefficients,
                            split_box)
from ..recurrence import AccumulatorCertificate, check_accumulator

HEADER = '''/-
GENERATED CANDIDATE PROOF SCRIPTS: not compiled in the authoring environment.
No theorem here is claimed to have passed Lean until `lake build` succeeds.
Generated from exact Python certificates; no `sorry` or oracle axioms inserted.
-/
import Mathlib

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace ForgeReplay
'''

FOOTER = '\nend ForgeReplay\n'

ORBIT_PREAMBLE = '''
def orbit {α : Type} (T : α → α) (s₀ : α) : Nat → α
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


def rat(c: Q, ty: str = 'ℝ') -> str:
    c = Q(c)
    return (f'({c.numerator} : {ty})' if c.denominator == 1
            else f'(({c.numerator} : {ty}) / {c.denominator})')


def number(c: Q) -> str:
    c = Q(c)
    return str(c.numerator) if c.denominator == 1 else f'({c.numerator} / {c.denominator})'


def poly_lean(p: Poly, names: Sequence[str] | None = None, ty: str = 'ℝ') -> str:
    names = tuple(names) if names else tuple(f'x{i}' for i in range(p.n))
    if len(names) != p.n:
        raise ValueError('wrong name dimension')
    out = []
    for m, c in p.terms:
        factors = [rat(c, ty)]
        for v, e in zip(names, m):
            if e:
                factors.append(f'({v})' if e == 1 else f'({v}) ^ {e}')
        out.append(' * '.join(factors))
    return '(' + ' + '.join(out) + ')' if out else f'(0 : {ty})'


def _statement(name: str, p: Poly, gs: Sequence[Poly], es: Sequence[Poly],
               names: Sequence[str]) -> str:
    args = ' '.join(names)
    return (f'theorem {name} ({args} : ℝ)\n'
            + ''.join(f'    (hg{i} : 0 ≤ {poly_lean(g, names)})\n' for i, g in enumerate(gs))
            + ''.join(f'    (he{i} : {poly_lean(e, names)} = 0)\n' for i, e in enumerate(es))
            + f'    : 0 ≤ {poly_lean(p, names)} := by\n')


def _nonneg_term(t, gs, names) -> tuple[str, str]:
    s = f'({rat(t.weight)} * ({poly_lean(t.square, names)}) ^ 2)'
    pr = (f'(mul_nonneg (by norm_num : (0 : ℝ) ≤ {rat(t.weight)}) '
          f'(sq_nonneg {poly_lean(t.square, names)}))')
    for i, k in enumerate(t.powers):
        for _ in range(k):
            s = f'({s} * {poly_lean(gs[i], names)})'
            pr = f'(mul_nonneg {pr} hg{i})'
    return s, pr


def cone_theorem(name: str, p: Poly, gs: Sequence[Poly], es: Sequence[Poly],
                 cert: ConeCertificate, names: Sequence[str] | None = None) -> str:
    """Emit a Lean proof for  gs >= 0, es = 0  |-  0 <= p.

    The certificate is re-checked here; a failure RAISES (p3) rather than
    asserting, so the guard survives `python -O`.
    """
    names = tuple(names) if names else tuple(f'x{i}' for i in range(p.n))
    if not check_cone(p, list(gs), list(es), cert):
        raise ValueError('refusing to emit Lean for an invalid cone certificate')
    text = _statement(name, p, gs, es, names)
    s, pr = '(0 : ℝ)', '(le_refl (0 : ℝ))'
    for i, t in enumerate(cert.terms):
        ti, pi = _nonneg_term(t, gs, names)
        text += f'  have ht{i} : 0 ≤ {ti} :=\n    {pi}\n'
        s = f'({s} + {ti})'
        pr = f'(add_nonneg {pr} ht{i})'
    text += f'  have hs : 0 ≤ {s} :=\n    {pr}\n'
    if es:
        ideal = '(' + ' + '.join(f'({poly_lean(h, names)} * {poly_lean(e, names)})'
                                 for h, e in zip(cert.equality_multipliers, es)) + ')'
        text += f'  have hi : {ideal} = 0 := by\n'
        text += ('    simp only [' + ', '.join([f'he{i}' for i in range(len(es))]
                                               + ['mul_zero', 'zero_mul', 'add_zero']) + ']\n')
        text += f'  have hid : {poly_lean(p, names)} = {s} + {ideal} := by ring\n'
        text += '  rw [hid, hi, add_zero]\n  exact hs\n\n'
    else:
        text += f'  calc\n    0 ≤ {s} := hs\n    _ = {poly_lean(p, names)} := by ring\n\n'
    return text


def invariant_theorem(name: str, cert: InvariantCertificate) -> str:
    """p5's orbit scaffolding for a conserved polynomial invariant."""
    if not check_invariant(cert):
        raise ValueError('refusing to emit Lean for an invalid invariant certificate')
    if cert.invariant.n != 2:
        raise ValueError('the emitted orbit scaffolding is binary-state only')
    vs = ['s.1', 's.2']
    inv = poly_lean(cert.invariant, vs)
    trans = '(' + ', '.join(poly_lean(p, vs) for p in cert.transition) + ')'
    init = '(' + ', '.join(rat(v) for v in cert.initial) + ')'
    return (f'def state_{name} : ℝ × ℝ := {init}\n'
            f'def step_{name} (s : ℝ × ℝ) : ℝ × ℝ :=\n  {trans}\n'
            f'def invariant_{name} (s : ℝ × ℝ) : ℝ :=\n  {inv}\n'
            f'theorem preserved_{name} (n : Nat) :\n'
            f'    invariant_{name} (orbit step_{name} state_{name} n) = 0 := by\n'
            f'  apply orbit_invariant step_{name} state_{name} invariant_{name}\n'
            f'  · norm_num [invariant_{name}, state_{name}]\n'
            f'  · intro s\n    dsimp [invariant_{name}, step_{name}]\n    ring\n\n')


def accumulator_theorem(name: str, r: Poly, cert: AccumulatorCertificate) -> str:
    """p7: `induction n generalizing a` for go(n+1,a) = go(n, a + r n)."""
    if not check_accumulator(r, cert):
        raise ValueError('refusing to emit Lean for an invalid accumulator certificate')
    func = 'acc_' + name
    rv = poly_lean(r, ['(n : ℚ)', 'a'], 'ℚ')
    fv = poly_lean(cert.invariant, ['(n : ℚ)', 'a'], 'ℚ')
    return (f'def {func} : ℕ → ℚ → ℚ\n  | 0, a => a\n'
            f'  | n + 1, a => {func} n (a + {rv})\n\n'
            f'theorem invariant_{name} (n : ℕ) (a : ℚ) :\n    {func} n a = {fv} := by\n'
            f'  induction n generalizing a with\n'
            f'  | zero => norm_num [{func}]\n'
            f'  | succ n ih =>\n    rw [{func}, ih]\n    push_cast <;> ring\n\n')


def _interval_basis(p: Poly, box: Box, names: Sequence[str]) -> str:
    coefficients = bernstein_coefficients(p, box)
    degrees = [max(beta[i] for beta in coefficients) for i in range(p.n)]
    terms = []
    for beta, c in coefficients.items():
        if not c:
            continue
        factors = []
        from math import comb
        for v, k, d, (l, u) in zip(names, beta, degrees, box):
            c *= Q(comb(d, k)) / (u - l) ** d
            if k:
                factors.append(f'({v} - ({number(l)})) ^ {k}')
            if d - k:
                factors.append(f'(({number(u)}) - {v}) ^ {d - k}')
        terms.append(f'({number(c)})' + ''.join(' * ' + s for s in factors))
    return ' +\n      '.join(terms) or '0'


def _branch_proof(p: Poly, box: Box, tree: BernsteinTree, names: Sequence[str],
                  level: int = 0, path: str = 'r') -> str:
    """p1's rcases branch emitter: one Lean case per box of the split tree."""
    pad = '  ' * level
    if isinstance(tree, BernsteinSplit):
        v = names[tree.axis]
        s = number(tree.point)
        left, right = split_box(box, tree.axis, tree.point)
        text = pad + f'rcases le_total {v} ({s}) with hs_{path} | hs_{path}\n'
        text += pad + '·\n' + _branch_proof(p, left, tree.left, names, level + 1, path + 'l')
        text += pad + '·\n' + _branch_proof(p, right, tree.right, names, level + 1, path + 'r')
        return text
    lines = []
    for i, (v, (l, u)) in enumerate(zip(names, box)):
        lines.append(pad + f'have lo_{path}_{i} : 0 ≤ {v} - ({number(l)}) := by linarith')
        lines.append(pad + f'have hi_{path}_{i} : 0 ≤ ({number(u)}) - {v} := by linarith')
    expr = _interval_basis(p, box, names).replace('\n', '\n' + pad)
    lines.append(pad + 'calc')
    lines.append(pad + f'  0 ≤ {expr} := by positivity')
    lines.append(pad + f'  _ = {p.lean(names)} := by ring')
    return '\n'.join(lines) + '\n'


def bernstein_theorem(name: str, p: Poly, box: Box, tree: BernsteinTree,
                      names: Sequence[str] | None = None) -> str:
    names = tuple(names) if names else tuple(f'x{i}' for i in range(p.n))
    if not check_bernstein(p, box, tree):
        raise ValueError('refusing to emit Lean for an invalid Bernstein certificate')
    hypotheses = ''.join(
        f' (h{v}l : {number(l)} ≤ {v}) (h{v}u : {v} ≤ {number(u)})'
        for v, (l, u) in zip(names, box))
    text = (f'theorem {name} ({" ".join(names)} : ℝ){hypotheses} :\n'
            f'    0 ≤ {p.lean(names)} := by\n')
    return text + _branch_proof(p, box, tree, names, 1) + '\n'
