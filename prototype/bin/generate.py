#!/usr/bin/env python3
"""Run every search family once and persist the accepted certificates.

This is the producing half of the pipeline: it MAY import NumPy, SciPy and SymPy.
The consuming half, bin/verify.py, must never import any of them, which is why
the two are separate programs. Nothing here decides whether a certificate is
valid -- every family self-checks with the exact checkers before being written.

Writes:
  results/certificates.json  -- replayed by `python -S bin/verify.py`
  results/lean/*.lean        -- emitted Lean sources, NOT compiled here
"""
from __future__ import annotations
import argparse
import json
import sys
from dataclasses import asdict
from fractions import Fraction as Q
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from forge.poly import Poly                                    # noqa: E402
from forge import bernstein, cone, horn, induction, sat  # noqa: E402
from forge.certificates import cone_json, tree_json  # noqa: E402
from forge.quadratic import quadratic_sos                      # noqa: E402
from forge.recurrence import (synthesize_recurrence, additive_invariant,  # noqa: E402
                              synthesize_accumulator)
from forge.univariate import univariate_search, univariate_json  # noqa: E402
from forge.witness import lattice, modular                     # noqa: E402
from forge.witness.affine import synthesize_affine_witness     # noqa: E402
from forge.io import lean                                      # noqa: E402


def box_json(b):
    return [[str(l), str(u)] for l, u in b]


def coefficient_tree_json(t):
    from forge.certificates import CoefficientLeaf
    if isinstance(t, CoefficientLeaf):
        return {'leaf': {'box': box_json(t.box), 'degrees': list(t.degrees),
                         'coefficients': [[list(k), str(c)] for k, c in t.coefficients]}}
    return {'split': {'box': box_json(t.box), 'axis': t.axis, 'cut': str(t.cut),
                      'left': coefficient_tree_json(t.left),
                      'right': coefficient_tree_json(t.right)}}


def horn_term_json(t):
    return {'symbol': t.symbol, 'args': [horn_term_json(a) for a in t.args]}


def horn_atom_json(a):
    return {'predicate': a.predicate, 'args': [horn_term_json(t) for t in a.args]}


def horn_rule_json(r):
    return {'name': r.name, 'head': horn_atom_json(r.head),
            'body': [horn_atom_json(a) for a in r.body]}


def horn_cert_json(c):
    return {'nodes': [{'conclusion': horn_atom_json(n.conclusion), 'rule': n.rule,
                       'substitution': [[k, horn_term_json(v)] for k, v in n.substitution],
                       'premises': list(n.premises)} for n in c.nodes],
            'root': c.root}


def build() -> list[dict]:
    records: list[dict] = []
    x, y = Poly.var(2, 0), Poly.var(2, 1)
    u = Poly.var(1, 0)

    # --- quadratic Schur complement (p1 + p3) ------------------------------
    p = 3 * (x - 2 * y + 1) ** 2 + 2 * (2 * x + y - 3) ** 2 + Q(1, 7) * (x + y) ** 2
    cert = quadratic_sos(p)
    records.append({'id': 'hidden_quadratic', 'family': 'Quadratic SOS',
                    'input': {'p': p.json()}, 'certificate': cone_json(cert)})

    # --- finite cone LP with an equality ideal (p5 + p7 + p8) --------------
    target = x * x + y * y - Q(1, 2)
    equalities = (x + y - 1,)
    result = cone.discover(target, (), equalities, degree=2)
    if result.status != 'proved':
        raise RuntimeError('cone search regression: ' + result.reason)
    records.append({'id': 'equality_constrained', 'family': 'Finite cone LP',
                    'input': {'p': target.json(),
                              'equalities': [e.json() for e in equalities]},
                    'certificate': cone_json(result.certificate)})

    target2 = x * y
    ge = (x, y)
    result2 = cone.discover(target2, ge, degree=2)
    if result2.status != 'proved':
        raise RuntimeError('guarded cone search regression: ' + result2.reason)
    records.append({'id': 'guard_product', 'family': 'Finite cone LP',
                    'input': {'p': target2.json(),
                              'inequalities': [g.json() for g in ge]},
                    'certificate': cone_json(result2.certificate)})

    # --- Bernstein, both tree shapes (p8/p3/p2 search, p1/p5 checkers) -----
    motzkin = x ** 4 * y ** 2 + x ** 2 * y ** 4 - 3 * x * x * y * y + 1 + Q(1, 16)
    mbox = ((Q(-2), Q(2)),) * 2
    tree = bernstein.bernstein_search(motzkin, mbox, max_depth=14)
    if tree is None:
        raise RuntimeError('Bernstein search regression')
    records.append({'id': 'motzkin_box', 'family': 'Bernstein box',
                    'input': {'p': motzkin.json(), 'box': box_json(mbox)},
                    'certificate': tree_json(tree)})

    q = (u - Q(1, 3)) ** 2 + Q(1, 100)
    ubox = ((Q(0), Q(1)),)
    ctree = bernstein.discover_coefficient_tree(q, ubox, depth=6)
    if ctree is None:
        raise RuntimeError('coefficient tree regression')
    records.append({'id': 'shifted_square_box', 'family': 'Bernstein expansion',
                    'input': {'p': q.json(), 'box': box_json(ubox)},
                    'certificate': coefficient_tree_json(ctree)})

    # --- recurrences and invariants (p1 + p2 + p7 + p5) --------------------
    for power in range(5):
        step = u ** power
        formula = synthesize_recurrence(step, Poly.const(1, 0), power + 1)
        if formula is None:
            raise RuntimeError('recurrence regression at power %d' % power)
        records.append({'id': 'power_sum_%d' % power, 'family': 'Polynomial recurrence',
                        'input': {'step': step.json(),
                                  'initial': Poly.const(1, 0).json()},
                        'certificate': formula.json()})

    invariant = additive_invariant((u + 1) ** 3)
    records.append({'id': 'cubic_accumulator', 'family': 'Conserved invariant',
                    'input': {},
                    'certificate': {'invariant': invariant.invariant.json(),
                                    'initial': [str(v) for v in invariant.initial],
                                    'transition': [t.json() for t in invariant.transition]}})

    # --- affine / lattice / modular witnesses (p1, p2, p7, p4) -------------
    A, B, c = [[1, 2], [0, 1]], [[3, -1], [2, 4]], [5, -3]
    w = synthesize_affine_witness(A, B, c, True)
    records.append({'id': 'integral_affine', 'family': 'Integral affine witness',
                    'input': {'A': A, 'B': B, 'c': c},
                    'certificate': {'linear': [[str(v) for v in row] for row in w.linear],
                                    'offset': [str(v) for v in w.offset]}})

    for name, mat, rhs in [('bezout_6_10', [[6, 10]], [2]),
                           ('coupled_system', [[6, 10, 15], [2, -4, 3]], [7, -1])]:
        lc = lattice.solve(mat, rhs)
        if not lattice.check(mat, rhs, lc):
            raise RuntimeError('lattice regression: ' + name)
        records.append({'id': name, 'family': 'Integer lattice',
                        'input': {'A': mat, 'b': rhs}, 'certificate': asdict(lc)})

    mcert = modular.synthesize(3, 1, 5)
    records.append({'id': 'residue_3_1_mod_5', 'family': 'Modular witness',
                    'input': {'a': 3, 'b': 1, 'm': 5}, 'certificate': mcert})

    # --- univariate with even-multiplicity zeros (p1, verbatim family) -----
    poly_u = (u - Q(1, 3)) ** 2 * (u * u + Q(1, 7)) * (u + 2) * (2 - u)
    ucert = univariate_search(poly_u, Q(-2), Q(2))
    if ucert is None:
        raise RuntimeError('univariate regression')
    records.append({'id': 'double_root', 'family': 'Univariate with zeros',
                    'input': {'p': poly_u.json(), 'interval': ['-2', '2']},
                    'certificate': univariate_json(ucert)})

    # --- Horn proof DAG (p5 + p8 + p9 + p3) --------------------------------
    facts, rules, goal = horn.chain_problem(8, 5)
    hr = horn.demand_prove(facts, rules, goal)
    if hr.status != 'proved':
        raise RuntimeError('horn regression')
    records.append({'id': 'chain_8_decoys_5', 'family': 'Horn proof',
                    'input': {'facts': [horn_atom_json(a) for a in facts],
                              'rules': [horn_rule_json(r) for r in rules],
                              'goal': horn_atom_json(goal)},
                    'certificate': horn_cert_json(horn.minimize(hr.certificate))})

    # --- structural induction (p4 + p2 + p9) -------------------------------
    bank, stats = induction.synthesize_accumulator()
    if stats.get('status') != 'certified':
        raise RuntimeError('induction regression: ' + str(stats))
    first = next(iter(bank.certificates))
    lhs, rhs, cert = bank.certificates[first]
    records.append({'id': first, 'family': 'List induction',
                    'input': {'lhs': lhs.json(), 'rhs': rhs.json()},
                    'certificate': cert})
    records.append({'id': 'revAcc_bank', 'family': 'Induction bank', 'input': {},
                    'certificate': {
                        'lemmas': [{'name': name, 'lhs': l.json(), 'rhs': r.json(),
                                    'certificate': c} for name, (l, r, c)
                                   in bank.certificates.items()],
                        'specialization': stats['specialization']}})
    _, lemma_records = induction.synthesize_lemmas()
    records.append({'id': 'signature_lemmas', 'family': 'Lemma bundle',
                    'input': {'required': ['app_right_id', 'app_assoc', 'rev_app']},
                    'certificate': lemma_records})

    # --- CDCL(T), both proof modes (p6 + p4) -------------------------------
    atoms = {1: sat.DiffAtom(0, 1, 0), 2: sat.DiffAtom(1, 2, 0), 3: sat.DiffAtom(2, 0, -1)}
    clauses = [[1], [2], [3]]
    solver = sat.Solver(3, clauses, atoms)
    if solver.solve() is not False:
        raise RuntimeError('IDL solver regression')
    if not sat.replay(3, solver.original, atoms, solver.proof):
        raise RuntimeError('IDL proof regression')
    records.append({'id': 'idl_negative_cycle', 'family': 'CDCL(T) refutation',
                    'input': {'n': 3, 'clauses': [list(c) for c in solver.original],
                              'atoms': {str(k): asdict(v) for k, v in atoms.items()}},
                    'certificate': solver.proof})

    holes = sat.pigeonhole(4, 3)
    res = sat.solve_resolution(holes)
    if res['status'] != 'unsat' or not sat.verify_resolution(holes, {}, None, res):
        raise RuntimeError('resolution proof regression')
    records.append({'id': 'pigeonhole_4_3', 'family': 'CDCL(T) resolution refutation',
                    'input': {'clauses': holes, 'atoms': {}, 'nodes': None},
                    'certificate': {'status': res['status'], 'proof': res['proof'],
                                    'root': res['root']}})
    return records


def emit_lean(out: Path) -> int:
    out.mkdir(parents=True, exist_ok=True)
    x, y = Poly.var(2, 0), Poly.var(2, 1)
    u = Poly.var(1, 0)
    text = lean.HEADER
    p = 3 * (x - 2 * y + 1) ** 2 + 2 * (2 * x + y - 3) ** 2 + Q(1, 7) * (x + y) ** 2
    text += lean.cone_theorem('hidden_quadratic', p, (), (), quadratic_sos(p), ['x', 'y'])
    target = x * x + y * y - Q(1, 2)
    es = (x + y - 1,)
    text += lean.cone_theorem('equality_constrained', target, (), es,
                              cone.discover(target, (), es, degree=2).certificate, ['x', 'y'])
    text += lean.FOOTER
    (out / 'Certificates.lean').write_text(text, encoding='utf-8')

    q = (u - Q(1, 4)) ** 2 + Q(1, 50)
    qbox = ((Q(0), Q(1)),)
    tree = bernstein.bernstein_search(q, qbox, max_depth=8)
    text = lean.HEADER + lean.bernstein_theorem('shifted_square_box', q, qbox, tree, ['x'])
    text += lean.FOOTER
    (out / 'Bernstein.lean').write_text(text, encoding='utf-8')

    text = lean.HEADER + lean.ORBIT_PREAMBLE
    text += lean.invariant_theorem('cubic', additive_invariant((u + 1) ** 3))
    acc, _ = synthesize_accumulator(Poly.var(2, 0) ** 2)
    text += lean.accumulator_theorem('square', Poly.var(2, 0) ** 2, acc)
    text += lean.FOOTER
    (out / 'Invariants.lean').write_text(text, encoding='utf-8')
    return 3


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out', type=Path, default=ROOT / 'results')
    args = ap.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    records = build()
    (args.out / 'certificates.json').write_text(
        json.dumps(records, indent=1, sort_keys=True) + '\n', encoding='utf-8')
    files = emit_lean(args.out / 'lean')
    print('wrote %d certificates and %d uncompiled Lean files to %s'
          % (len(records), files, args.out))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
