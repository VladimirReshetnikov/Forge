"""Replay all archived certificates using Python's standard library only.

No discovery function, SciPy optimizer, SymPy routine, external executable, or
Lean runtime is called. This is a software checker, not a Lean kernel check.
"""
from __future__ import annotations
import argparse
from collections import Counter
from fractions import Fraction
import json
from pathlib import Path
import sys
from polynomial import Poly
import sos, lattice, induction, horn


def load_sos(obj):
    p = obj['problem']
    problem = sos.Problem(Poly.from_json(p['target']),
                          tuple(Poly.from_json(x) for x in p['ge']),
                          tuple(Poly.from_json(x) for x in p['eq']))
    c = obj['certificate']
    cert = sos.Certificate(tuple((Fraction(t['weight']), sos.Atom(
        Poly.from_json(t['square']), tuple(t['assumptions']))) for t in c['positive']),
        tuple((t['equality'], Poly.from_json(t['multiplier'])) for t in c['ideal']))
    return problem, cert


def verify(obj):
    kind = obj['kind']
    if kind == 'sos':
        return sos.check(*load_sos(obj))
    if kind == 'lattice':
        c = obj['certificate']
        steps = tuple(lattice.Step(s['row'], tuple(map(tuple, s['transform'])),
                     s['gcd'], s['residual'], s['quotient'], s['obstruction'])
                     for s in c['steps'])
        cert = lattice.Certificate(c['feasible'], steps, tuple(c['witness']),
                                   tuple(map(tuple, c['basis'])))
        return lattice.check(obj['matrix'], obj['rhs'], cert)
    if kind == 'induction':
        c = obj['certificate']
        return induction.check(Poly.from_json(obj['increment']), induction.Certificate(
            Poly.from_json(c['invariant']), tuple(c['generalized'])))
    if kind == 'horn':
        rules = [horn.Rule(tuple(r['premises']), r['conclusion']) for r in obj['rules']]
        proof = [horn.Step(s['rule'], s['conclusion']) for s in obj['proof']]
        return horn.check(rules, obj['target'], proof)
    raise ValueError(f'Unknown certificate kind: {kind!r}')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('directory', nargs='?', type=Path,
                    default=Path(__file__).resolve().parents[1]/'results'/'certificates')
    args = ap.parse_args()
    paths = sorted(args.directory.glob('*.json'))
    if not paths:
        print('No certificates found.', file=sys.stderr); return 2
    counts = Counter(); failed = []
    for p in paths:
        try:
            obj = json.loads(p.read_text(encoding='utf-8'))
            if not verify(obj): raise ValueError('certificate rejected')
            counts[obj['kind']] += 1
        except (KeyError, ValueError, TypeError, IndexError, OverflowError) as exc:
            failed.append({'file': p.name, 'error': str(exc)})
    print(json.dumps({'checker': 'stdlib-only Python; not Lean',
                      'accepted': dict(counts), 'total': sum(counts.values()),
                      'failed': failed}, indent=2))
    return int(bool(failed))

if __name__ == '__main__': sys.exit(main())
