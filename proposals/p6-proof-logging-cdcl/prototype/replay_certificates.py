#!/usr/bin/env python3
"""Replay saved SAT, polynomial and induction certificates without search libraries.

Uses Python's standard library only. In particular, induction certificates are
checked with sparse Fraction-polynomial substitution independently of the SymPy
implementation used by the synthesis oracle. This is not Lean kernel checking.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import json
from pathlib import Path
from cdcl_idl import DiffAtom, replay
from polynomial import Poly, check_certificate, variables


def substitute(p: Poly, replacements: list[Poly]) -> Poly:
    if len(replacements) != p.n:
        raise ValueError('substitution arity mismatch')
    out = Poly.constant(p.n, 0)
    for monomial, coefficient in p.terms.items():
        term = Poly.constant(p.n, coefficient)
        for replacement, exponent in zip(replacements, monomial):
            term = term * replacement**exponent
        out = out + term
    return out


def check_induction(power: int, coefficients: list) -> bool:
    if type(power) is not int or power < 0:
        return False
    q = Poly.decode({'n': 2, 'terms': coefficients})
    n, a = variables(2)
    base = substitute(q, [Poly.constant(2, 0), a]) - a
    step = substitute(q, [n+1, a]) - substitute(q, [n, a+(n+1)**power])
    return not base.terms and not step.terms


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--results', type=Path, default=Path('results'))
    args = ap.parse_args()
    counts = {'sat_certificates': 0, 'polynomial_certificates': 0,
              'induction_certificates': 0, 'induction_mutations_rejected': 0,
              'unknown_search_results_skipped': 0}
    for path in sorted(args.results.glob('*.json')):
        if path.name in {'summary.json', 'replay-summary.json'}:
            continue
        data = json.loads(path.read_text(encoding='utf-8'))
        if 'proof' in data and 'clauses' in data:
            atoms = {int(k): DiffAtom(**v) for k, v in data['atoms'].items()}
            if not replay(data['n'], data['clauses'], atoms, data['proof']):
                raise RuntimeError(f'invalid SAT certificate: {path.name}')
            counts['sat_certificates'] += 1
        elif 'certificate' in data and 'target' in data:
            if data['certificate'] is None:
                counts['unknown_search_results_skipped'] += 1
                continue
            if not check_certificate(Poly.decode(data['target']),
                    [Poly.decode(x) for x in data['nonnegative_assumptions']],
                    [Poly.decode(x) for x in data['equality_assumptions']],
                    data['certificate']):
                raise RuntimeError(f'invalid polynomial certificate: {path.name}')
            counts['polynomial_certificates'] += 1
        elif 'invariant_coefficients' in data:
            cs = data['invariant_coefficients']
            power = data['result']['power']
            if not check_induction(power, cs):
                raise RuntimeError(f'invalid induction certificate: {path.name}')
            q = Poly.decode({'n': 2, 'terms': cs})
            n, _ = variables(2)
            for wrong in [q+1, q+n]:
                if check_induction(power, wrong.encode()['terms']):
                    raise RuntimeError('accepted a mutated induction certificate')
                counts['induction_mutations_rejected'] += 1
            counts['induction_certificates'] += 1
    # Fail rather than succeed vacuously on a mistyped or empty result directory.
    if any(counts[k] == 0 for k in ['sat_certificates', 'polynomial_certificates',
                                   'induction_certificates']):
        raise RuntimeError('missing required certificate families')
    print(json.dumps({'all_saved_certificates_valid': True,
                      'verification_dependencies': 'Python standard library only',
                      **counts}, indent=2))

if __name__ == '__main__':
    main()
