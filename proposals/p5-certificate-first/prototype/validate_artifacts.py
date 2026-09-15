"""Validate exported exact certificates, without importing discovery routines.
Usage: python validate_artifacts.py --results ../results
This is executable validation in Python, not Lean kernel checking.
"""
from __future__ import annotations
import argparse,json
from pathlib import Path
from fractions import Fraction as Q
from forge.polynomial import Poly
from forge.checkers import ConeTerm,ConeCertificate,InvariantCertificate,check_cone,check_invariant


def load_cone(record):
    c=record['certificate']
    cert=ConeCertificate(tuple(ConeTerm(Q(t['weight']),Poly.from_json(t['square']),tuple(t['factors']))
                              for t in c['terms']),tuple(Poly.from_json(p) for p in c['ideal']))
    return (Poly.from_json(record['target']),tuple(Poly.from_json(p) for p in record['nonnegative']),
            tuple(Poly.from_json(p) for p in record['equal_zero']),cert)


def load_invariant(record):
    return InvariantCertificate(Poly.from_json(record['invariant']),tuple(Q(v) for v in record['initial']),
                                tuple(Poly.from_json(p) for p in record['transition']))


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--results',type=Path,default=Path('../results'))
    a=parser.parse_args(); counts={}
    for filename,kind,load,check in [('cone_certificates.json','cone',load_cone,lambda x:check_cone(*x)),
                                    ('invariant_certificates.json','invariant',load_invariant,check_invariant)]:
        records=json.loads((a.results/filename).read_text())
        for r in records:
            if not check(load(r)):
                raise SystemExit('REJECTED: '+r['name'])
        counts[kind]=len(records)
    print(json.dumps({'status':'all_exported_certificates_accepted','counts':counts,
                      'checker':'Python exact rational arithmetic; not Lean'},indent=2))

if __name__=='__main__': main()
