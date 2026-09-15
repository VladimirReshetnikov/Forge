#!/usr/bin/env python3
"""Replay persisted certificates using only Python's standard library.

Not a Lean kernel checker. Never imports SciPy, NumPy, SymPy, or search engines.
Accepted statements are conditional on the explicit premise/guard inventory.
JSON is treated as data, never executed. The generated-file workflow assumes
modest input sizes; this is not a hardened network certificate service.
"""
from pathlib import Path
import sys, json
from fractions import Fraction as Q
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from forge_lab.poly import Poly, ConeCertificate, ConeTerm, BoxCertificate, check_cone, check_box
from forge_lab.terms import T, Step, DEFINITIONS, replay, well_typed
from forge_lab.induction import EqGoal, InductionCertificate, TheoremBank
from forge_lab.horn import Atom, HornRule, Node, check_horn

def poly(o):
    if type(o['variables']) is not int: raise ValueError('invalid dimension')
    terms=[(tuple(m),Q(c)) for m,c in o['terms']]
    if len(dict(terms))!=len(terms): raise ValueError('duplicate polynomial terms')
    return Poly.make(o['variables'],dict(terms))

def cone(o):
    if o['kind']!='nonnegative_cone': raise ValueError('wrong certificate')
    return ConeCertificate(tuple(ConeTerm(Q(t['weight']),poly(t['square']),tuple(t['guards'])) for t in o['terms']))

def boxcert(o):
    if o['kind']=='leaf': return BoxCertificate(lower=Q(o['lower']))
    if o['kind']!='split': raise ValueError('wrong box node')
    return BoxCertificate(axis=o['axis'],split=Q(o['point']),left=boxcert(o['left']),right=boxcert(o['right']))

def term(o):
    t=T(o['symbol'],tuple(term(a) for a in o['args']),o['sort'])
    if not well_typed(t): raise ValueError('ill-sorted term')
    return t

def steps(xs): return tuple(Step(tuple(s['path']),s['rule']) for s in xs)
def goal(o): return EqGoal(term(o['lhs']),term(o['rhs']))
def atom(o): return Atom(o['predicate'],term(o['argument']))

def verify(o):
    kind=o['kind']
    if kind=='cone':
        return check_cone(poly(o['target']),tuple(poly(g) for g in o['guards']),cone(o['certificate']))
    if kind=='box':
        if type(o['strict']) is not bool: return False
        return check_box(poly(o['target']),tuple(tuple(Q(v) for v in row) for row in o['box']),boxcert(o['certificate']),o['strict'])
    if kind=='witness':
        w=poly(o['witness'])
        if w.n!=1: return False
        x=Poly.var(1,0)
        return check_cone(w-x,(),cone(o['minus'])) and check_cone(w+x,(),cone(o['plus']))
    if kind=='horn':
        rs=tuple(HornRule(r['name'],tuple(atom(a) for a in r['body']),atom(r['head'])) for r in o['rules'])
        trace=tuple(Node(atom(n['fact']),n['rule'],tuple(n['parents'])) for n in o['proof'])
        return check_horn(atom(o['goal']),tuple(atom(a) for a in o['facts']),rs,trace)
    if kind=='theorem_bank':
        bank=TheoremBank()
        for l in o['lemmas']:
            c=l['certificate']; cases=c['cases']
            if c['kind']!='list_induction': return False
            cert=InductionCertificate(c['variable'],tuple(c['generalized']),
                *(steps(cases[k]) for k in ('nil_left','nil_right','cons_left','cons_right')))
            if not bank.add(l['name'],goal(l['goal']),cert): return False
        s=o['specialization']; g=goal(s['goal'])
        rules={r.name:r for r in DEFINITIONS+bank.rules}
        a=replay(g.lhs,steps(s['left']),rules); b=replay(g.rhs,steps(s['right']),rules)
        return a is not None and a==b
    raise ValueError('unknown certificate kind')

def main():
    path=Path(sys.argv[1]) if len(sys.argv)>1 else ROOT/'results/certificates.json'
    try:
        records=json.loads(path.read_text())
        for i,o in enumerate(records):
            if not verify(o): raise ValueError(f'certificate {i} rejected')
        print(f'{len(records)} persisted certificate bundles replayed successfully (Python exact checkers; NOT Lean).')
    except (KeyError,ValueError,TypeError,IndexError,RecursionError) as e:
        print('REJECTED:',e,file=sys.stderr); sys.exit(1)

if __name__=='__main__': main()
