"""Replay saved prototype certificates without SciPy, SymPy, or floating point.

These are Python checks, not Lean kernel checks. Run:
    python prototype/replay.py results/certificates/*.json
Only small JSON packages in the documented formats are supported.
"""
from __future__ import annotations
import argparse
import json
from fractions import Fraction as Q
from pathlib import Path
from polynomial import Poly
from cone import Atom, ConeCertificate, check_cone
from bernstein import Leaf, Split, check_tree
from horn import Rule, Proof, check as check_horn
from induction import Term, Equation, Step, EqualityProof, InductionProof, Kernel, valid


def rational(s) -> Q:
    if not isinstance(s,str) or len(s)>1024: raise ValueError('Expected bounded rational string')
    return Q(s)


def poly(d) -> Poly:
    if type(d['n']) is not int or not 1<=d['n']<=8 or len(d['terms'])>10000:
        raise ValueError('Polynomial size limit')
    rows=[]
    for m,c in d['terms']:
        if any(type(e) is not int or not 0<=e<=64 for e in m): raise ValueError('Exponent limit')
        rows.append((tuple(m),rational(c)))
    return Poly.make(d['n'],rows)


def tree(d,depth=0):
    if depth>128: raise ValueError('Tree depth limit')
    if set(d)=={'leaf'}:
        v=d['leaf']
        return Leaf(tuple(v['degrees']),tuple(map(rational,v['coefficients'])))
    if set(d)=={'split'}:
        v=d['split']
        return Split(v['axis'],rational(v['cut']),tree(v['left'],depth+1),tree(v['right'],depth+1))
    raise ValueError('Unexpected tree node')


def term_json(t: Term) -> dict:
    return {'name':t.name,'sort':t.sort,'variable':t.variable,'args':[term_json(a) for a in t.args]}


def term(d,depth=0) -> Term:
    if depth>128 or type(d['variable']) is not bool: raise ValueError('Bad term')
    t=Term(d['name'],d['sort'],tuple(term(a,depth+1) for a in d['args']),d['variable'])
    if not valid(t): raise ValueError('Ill-sorted term')
    return t


def induction_json(e: Equation,p: InductionProof) -> dict:
    def steps(ss): return [{'path':list(s.path),'rule':s.rule,'after':term_json(s.after)} for s in ss]
    def equality(ep): return {'left':steps(ep.left),'right':steps(ep.right)}
    return {'equation':{'name':e.name,'lhs':term_json(e.lhs),'rhs':term_json(e.rhs)},
            'proof':{'subject':p.subject,'generalize':list(p.generalize),
                     'base':equality(p.base),'step':equality(p.step)}}


def parse_induction(row):
    d=row['equation']; e=Equation(d['name'],term(d['lhs']),term(d['rhs']))
    def equality(d):
        def steps(ds): return tuple(Step(tuple(v['path']),v['rule'],term(v['after'])) for v in ds)
        return EqualityProof(steps(d['left']),steps(d['right']))
    d=row['proof']
    p=InductionProof(d['subject'],tuple(d['generalize']),equality(d['base']),equality(d['step']))
    return e,p


def replay(d) -> bool:
    try:
        if d['kind']=='cone':
            hs=tuple(poly(h) for h in d['hypotheses'])
            c=ConeCertificate(tuple((rational(t['weight']),
                  Atom(poly(t['square']),tuple(t['hypotheses']))) for t in d['certificate']['terms']))
            return check_cone(poly(d['target']),hs,c)
        if d['kind']=='bernstein':
            box=tuple(tuple(map(rational,b)) for b in d['box'])
            if type(d['strict']) is not bool: return False
            return check_tree(poly(d['target']),box,tree(d['certificate']),strict=d['strict'])
        if d['kind']=='horn':
            rs=tuple(Rule(r['name'],tuple(r['premises']),r['conclusion']) for r in d['rules'])
            pf=Proof(tuple((r,c) for r,c in d['certificate']))
            return check_horn(frozenset(d['facts']),rs,d['target'],pf)
        if d['kind']=='induction_sequence':
            k=Kernel()
            for row in d['theorems']:
                e,p=parse_induction(row)
                k.install(e,p)
            return bool(d['theorems'])
    except (ValueError,TypeError,KeyError,IndexError,AttributeError,RecursionError):
        return False
    return False


def no_duplicates(pairs):
    d={}
    for k,v in pairs:
        if k in d: raise ValueError('Duplicate JSON key')
        d[k]=v
    return d


def main() -> int:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('files',nargs='+',type=Path)
    args=ap.parse_args()
    failed=False
    for f in args.files:
        try:
            if f.stat().st_size>20_000_000: raise ValueError('File limit')
            d=json.loads(f.read_text(),object_pairs_hook=no_duplicates)
            ok=replay(d)
        except (OSError,ValueError): ok=False
        print(('CHECKED_PYTHON' if ok else 'REJECTED')+' '+str(f))
        failed |= not ok
    return int(failed)

if __name__=='__main__': raise SystemExit(main())
