"""One-parameter quantified closure by a complete exact sign-cell cover.

A root interval is a *section*, not a sample standing in for its neighboring
sectors. The independently supplied problem determines the quantifier and
condition. No search module is imported.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from .exact import P, Reject, Limit, integer, poly, rat, qjson, sgn
from .checker import verify
from .logic import RELS
from .sturm import from_sparse, root_product, root_count, ev


def validate_condition(f,m,depth=0):
    if depth>40:raise Limit('outer formula depth')
    if not isinstance(f,list) or not f:raise Reject('outer formula')
    op=f[0]
    if op in ('true','false'):
        if len(f)!=1:raise Reject('outer literal arity')
    elif op=='atom':
        if len(f)!=3 or f[2] not in RELS:raise Reject('outer atom')
        integer(f[1],0,m-1)
    elif op=='count':
        if len(f)!=3 or f[1] not in RELS:raise Reject('count test')
        integer(f[2],0,12)
    elif op=='not':
        if len(f)!=2:raise Reject('outer not')
        validate_condition(f[1],m,depth+1)
    elif op in ('and','or','implies','iff'):
        if len(f)!=3:raise Reject('outer connective')
        validate_condition(f[1],m,depth+1);validate_condition(f[2],m,depth+1)
    else:raise Reject('outer operator')


def eval_condition(f,count,signs):
    op=f[0]
    if op=='true':return True
    if op=='false':return False
    if op=='atom':return bool(RELS[f[2]](signs[f[1]]))
    if op=='count':return bool(RELS[f[1]](sgn(count-f[2])))
    if op=='not':return not eval_condition(f[1],count,signs)
    a,b=eval_condition(f[1],count,signs),eval_condition(f[2],count,signs)
    return {'and':a and b,'or':a or b,'implies':not a or b,'iff':a==b}[op]


def parse_outer(problem):
    if not isinstance(problem,dict) or set(problem)!={'schema','fiber','parameter_atoms','condition','quantifier'}:
        raise Reject('outer problem keys')
    if problem['schema']!='outer-one-parameter-v1':raise Reject('outer problem schema')
    if problem['quantifier'] not in ('forall','exists'):raise Reject('outer quantifier')
    if not isinstance(problem['parameter_atoms'],list) or len(problem['parameter_atoms'])>12:raise Reject('outer atoms')
    atoms=[poly(p,1) for p in problem['parameter_atoms']]
    validate_condition(problem['condition'],len(atoms))
    return atoms


@dataclass
class CheckedOuter:
    value:bool
    cells:list
    root_degree:int
    decisive_cell:int|None


def verify_outer(problem,certificate):
    atoms=parse_outer(problem)
    if not isinstance(certificate,dict) or set(certificate)!={'schema','fiber_certificate','roots','claim'}:
        raise Reject('outer certificate keys')
    if certificate['schema']!='outer-sign-cover-v1' or type(certificate['claim']) is not bool:
        raise Reject('outer certificate schema or claim')
    cf=verify(problem['fiber'],certificate['fiber_certificate'])
    if cf.fiber.k!=1:raise Reject('outer closure requires exactly one parameter')
    support=cf.support()+atoms
    P0=root_product(support)
    roots=certificate['roots']
    if not isinstance(roots,list) or len(roots)>160:raise Limit('root count cap')
    intervals=[]
    for pair in roots:
        if not isinstance(pair,list) or len(pair)!=2:raise Reject('root isolator')
        l,r=map(rat,pair)
        if l>=r or (intervals and intervals[-1][1]>=l):raise Reject('overlapping or unordered isolators')
        if root_count(P0,l,r)!=1:raise Reject('not exactly one distinct root')
        intervals.append((l,r))
    if len(intervals)!=root_count(P0):raise Reject('incomplete real-line boundary cover')
    cells=[]
    def record(sign_of,description):
        count=cf.count_by_sign(sign_of)
        signs=[sign_of(p) for p in atoms]
        truth=eval_condition(problem['condition'],count,signs)
        cells.append({**description,'count':count,'parameter_atom_signs':signs,'condition':truth})
    def at(t):return lambda p:sgn(p.eval([t]))
    if not intervals:
        record(at(Q(0)),{'kind':'sector','sample':qjson(Q(0))})
    else:
        record(at(intervals[0][0]-1),{'kind':'sector','sample':qjson(intervals[0][0]-1)})
        for i,(l,r) in enumerate(intervals):
            def sign_at_root(p):
                a=from_sparse(p)
                if len(a)<2:return sgn(a[0]) if a else 0
                # Every zero of a is a zero of P0, and this isolator has one P0 root.
                return 0 if root_count(a,l,r)==1 else sgn(ev(a,(l+r)/2))
            record(sign_at_root,{'kind':'section','isolator':[qjson(l),qjson(r)]})
            t=(r+intervals[i+1][0])/2 if i+1<len(intervals) else r+1
            record(at(t),{'kind':'sector','sample':qjson(t)})
    quantifier=problem['quantifier']
    value=all(c['condition'] for c in cells) if quantifier=='forall' else any(c['condition'] for c in cells)
    if certificate['claim']!=value:raise Reject('quantified verdict mismatch')
    decisive=next((i for i,c in enumerate(cells) if c['condition']==(quantifier=='exists')),None)
    return CheckedOuter(value,cells,len(P0)-1,decisive)
