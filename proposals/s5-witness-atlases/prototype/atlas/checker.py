"""Finite-premise checker for a plane sign atlas. No SymPy imports.

Acceptance audits the algebraic data needed by the atlas theorem in the article.
The theorem and this implementation have NOT been verified by the Lean kernel.
"""
from __future__ import annotations
from itertools import combinations
from fractions import Fraction as Q
from typing import Any
from . import exact as E
from . import polynomial as P

MAX_FACTORS = 32
MAX_CELLS = 4000
RELATIONS = {
    'eq': lambda s:s==0, 'ne':lambda s:s!=0,
    'lt':lambda s:s<0, 'le':lambda s:s<=0,
    'gt':lambda s:s>0, 'ge':lambda s:s>=0,
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def evaluate_formula(f: Any, signs: list[int], depth: int=0) -> bool:
    require(depth < 128, 'formula nesting limit')
    if type(f) is bool:
        return f
    require(isinstance(f,list) and len(f)>0 and isinstance(f[0],str), 'malformed formula')
    op = f[0]
    if op in RELATIONS:
        require(len(f)==2 and type(f[1]) is int and 0<=f[1]<len(signs),'invalid atom')
        return RELATIONS[op](signs[f[1]])
    if op=='not':
        require(len(f)==2,'invalid negation')
        return not evaluate_formula(f[1], signs, depth+1)
    if op=='implies':
        require(len(f)==3,'invalid implication')
        # Validate both sides, even when the first is false.
        a,b=(evaluate_formula(v,signs,depth+1) for v in f[1:])
        return (not a) or b
    require(op in ('and','or') and len(f)>=2,'invalid connective')
    values=[evaluate_formula(v,signs,depth+1) for v in f[1:]]
    return all(values) if op=='and' else any(values)


def problem_polynomials(problem: dict) -> list[P.Poly2]:
    require(isinstance(problem,dict) and problem.get('schema')=='forge.atlas.problem/1','problem schema')
    require(problem.get('outer') in ('forall','exists','free'),'outer quantifier')
    require(problem.get('inner') in ('forall','exists'),'inner quantifier')
    polys=[P.decode(p) for p in problem['polynomials']]
    require(len(polys)<=64,'too many atoms')
    evaluate_formula(problem['formula'],[0]*len(polys))
    return polys


def check_projection(problem: dict, cert: dict) -> tuple[list[P.Poly2],tuple]:
    polys=problem_polynomials(problem)
    require(cert.get('schema')=='forge.atlas.certificate/1','certificate schema')
    factors=[P.decode(p) for p in cert['factors']]
    require(len(factors)<=MAX_FACTORS,'too many factors')
    require(all(p and any(i+j>0 for i,j in p) for p in factors),'constant/zero factor')
    require(len({tuple(sorted(p.items())) for p in factors})==len(factors),'duplicate factors')
    facts=cert['factorizations']
    require(len(facts)==len(polys),'source factorization coverage')
    used=set()
    for original, f in zip(polys,facts):
        scalar=E.parse_q(f['scalar'])
        value={(0,0):scalar} if scalar else {}
        last=-1
        for pair in f['powers']:
            require(isinstance(pair,list) and len(pair)==2,'malformed factor power')
            k,n=pair
            require(type(k) is int and 0<=k<len(factors) and k>last,'factor index/order')
            require(type(n) is int and 1<=n<=64,'factor exponent')
            require(scalar!=0,'zero source uses extraneous factors')
            last=k; used.add(k)
            value=P.times(value,P.pow2(factors[k],n))
        require(value==original,'source factorization identity')
    require(used==set(range(len(factors))),'unused factor')
    positive_y=[i for i,f in enumerate(factors) if P.y_degree(f)>0]
    guards=[P.xpoly(f) for f in factors if P.y_degree(f)==0]
    guards += [P.leading_y(factors[i]) for i in positive_y]
    derivatives=cert['derivative_guards']
    require(all(type(r.get('factor')) is int for r in derivatives),'derivative index type')
    require([r.get('factor') for r in derivatives]==positive_y,'derivative coverage/order')
    for row in derivatives:
        i=row['factor']; a,b=P.decode(row['a']),P.decode(row['b'])
        g=P.decode_dense(row['guard'])
        require(bool(g),'zero derivative guard')
        lhs=P.plus(P.times(a,factors[i]),P.times(b,P.dy(factors[i])))
        require(lhs==P.from_x(g),'derivative Bezout identity')
        guards.append(g)
    expected=list(combinations(positive_y,2))
    cross=cert['pair_guards']
    actual=[]
    for r in cross:
        pair=r.get('pair')
        require(isinstance(pair,list) and len(pair)==2 and all(type(i) is int for i in pair),'pair indices')
        actual.append(tuple(pair))
    require(actual==expected,'pair coverage/order')
    for row,(i,j) in zip(cross,expected):
        a,b=P.decode(row['a']),P.decode(row['b']); g=P.decode_dense(row['guard'])
        require(bool(g),'zero pair guard')
        lhs=P.plus(P.times(a,factors[i]),P.times(b,factors[j]))
        require(lhs==P.from_x(g),'pair Bezout identity')
        guards.append(g)
    product=(Q(1),)
    for g in guards:
        require(bool(g),'zero projection guard')
        # Remove repeats before multiplying to limit avoidable degree growth.
        g=E.squarefree(g)
        product=E.monic(E.quotient(E.mul(product,g),E.gcd(product,g)))
    projection=E.squarefree(product)
    require(P.decode_dense(cert['projection'])==projection,'projection zero-set coverage')
    return factors,projection


def fiber_product(factors: list[P.Poly2], x: Q|E.AField) -> tuple:
    product=(Q(1),)
    for f in factors:
        p=E.coefficient_at_x(f,x)
        # Zero/constant specializations do not create y-root boundaries.
        if len(p)>1:
            product=E.mul(product,p)
    return E.squarefree(product)


def checked_selection(inner: str, truths: list[bool], selection: Any) -> bool:
    value=any(truths) if inner=='exists' else all(truths)
    desired=True if inner=='exists' else False
    needed=value if inner=='exists' else not value
    if needed:
        require(type(selection) is int and 0<=selection<len(truths),'missing/invalid fiber selection')
        require(truths[selection] is desired,'fiber selection has wrong truth')
    else:
        require(selection is None,'unexpected fiber selection')
    return value


def verify(problem: dict, cert: dict) -> dict:
    """Raise on invalid evidence, return exact Boolean audit results otherwise."""
    factors,projection=check_projection(problem,cert)
    originals=problem_polynomials(problem)
    base=E.verify_root_cover(projection,cert['base_roots'])
    stacks=cert['stacks']
    require(len(stacks)==2*len(base)+1 and len(stacks)<=MAX_CELLS,'base cell coverage')
    values=[]; total=0
    for index,stack in enumerate(stacks):
        if index%2==0:
            x=E.parse_q(stack['sample'])
            require(E.sample_in_sector(x,base,index//2),'x sample outside its base sector')
        else:
            require(stack.get('sample') is None,'section must use its algebraic base root')
            r=base[index//2]
            x=r.lo if r.lo==r.hi else E.AField(r)
        p=fiber_product(factors,x)
        roots=E.verify_root_cover(p,stack['y_roots'])
        samples=[E.parse_q(q) for q in stack['y_samples']]
        require(len(samples)==len(roots)+1,'y sector sample coverage')
        for k,s in enumerate(samples):
            require(E.sample_in_sector(s,roots,k),'y sample outside its sector')
        supplied=stack['signs']
        require(len(supplied)==2*len(roots)+1,'fiber sign-row coverage')
        special=[E.coefficient_at_x(f,x) for f in originals]
        truths=[]
        for j,row in enumerate(supplied):
            require(isinstance(row,list) and len(row)==len(originals)
                    and all(type(v) is int and v in (-1,0,1) for v in row),'malformed sign row')
            computed=([E.sign(E.evaluate(f,samples[j//2])) for f in special] if j%2==0
                      else [roots[j//2].sign_at(f) for f in special])
            require(row==computed,'incorrect sample sign')
            truths.append(evaluate_formula(problem['formula'],computed))
        require(stack['truths']==truths and all(type(t) is bool for t in stack['truths']),'incorrect fiber truth table')
        value=checked_selection(problem['inner'],truths,stack['selection'])
        require(type(stack['value']) is bool and stack['value']==value,'incorrect inner result')
        values.append(value);total+=len(truths)
        require(total<=MAX_CELLS,'total cell budget')
    outer=problem['outer']
    closed=(all(values) if outer=='forall' else any(values)) if outer!='free' else None
    require(cert['truth_by_x']==values and all(type(t) is bool for t in cert['truth_by_x']),'incorrect projected truth')
    require(cert['closed_value'] is closed,'incorrect closed verdict')
    chosen=cert['selected_x']
    needed=(outer=='exists' and closed is True) or (outer=='forall' and closed is False)
    if needed:
        require(type(chosen) is int and 0<=chosen<len(values),'missing outer witness/counterexample')
        require(values[chosen] is (outer=='exists'),'wrong outer selection')
    else:
        require(chosen is None,'unexpected outer selection')
    return {'accepted':True,'closed_value':closed,'truth_by_x':values,
            'base_cells':len(stacks),'plane_cells':total,
            'projection_degree':len(projection)-1,'selected_x':chosen}


def selector(stack: dict) -> dict|None:
    """Return a root-index strategy, NOT the rational sample reused for all x."""
    j=stack['selection']
    if j is None:
        return None
    n=len(stack['y_roots'])
    if j%2:
        return {'kind':'root','index':j//2}
    k=j//2
    if n==0:
        return {'kind':'constant','value':'0'}
    if k==0:
        return {'kind':'below','root':0,'offset':'1'}
    if k==n:
        return {'kind':'above','root':n-1,'offset':'1'}
    return {'kind':'midpoint','left':k-1,'right':k}
