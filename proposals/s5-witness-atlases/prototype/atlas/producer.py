"""Untrusted factorization/Bézout proposer using SymPy, with exact lifting.

The checker does not import this module. Root arithmetic is shared research code;
producer/checker separation does not imply independent arithmetic implementations.
"""
from __future__ import annotations
from itertools import combinations
from fractions import Fraction as Q
import sympy as sp
from . import exact as E
from . import polynomial as P
from .checker import evaluate_formula, fiber_product

x,y=sp.symbols('x y')


def sparse(expr) -> P.Poly2:
    poly=sp.Poly(expr,x,y,domain=sp.QQ)
    return {m:Q(int(c.p),int(c.q)) for m,c in poly.terms() if c}


def symbolic(poly: P.Poly2):
    return sum((sp.Rational(c.numerator,c.denominator)*x**i*y**j for (i,j),c in poly.items()), sp.S.Zero)


def problem(name: str, polys: list, formula, outer='forall',inner='exists') -> dict:
    return {'schema':'forge.atlas.problem/1','name':name,'outer':outer,'inner':inner,
            'polynomials':[P.encode(sparse(p)) for p in polys],'formula':formula}


def bezout(f,g) -> dict:
    a,b,h=sp.gcdex(f,g,y,domain=sp.QQ.frac_field(x))
    if sp.Poly(h,y).degree()!=0 or h==0:
        raise ValueError('noncoprime factors in Q(x)[y]')
    a,b=sp.cancel(a/h),sp.cancel(b/h)
    denominators=[]
    for poly in (sp.Poly(a,y),sp.Poly(b,y)):
        denominators += [sp.fraction(sp.cancel(c))[1] for c in poly.all_coeffs()]
    d=sp.Integer(1)
    for t in denominators:
        d=sp.lcm(d,t)
    a,b=sp.cancel(d*a),sp.cancel(d*b)
    guard=P.xpoly(sparse(d))
    return {'a':P.encode(sparse(a)), 'b':P.encode(sparse(b)), 'guard':P.encode_dense(guard)}


def rational_roots_sympy(p: tuple) -> list[E.Root]:
    if len(p)<=1:
        return []
    expr=sum(sp.Rational(a.numerator,a.denominator)*x**i for i,a in enumerate(p))
    intervals=sp.Poly(expr,x).intervals(eps=sp.Rational(1,16))
    roots=[]
    for (a,b),multiplicity in intervals:
        if multiplicity!=1:
            raise ValueError('projection was not square-free')
        roots.append(E.Root(p,Q(a),Q(b)))
    # SymPy may return touching isolating intervals; tighten them for the wire format.
    for a,b in zip(roots,roots[1:]):
        while a.hi>=b.lo:
            a.refine();b.refine()
    return roots


def produce(problem: dict) -> dict:
    originals=[symbolic(P.decode(p)) for p in problem['polynomials']]
    factors=[];factor_expr=[];factor_ids={};facts=[]
    for f in originals:
        c,parts=sp.factor_list(f,x,y)
        powers=[]
        for q,n in parts:
            q=sp.Poly(q,x,y,domain=sp.QQ)
            lc=q.LC(); q=sp.Poly(q.as_expr()/lc,x,y,domain=sp.QQ)
            c*=lc**n
            encoded=P.encode(sparse(q.as_expr()))
            key=tuple(tuple(row) for row in encoded)
            if key not in factor_ids:
                factor_ids[key]=len(factors);factors.append(encoded);factor_expr.append(q.as_expr())
            powers.append([factor_ids[key],int(n)])
        facts.append({'scalar':str(Q(c)),'powers':sorted(powers)})
    positive=[i for i,f in enumerate(factor_expr) if sp.Poly(f,y).degree()>0]
    deriv=[];cross=[]
    for i in positive:
        row=bezout(factor_expr[i],sp.diff(factor_expr[i],y));row['factor']=i;deriv.append(row)
    for i,j in combinations(positive,2):
        row=bezout(factor_expr[i],factor_expr[j]);row['pair']=[i,j];cross.append(row)
    decoded=[P.decode(f) for f in factors]
    guards=[P.xpoly(f) for f in decoded if P.y_degree(f)==0]
    guards += [P.leading_y(decoded[i]) for i in positive]
    guards += [P.decode_dense(r['guard']) for r in deriv+cross]
    projection_expr=sp.Integer(1)
    for g in guards:
        projection_expr=sp.lcm(projection_expr,
            sp.Poly(sum(sp.Rational(a.numerator,a.denominator)*x**i for i,a in enumerate(g)),x).sqf_part().as_expr())
    projection_sp=sp.Poly(projection_expr,x).monic()
    projection=E.trim(Q(projection_sp.nth(i)) for i in range(projection_sp.degree()+1))
    base=rational_roots_sympy(projection)
    base_samples=E.sector_samples(base)
    stacks=[]
    orig_decoded=[P.decode(p) for p in problem['polynomials']]
    for index in range(2*len(base)+1):
        sample=None
        if index%2==0:
            xx=base_samples[index//2];sample=str(xx)
        else:
            r=base[index//2];xx=r.lo if r.lo==r.hi else E.AField(r)
        fp=fiber_product(decoded,xx)
        roots=E.isolate_roots(fp)
        ys=E.sector_samples(roots)
        special=[E.coefficient_at_x(f,xx) for f in orig_decoded]
        signs=[]
        for j in range(2*len(roots)+1):
            row=([E.sign(E.evaluate(f,ys[j//2])) for f in special] if j%2==0
                 else [roots[j//2].sign_at(f) for f in special])
            signs.append(row)
        truths=[evaluate_formula(problem['formula'],s) for s in signs]
        value=any(truths) if problem['inner']=='exists' else all(truths)
        wanted=True if problem['inner']=='exists' else False
        needed=value if problem['inner']=='exists' else not value
        selection=truths.index(wanted) if needed else None
        stacks.append({'sample':sample,'y_roots':[r.descriptor() for r in roots],
                       'y_samples':[str(q) for q in ys],'signs':signs,'truths':truths,
                       'value':value,'selection':selection})
    values=[s['value'] for s in stacks]
    outer=problem['outer']
    closed=(all(values) if outer=='forall' else any(values)) if outer!='free' else None
    chosen=(values.index(outer=='exists') if (outer=='exists' and closed) or
            (outer=='forall' and closed is False) else None)
    return {'schema':'forge.atlas.certificate/1','factors':factors,'factorizations':facts,
            'derivative_guards':deriv,'pair_guards':cross,'projection':P.encode_dense(projection),
            'base_roots':[r.descriptor() for r in base],'stacks':stacks,
            'truth_by_x':values,'closed_value':closed,'selected_x':chosen}
