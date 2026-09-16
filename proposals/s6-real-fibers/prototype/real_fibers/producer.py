"""Untrusted SymPy producer; deliberately not imported by the replay package.

It uses a Groebner normal form, multiplication matrices, and SymPy's
characteristic polynomial. Replay uses triangular substitution, direct trace
entries, and Newton identities instead. Representation code is shared.
"""
from __future__ import annotations
from itertools import product
from fractions import Fraction as Q
import sympy as s
from .exact import P, qjson
from .checker import Fiber
from .logic import eval_formula


def symbols_for(k,n):
    return tuple(s.symbols(f't0:{k}')),tuple(s.symbols(f'x0:{n}'))


def expr(p,variables):
    return s.Add(*(s.Rational(c.numerator,c.denominator)*s.Mul(*(x**a for x,a in zip(variables,e)))
                   for e,c in p.terms))


def sparse(a,variables):
    a=s.expand(a)
    if not variables:
        a=s.Rational(a)
        return P.const(0,Q(int(a.p),int(a.q)))
    p=s.Poly(a,*variables,domain=s.QQ)
    return P.make(len(variables),[(tuple(e),Q(int(c.p),int(c.q))) for e,c in p.terms()])


def make_problem(parameters,variables,equations,atoms,formula):
    allvars=tuple(parameters)+tuple(variables)
    return {'schema':'forge-real-fiber-v1','parameters':len(parameters),
            'degrees':[int(s.degree(f,x)) for f,x in zip(equations,variables)],
            'equations':[sparse(f,allvars).data() for f in equations],
            'atoms':[sparse(q,allvars).data() for q in atoms], 'formula':formula}


def truth_table_indicator(formula,m):
    """Independent producer algorithm: tensor Lagrange interpolation on sign cube."""
    zs=tuple(s.symbols(f'z0:{m}'))
    out=s.Integer(0)
    for signs in product((-1,0,1),repeat=m):
        if eval_formula(formula,signs):
            factor=s.Integer(1)
            for z,v in zip(zs,signs):
                factor *= (1-z*z) if v==0 else (z*z+v*z)/2
            out+=factor
    return sparse(out,zs)


def produce(problem):
    f=Fiber.parse(problem)  # schema/admission only, not replay algorithms
    ts,xs=symbols_for(f.k,f.n);variables=ts+xs
    fs=[expr(p,variables) for p in f.fs];qs=[expr(p,variables) for p in f.qs]
    domain=s.QQ.poly_ring(*ts) if ts else s.QQ
    G=s.groebner(fs,*reversed(xs),order='lex',domain=domain)
    bs=[s.Mul(*(x**e for x,e in zip(xs,b))) for b in f.basis]
    def normal(a):return G.reduce(s.expand(a))[1]
    def coordinates(a):
        a=s.Poly(normal(a),*xs)
        return s.Matrix([a.coeff_monomial(b) for b in bs])
    def mult(a):return s.Matrix.hstack(*(coordinates(a*b) for b in bs))
    H1=s.Matrix(f.d,f.d,lambda i,j:s.trace(mult(bs[i]*bs[j])))
    terms=truth_table_indicator(f.formula,len(qs)).terms
    rows=[]
    for e,c in terms:
        w=s.Mul(*(q**j for q,j in zip(qs,e)))
        H=s.simplify(H1*mult(w))
        cs=H.charpoly().all_coeffs()
        rows.append({'exponents':list(e),'coefficient':qjson(c),
                     'hermite':[[sparse(H[i,j],ts).data() for j in range(f.d)] for i in range(f.d)],
                     'charpoly':[sparse(a,ts).data() for a in cs]})
    return {'schema':'hermite-charpoly-v1','queries':rows}


def isolators(polynomial,variable,epsilon=s.Rational(1,1024)):
    """Get disjoint open isolators, expanding rational singleton roots safely."""
    p=s.Poly(polynomial,variable,domain=s.QQ).sqf_part()
    if p.degree()<1:return []
    raw=[(Q(int(a.p),int(a.q)),Q(int(b.p),int(b.q))) for (a,b),mult in s.intervals(p,eps=epsilon)]
    out=[]
    for i,(a,b) in enumerate(raw):
        if a==b:
            delta=Q(1,1024)
            if i:delta=min(delta,(a-raw[i-1][1])/4)
            if i+1<len(raw):delta=min(delta,(raw[i+1][0]-a)/4)
            if delta<=0:raise ValueError('root isolation did not separate neighbors')
            a,b=a-delta,b+delta
        out.append([qjson(a),qjson(b)])
    return out


def produce_outer(problem):
    from .outer import verify_outer,parse_outer
    from .checker import verify
    from .sturm import root_product,to_sparse
    atoms=parse_outer(problem)
    cert=produce(problem['fiber']);checked=verify(problem['fiber'],cert)
    # This producer reuses the product assembler; replay recomputes the product.
    # Isolation itself is SymPy; replay constructs an exact Sturm chain separately.
    p=root_product(checked.support()+atoms)
    t=s.Symbol('t')
    roots=isolators(expr(to_sparse(p),(t,)),t)
    out={'schema':'outer-sign-cover-v1','fiber_certificate':cert,'roots':roots,'claim':False}
    # The verdict is cheap to recompute; a separate checker owns acceptance.
    try:verify_outer(problem,out)
    except ValueError as e:
        if str(e)!='quantified verdict mismatch':raise
        out['claim']=True;verify_outer(problem,out)
    return out


def produce_witness(problem):
    from .witness import verify_witness
    from .sturm import root_product,to_sparse
    f=Fiber.parse(problem)
    if f.k or f.n!=1:raise ValueError('witness producer supports a concrete univariate fiber')
    x=s.Symbol('x')
    # Isolating roots of the union separates unrelated atom roots as well.
    p=root_product(f.fs+f.qs)
    for interval in isolators(expr(to_sparse(p),(x,)),x):
        cert={'schema':'algebraic-witness-v1','interval':interval}
        try:verify_witness(problem,cert);return cert
        except ValueError:pass
    return None  # no acceptance, not by itself a refutation
