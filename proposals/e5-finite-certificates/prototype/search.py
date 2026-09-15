"""Untrusted exact search prototypes. Requires SymPy; never imported by checker."""
from __future__ import annotations
from collections import deque
from itertools import product
from math import gcd
from functools import reduce
import sympy as s


def qr(x):
    a, b = s.Rational(x).as_numer_denom()
    return [int(a), int(b)]

def vector(v):
    return [qr(x) for x in v]

def mat(m):
    return [vector(m.row(i)) for i in range(m.rows)]

def enc(p, variables):
    p = s.Poly(s.expand(p), *variables, domain=s.QQ)
    return [[list(e), qr(c)] for e, c in sorted(p.terms()) if c]

def dec(raw, variables):
    return s.Add(*(s.Rational(*c)*s.prod(x**e for x, e in zip(variables, ex)) for ex, c in raw))

def matrix_from(raw):
    return s.Matrix([[s.Rational(*c) for c in row] for row in raw])

def linear_problem(actions, initial, target):
    return {'kind': 'linear', 'dimension': len(initial),
            'actions': [mat(s.Matrix(a)) for a in actions],
            'initial': vector(initial), 'target': vector(target)}

def linear_search(problem):
    n = problem['dimension']
    acts = [matrix_from(a) for a in problem['actions']]
    q = s.Matrix([list(map(lambda z:s.Rational(*z), problem['target']))])
    s0 = s.Matrix([s.Rational(*z) for z in problem['initial']])
    queue = deque([(q, ())])
    rows, words = [], []
    candidates = 0
    while queue:
        row, word = queue.popleft()
        candidates += 1
        if (row*s0)[0] != 0:
            state = s0
            for a in word:
                state = acts[a]*state
            assert (q*state)[0] != 0
            return {'status':'counterexample', 'word':list(word), 'value':qr((q*state)[0]),
                    'stats':{'basis_size':len(rows), 'candidates':candidates}}
        old = s.Matrix.vstack(*rows) if rows else s.zeros(0, n)
        if s.Matrix.vstack(old, row).rank() == len(rows):
            continue
        rows.append(row)
        words.append(word)
        for a, action in enumerate(acts):
            queue.append((row*action, (a,)+word))
    g = s.Matrix.vstack(*rows) if rows else s.zeros(0, n)
    def coefficients(row):
        if not rows:
            assert row == s.zeros(1, n)
            return []
        solution, params = g.T.gauss_jordan_solve(row.T)
        assert not params.rows
        return vector(solution)
    cert = {'kind':'linear', 'basis':mat(g), 'target_weights':coefficients(q),
            'action_weights':[[coefficients(row*a) for row in rows] for a in acts]}
    return {'status':'certified', 'certificate':cert,
            'stats':{'basis_size':len(rows), 'candidates':candidates, 'basis_words':[list(w) for w in words]}}

def ideal_problem(variables, actions, parameters, initial, target):
    return {'kind':'ideal', 'dimension':len(variables), 'parameters':len(parameters),
            'actions':[[enc(f, variables) for f in action] for action in actions],
            'initial':[enc(f, parameters) for f in initial], 'target':enc(target,variables)}

def ideal_search(problem, max_extensions=12, max_degree=32, max_words=10000, max_points=10000):
    xs = s.symbols(f'x0:{problem["dimension"]}')
    ts = s.symbols(f't0:{problem["parameters"]}')
    q = dec(problem['target'], xs)
    fs = [[dec(f,xs) for f in a] for a in problem['actions']]
    ini = [dec(f,ts) for f in problem['initial']]
    base = [q] if q != 0 else [s.Integer(0)]
    depth = 0
    reductions = 0
    def subst(p, vals):
        return s.expand(p.subs(dict(zip(xs, vals)), simultaneous=True))
    while True:
        gb = s.groebner(base, *xs, order='grevlex', domain=s.QQ)
        generators = [g.as_expr() for g in gb.polys]
        if not generators:
            generators = [s.Integer(0)]
        if any(s.Poly(g,*xs).total_degree()>max_degree for g in generators):
            return {'status':'unknown', 'reason':'degree_budget', 'stats':{'extensions':depth,'reductions':reductions}}
        initial_residuals = [subst(g, ini) for g in generators]
        if any(r != 0 for r in initial_residuals):
            # Never treat a bad auxiliary generator as the original counterexample.
            # Enumerate actual words on the original problem and replay the target.
            examined = 0
            points = 0
            for length in range(depth+1):
                for word in product(range(len(fs)), repeat=length):
                    examined += 1
                    if examined > max_words:
                        return {'status':'unknown','reason':'counterexample_budget','stats':{'extensions':depth,'reductions':reductions}}
                    state = ini
                    for a in word:
                        state = [subst(f,state) for f in fs[a]]
                    residual = subst(q,state)
                    if residual == 0:
                        continue
                    ds = [s.degree(residual,t) for t in ts]
                    for vals in product(*(range(int(d)+1) for d in ds)):
                        points += 1
                        if points > max_points:
                            return {'status':'unknown','reason':'point_budget','stats':{'extensions':depth,'reductions':reductions}}
                        value = residual.subs(dict(zip(ts, vals)))
                        if value != 0:
                            return {'status':'counterexample','word':list(word),'parameters':list(vals),'value':qr(value),
                                    'stats':{'extensions':depth,'reductions':reductions,'words':examined}}
            raise AssertionError('nonzero ideal generator did not yield bounded-depth target witness')
        extra = None
        for f in fs:
            for g in generators:
                pull = subst(g, f)
                if s.Poly(pull,*xs).total_degree()>max_degree:
                    return {'status':'unknown','reason':'degree_budget','stats':{'extensions':depth,'reductions':reductions}}
                reductions += 1
                rem = gb.reduce(pull)[1] if gb.polys else pull
                if rem != 0:
                    extra = rem
                    break
            if extra is not None:
                break
        if extra is None:
            break
        if depth >= max_extensions:
            return {'status':'unknown','reason':'extension_budget','stats':{'extensions':depth,'reductions':reductions}}
        base = generators + [extra]
        depth += 1
    def quot(p):
        if not gb.polys:
            assert p == 0
            return [[]]
        qs, rem = gb.reduce(p)
        assert rem == 0
        return [enc(z,xs) for z in qs]
    cert={'kind':'ideal','generators':[enc(g,xs) for g in generators],
          'target_weights':quot(q),
          'action_weights':[[quot(subst(g,f)) for g in generators] for f in fs]}
    return {'status':'certified','certificate':cert,
            'stats':{'extensions':depth,'reductions':reductions,'generators':len(generators),
                     'max_generator_degree':max(s.Poly(g,*xs).total_degree() for g in generators)}}

def sum_problem(power, moment=0):
    k=s.Symbol('k')
    return {'kind':'binomial_sum','power':power,'weight':enc(k**moment,(k,))}

def sum_search(problem, max_p_degree=3, max_r_degree=4):
    A,B,n,k = vs = s.symbols('A B n k')
    m=problem['power']
    w=dec(problem['weight'],(k,))
    rel=(n+1-k)*A-k*B
    gb=s.groebner([rel],*vs,order='lex',domain=s.QQ)
    trials=0
    for cost in range(max_p_degree+max_r_degree+1):
        for dp in range(max_p_degree+1):
            dr=cost-dp
            if not 0<=dr<=max_r_degree:
                continue
            ps=[n**i for i in range(dp+1)]
            rs=[n**i*k**j for total in range(dr+1) for i in range(total+1) for j in [total-i]]
            cols=[p*w*B**m for p in ps]+[p*w*(A+B)**m for p in ps]
            cols += [r*A**m-r.subs(k,k+1)*B**m for r in rs]
            reduced=[s.Poly(gb.reduce(s.expand(c))[1],*vs,domain=s.QQ) for c in cols]
            monomials=sorted(set(e for p in reduced for e,c in p.terms() if c))
            dictionaries=[p.as_dict() for p in reduced]
            matrix=s.Matrix([[d.get(e,0) for d in dictionaries] for e in monomials])
            if not monomials:
                matrix=s.zeros(0,len(cols))
            trials+=1
            for v in matrix.nullspace():
                if not any(v[dp+1:2*(dp+1)]):
                    continue
                lcm=s.ilcm(*[c.q for c in v]) if len(v)>1 else v[0].q
                ints=[int(c*lcm) for c in v]
                common=reduce(gcd,ints)
                ints=[i//abs(common) for i in ints]
                p0=s.expand(sum(c*p for c,p in zip(ints[:dp+1],ps)))
                p1=s.expand(sum(c*p for c,p in zip(ints[dp+1:2*(dp+1)],ps)))
                r=s.expand(sum(c*p for c,p in zip(ints[2*(dp+1):],rs)))
                if s.LC(s.Poly(p1,n))<0:
                    p0,p1,r=-p0,-p1,-r
                residual=s.expand(p1*w*(A+B)**m+p0*w*B**m-r.subs(k,k+1)*B**m+r*A**m)
                quotient, remainder=s.div(residual,rel,*vs,domain=s.QQ)
                assert remainder==0
                cert={'kind':'binomial_sum','p0':enc(p0,(n,)),'p1':enc(p1,(n,)),
                      'r':enc(r,(n,k)),'relation_multiplier':enc(quotient,vs)}
                exceptional=[int(root) for root in s.polys.polytools.ground_roots(p1,n) if root.is_integer and root>=0]
                return {'status':'certified','certificate':cert,
                        'stats':{'trials':trials,'p_degree':dp,'r_degree':dr,'columns':len(cols),'rows':len(monomials),
                                 'nonnegative_leading_zeros':sorted(exceptional)}}
    return {'status':'unknown','reason':'template_exhausted','stats':{'trials':trials}}
