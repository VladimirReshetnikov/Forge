"""Counterexample-guided polynomial invariant synthesis for accumulator recurrences.

F_p(0,a)=a; F_p(n+1,a)=F_p(n,a+(n+1)^p).
Search ranges over bivariate polynomials Q(n,a) of increasing total degree.
Numerical samples reject candidates; acceptance uses exact base/step polynomial
identities. An ordinary structural induction then establishes F_p(n,a)=Q(n,a).
No Lean kernel is called by this module.
"""
from __future__ import annotations
import sympy as sp
from itertools import product
from fractions import Fraction
n, a = sp.symbols('n a')


def actual(power: int, nn: int, aa: int) -> int:
    return aa + sum(k**power for k in range(1, nn+1))


def check_invariant(power: int, q) -> tuple[bool, object, object]:
    """Exact polynomial equalities; unrelated to the finite sample set."""
    q = sp.Poly(q, n, a, domain=sp.QQ).as_expr()
    base = sp.Poly(q.subs(n, 0) - a, a, domain=sp.QQ).as_expr()
    step = sp.Poly(q.subs(n, n+1) - q.subs(a, a+(n+1)**power), n, a, domain=sp.QQ).as_expr()
    return base == 0 and step == 0, base, step


def synthesize(power: int, max_degree=7, max_iterations=300):
    if type(power) is not int or power < 0:
        raise ValueError('nonnegative integral power required')
    samples = [(0, 0)]
    history = []
    for degree in range(max_degree + 1):
        exps = sorted(((i,j) for i in range(degree+1) for j in range(degree+1-i)),
                      key=lambda t:(sum(t), t))
        basis = [n**i*a**j for i,j in exps]
        for _ in range(max_iterations):
            mat = sp.Matrix([[nn**i*aa**j for i,j in exps] for nn,aa in samples])
            rhs = sp.Matrix([actual(power,nn,aa) for nn,aa in samples])
            sols = sp.linsolve((mat,rhs))
            if sols is sp.EmptySet or not sols:
                history.append({'degree':degree,'event':'inconsistent samples','samples':len(samples)})
                break
            sol = next(iter(sols))
            free = set().union(*(v.free_symbols for v in sol))
            cs = [v.subs({s:0 for s in free}) for v in sol]
            q = sp.expand(sum(c*b for c,b in zip(cs,basis)))
            ok, base, step = check_invariant(power,q)
            history.append({'degree':degree,'candidate':str(q),'accepted':ok,'samples':len(samples)})
            if ok:
                return q, {'power':power,'degree':degree,'sample_count':len(samples),
                           'samples':[list(s) for s in samples],'history':history,
                           'base_residual':str(base),'step_residual':str(step)}
            # Nonzero bivariate polynomial of degrees <= B cannot vanish on
            # the whole (B+1)x(B+1) integer grid. This is a complete separator
            # for this exact residual, not a random testing heuristic.
            B = max(degree, degree*max(power,1)) + 2
            found = None
            if base != 0:
                for aa in range(B+1):
                    if base.subs(a,aa) != 0:
                        found = (0,aa); break
            else:
                for nn,aa in product(range(B+1),repeat=2):
                    if step.subs({n:nn,a:aa}) != 0:
                        pairs = [(nn+1,aa),(nn,aa+(nn+1)**power)]
                        found = next((pair for pair in pairs if
                                      q.subs({n:pair[0],a:pair[1]}) != actual(power,*pair)),None)
                        if found is not None:
                            break
            if found is None or found in samples:
                raise RuntimeError('failed to separate an incorrect invariant')
            samples.append(found)
        else:
            return None, {'status':'iteration limit','history':history}
    return None, {'status':'degree limit','history':history}


def encode(q):
    return [[list(m),str(c)] for m,c in sp.Poly(q,n,a,domain=sp.QQ).terms()]
