"""Untrusted numerical cone search with exact replay of all accepted results.

This is a finite-dictionary LP, NOT a general SOS/SDP implementation.
SciPy is imported only inside the search function. The verifier uses Fractions.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import combinations_with_replacement
from time import perf_counter
from polynomial import Poly, monomials

@dataclass(frozen=True)
class Atom:
    square: Poly
    hypotheses: tuple[int, ...] = ()

    def expand(self, hs: tuple[Poly, ...]) -> Poly:
        p = self.square**2
        for i in self.hypotheses:
            if type(i) is not int or not 0 <= i < len(hs):
                raise ValueError('Invalid hypothesis reference')
            p = p*hs[i]
        return p

@dataclass(frozen=True)
class ConeCertificate:
    terms: tuple[tuple[Q, Atom], ...]

    def to_json(self) -> dict:
        return {'kind': 'nonnegative_cone', 'terms': [
            {'weight': str(w), 'square': a.square.to_json(), 'hypotheses': list(a.hypotheses)}
            for w, a in self.terms]}


def check_cone(target: Poly, hs: tuple[Poly, ...], cert: ConeCertificate) -> bool:
    """Checks identity and positivity rules. hs are caller-proved nonnegative."""
    try:
        if any(h.n != target.n for h in hs):
            return False
        total = Poly.const(target.n, 0)
        for w, a in cert.terms:
            if not isinstance(w, Q) or w < 0 or a.square.n != target.n:
                return False
            total += w*a.expand(hs)
        return total == target
    except (TypeError, ValueError, IndexError, AttributeError):
        return False


def dictionary(n: int, degree: int, hs: tuple[Poly, ...], *, pair_squares: bool = True,
               product_order: int = 2, extra_squares: tuple[Poly, ...] = ()) -> tuple[Atom, ...]:
    """Bounded products of hypotheses times squares of small monomial combinations."""
    bases = monomials(n, degree//2)
    sqs = bases[:]
    if pair_squares:
        for i, a in enumerate(bases):
            for b in bases[i+1:]:
                sqs.extend((a+b, a-b))
    sqs.extend(extra_squares)
    factors = [()]
    for k in range(1, product_order+1):
        factors.extend(combinations_with_replacement(range(len(hs)), k))
    out: list[Atom] = []
    seen: set[Poly] = set()
    for s in sqs:
        for factors_ in factors:
            a = Atom(s, tuple(factors_))
            p = a.expand(hs)
            if p.degree() <= degree and p.terms and p not in seen:
                seen.add(p)
                out.append(a)
    return tuple(out)


def solve_cone(target: Poly, hs: tuple[Poly, ...], atoms: tuple[Atom, ...],
               timeout: float = 5.0) -> tuple[ConeCertificate | None, dict]:
    """Return certified candidate or None (unknown), including infeasible LP results."""
    import numpy as np
    from scipy.optimize import linprog
    t = perf_counter()
    polys = [a.expand(hs) for a in atoms]
    mons = sorted(set(dict(target.terms)).union(*(set(dict(p.terms)) for p in polys)))
    if not atoms:
        c = ConeCertificate(())
        return (c if check_cone(target, hs, c) else None), {'status':'empty_dictionary'}
    A = [[dict(p.terms).get(m, Q(0)) for p in polys] for m in mons]
    b = [dict(target.terms).get(m, Q(0)) for m in mons]
    try:
        result = linprog(np.ones(len(atoms)), A_eq=np.array(A, dtype=float),
                         b_eq=np.array(b, dtype=float), bounds=(0, None),
                         method='highs', options={'time_limit': timeout})
    except (ValueError, OverflowError) as ex:
        return None, {'status':'oracle_error','detail':str(ex)}
    stats = {'atoms':len(atoms),'monomials':len(mons),'lp_status':int(result.status),
             'search_seconds':perf_counter()-t}
    if not result.success:
        stats['status'] = 'unknown'
        return None, stats
    # Approximate values propose a support and rationals; never certify residuals numerically.
    indices = [i for i, x in enumerate(result.x) if x > 1e-9]
    weights = [Q(float(result.x[i])).limit_denominator(1_000_000) for i in indices]
    cert = ConeCertificate(tuple((w, atoms[i]) for i, w in zip(indices, weights) if w))
    if not check_cone(target, hs, cert):
        # Repair a proposed support by exact rational Gaussian elimination.
        # Parameterized/degenerate supports may still be rejected safely.
        import sympy as sp
        try:
            M = sp.Matrix([[sp.Rational(A[r][i].numerator,A[r][i].denominator)
                            for i in indices] for r in range(len(mons))])
            v = sp.Matrix([sp.Rational(x.numerator,x.denominator) for x in b])
            sol, params = M.gauss_jordan_solve(v)
            if params.rows:
                sol = sol.subs({a: 0 for a in params})
            weights = [Q(int(x.p), int(x.q)) for x in sol]
            cert = ConeCertificate(tuple((w, atoms[i]) for i, w in zip(indices, weights) if w))
        except (ValueError, TypeError, AttributeError, ZeroDivisionError):
            stats['status'] = 'reconstruction_rejected'
            return None, stats
    tc = perf_counter()
    accepted = check_cone(target, hs, cert)
    stats.update(status='checked_python' if accepted else 'reconstruction_rejected',
                 check_seconds=perf_counter()-tc, certificate_terms=len(cert.terms))
    return (cert if accepted else None), stats


def lean_proof(name: str, target: Poly, hs: tuple[Poly,...], cert: ConeCertificate,
               names: tuple[str,...]) -> str:
    """Emit a direct proof for mathlib; output is explicitly UNCOMPILED in this package."""
    if not check_cone(target, hs, cert):
        raise ValueError('Refusing to export invalid certificate')
    def atom_expr(a: Atom) -> str:
        s = f'({a.square.lean(names)}) ^ 2'
        for i in a.hypotheses:
            s = f'({s}) * ({hs[i].lean(names)})'
        return s
    def atom_proof(a: Atom) -> str:
        p = f'(sq_nonneg ({a.square.lean(names)}))'
        for i in a.hypotheses:
            p = f'(mul_nonneg {p} h{i})'
        return p
    lines = [f'theorem {name} ({" ".join(names)} : ℝ)']
    lines += [f'    (h{i} : 0 ≤ {h.lean(names)})' for i,h in enumerate(hs)]
    lines += [f'    : 0 ≤ {target.lean(names)} := by']
    expressions = []
    proofs = []
    for j,(w,a) in enumerate(cert.terms):
        wstr = f'({w.numerator} / {w.denominator} : ℝ)'
        expr = f'{wstr} * ({atom_expr(a)})'
        expressions.append(expr)
        lines += [f'  have c{j} : (0 : ℝ) ≤ {wstr} := by norm_num',
                  f'  have t{j} : (0 : ℝ) ≤ {expr} :=',
                  f'    mul_nonneg c{j} {atom_proof(a)}']
        proofs.append(f't{j}')
    if not expressions:
        lines += ['  norm_num']
    else:
        total = expressions[0]
        pr = proofs[0]
        for ex,pf in zip(expressions[1:],proofs[1:]):
            total = f'({total}) + ({ex})'
            pr = f'add_nonneg ({pr}) ({pf})'
        lines += [f'  have hsum : (0 : ℝ) ≤ {total} := {pr}',
                  f'  have hid : ({total}) = {target.lean(names)} := by ring',
                  '  rw [hid] at hsum','  exact hsum']
    return '\n'.join(lines)+'\n'
