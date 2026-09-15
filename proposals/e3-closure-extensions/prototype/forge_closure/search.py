"""Untrusted certificate producers. SymPy is used only on this side."""
from __future__ import annotations
from collections import deque
from dataclasses import dataclass
from time import perf_counter
from typing import Any
import sympy as sp
from .checker import verify


def wire_q(q):
    q = sp.Rational(q)
    return [int(q.p), int(q.q)]


def wire_poly(p, variables):
    return [[list(e), wire_q(c)] for e, c in sp.Poly(p, *variables, domain=sp.QQ).terms() if c]


def expression(raw, variables):
    return sum((sp.Rational(*q) * sp.prod(v**e for v, e in zip(variables, es, strict=True)) for es, q in raw), sp.Integer(0))


def wire_matrix(rows):
    return [[wire_q(c) for c in row] for row in rows]


def make_problem(variables, transitions, initial, targets):
    return {
        "kind": "polynomial_transition_system_v1",
        "dimension": len(variables),
        "initial": [wire_q(q) for q in initial],
        "transitions": [[wire_poly(p, variables) for p in fs] for fs in transitions],
        "targets": [wire_poly(p, variables) for p in targets],
    }


def coordinates(q, basis, variables):
    """Exact span membership, returning coordinates or None."""
    q = sp.Poly(q, *variables, domain=sp.QQ)
    if not basis:
        return [] if q.is_zero else None
    ps = [sp.Poly(p, *variables, domain=sp.QQ) for p in basis]
    monomials = sorted(set(q.monoms()).union(*(set(p.monoms()) for p in ps)))
    a = sp.Matrix([[p.coeff_monomial(m) for p in ps] for m in monomials])
    b = sp.Matrix([q.coeff_monomial(m) for m in monomials])
    try:
        solution, params = a.gauss_jordan_solve(b)
    except ValueError:
        return None
    # Basis construction guarantees independence; never silently pick free values.
    if params.rows:
        raise RuntimeError("search basis unexpectedly dependent")
    return list(solution)


@dataclass(frozen=True)
class ClosureLimits:
    basis: int = 32
    degree: int = 12
    terms: int = 10000
    pullbacks: int = 1000


def pullback_search(problem, limits=ClosureLimits()):
    started = perf_counter()
    dim = problem["dimension"]
    xs = sp.symbols(f"x0:{dim}")
    initial = [sp.Rational(*q) for q in problem["initial"]]
    trans = [[expression(p, xs) for p in fs] for fs in problem["transitions"]]
    targets = [expression(p, xs) for p in problem["targets"]]
    basis, origins = [], []
    work = deque((q, j, ()) for j, q in enumerate(targets))
    stats = {"span_queries": 0, "pullbacks": 0, "maximum_degree": 0}

    def result(status, reason=None, cert=None):
        stats["basis_dimension"] = len(basis)
        if cert is not None:
            verify(problem, cert)
        stats["seconds"] = perf_counter() - started
        return {"status": status, "reason": reason, "certificate": cert, "statistics": stats}

    while work:
        q, goal, word = work.popleft()
        p = sp.Poly(q, *xs, domain=sp.QQ)
        degree = 0 if p.is_zero else int(p.total_degree())
        stats["maximum_degree"] = max(stats["maximum_degree"], degree)
        if degree > limits.degree or len(p.terms()) > limits.terms:
            return result("unknown", "polynomial_resource_ceiling")
        if p.eval(dict(zip(xs, initial, strict=True))) != 0:
            cert = {"kind": "transition_word_counterexample_v1", "target": goal, "word": list(word)}
            return result("refuted", cert=cert)
        stats["span_queries"] += 1
        if coordinates(q, basis, xs) is not None:
            continue
        if len(basis) >= limits.basis:
            return result("unknown", "basis_ceiling")
        basis.append(q)
        origins.append({"target": goal, "word": list(word)})
        for a, fs in enumerate(trans):
            if stats["pullbacks"] >= limits.pullbacks:
                return result("unknown", "pullback_ceiling")
            # Simultaneous substitution is essential; sequential substitution is wrong.
            new = sp.expand(q.subs(dict(zip(xs, fs, strict=True)), simultaneous=True))
            stats["pullbacks"] += 1
            work.append((new, goal, (a,) + word))
    hs = []
    for fs in trans:
        rows = []
        for q in basis:
            qb = sp.expand(q.subs(dict(zip(xs, fs, strict=True)), simultaneous=True))
            row = coordinates(qb, basis, xs)
            if row is None:
                raise RuntimeError("unclosed basis escaped the worklist")
            rows.append(row)
        hs.append(wire_matrix(rows))
    cs = [coordinates(q, basis, xs) for q in targets]
    cert = {"kind": "pullback_closure_v1", "basis": [wire_poly(q, xs) for q in basis],
            "steps": hs, "targets": wire_matrix(cs), "origins": origins}
    return result("proved", cert=cert)


def moore_search(problem, max_pairs=10000):
    started = perf_counter()
    left, right = problem["left"], problem["right"]
    root = (left["initial"], right["initial"])
    parents = {root: None}
    queue = deque([root])
    expanded = 0
    while queue:
        p, q = queue.popleft()
        expanded += 1
        if left["outputs"][p] != right["outputs"][q]:
            word = []
            pair = (p, q)
            while parents[pair] is not None:
                previous, symbol = parents[pair]
                word.append(symbol)
                pair = previous
            cert = {"kind": "moore_counterexample_v1", "word": list(reversed(word))}
            verify(problem, cert)
            return {"status": "refuted", "certificate": cert, "statistics": {"pairs": len(parents), "expanded": expanded, "seconds": perf_counter()-started}}
        for a in range(problem["alphabet_size"]):
            child = (left["transitions"][p][a], right["transitions"][q][a])
            if child not in parents:
                if len(parents) >= max_pairs:
                    return {"status": "unknown", "reason": "pair_ceiling", "certificate": None, "statistics": {"pairs": len(parents), "expanded": expanded, "seconds": perf_counter()-started}}
                parents[child] = ((p, q), a)
                queue.append(child)
    cert = {"kind": "moore_bisimulation_v1", "relation": [list(pair) for pair in sorted(parents)]}
    verify(problem, cert)
    return {"status": "proved", "certificate": cert, "statistics": {"pairs": len(parents), "expanded": expanded, "seconds": perf_counter()-started}}


def make_moment(power, weight, k):
    return {"kind": "binomial_moment_v1", "power": power, "weight": wire_poly(weight, (k,))}


def telescoper_search(problem, max_degree=3, max_u_degree=6):
    """First-order ansatz search; no general Zeilberger completeness claim.

    Seek a(n) S(n+1) = b(n) S(n), with flux
    k^m U(n,k) choose(n+1,k)^m / (n+1)^m.
    """
    started = perf_counter()
    n, k = sp.symbols("n k")
    m = problem["power"]
    w = expression(problem["weight"], (k,))
    tried = 0
    for degree in range(max_degree+1):
        for ud in range(max_u_degree+1):
            a_mons = [n**i for i in range(degree+1)]
            u_mons = [n**i*k**j for t in range(ud+1) for i in range(t+1) for j in [t-i]]
            columns = [(n+1)**m*w*z for z in a_mons]
            columns += [-(n+1-k)**m*w*z for z in a_mons]
            columns += [-(n+1-k)**m*z.subs(k,k+1) + k**m*z for z in u_mons]
            ps = [sp.Poly(sp.expand(z),n,k) for z in columns]
            mons = sorted(set().union(*(set(p.monoms()) for p in ps)))
            matrix = sp.Matrix([[p.coeff_monomial(mon) for p in ps] for mon in mons])
            tried += 1
            for vector in matrix.nullspace():
                j = degree+1
                a = sp.expand(sum(c*z for c,z in zip(vector[:j],a_mons,strict=True)))
                if a == 0:
                    continue
                b = sp.expand(sum(c*z for c,z in zip(vector[j:2*j],a_mons,strict=True)))
                u = sp.expand(sum(c*z for c,z in zip(vector[2*j:],u_mons,strict=True)))
                denominator = sp.ilcm(*[sp.denom(c) for c in vector])
                a,b,u = [sp.expand(denominator*z) for z in (a,b,u)]
                common = sp.gcd(sp.gcd(a,b),u)
                if common != 0:
                    a,b,u = [sp.cancel(z/common) for z in (a,b,u)]
                # Exact replay below rejects a common factor involving k that invalidates the schema.
                if sp.Poly(a,n).LC() < 0:
                    a,b,u = [-a,-b,-u]
                regular = None
                for start in range(21):
                    shifted = sp.Poly(a.subs(n,n+start),n)
                    if shifted.TC()>0 and all(c>=0 for c in shifted.all_coeffs()):
                        regular = start
                        break
                if regular is None:
                    continue
                cert = {"kind":"binomial_flux_v1", "a":wire_poly(a,(n,)), "b":wire_poly(b,(n,)),
                        "u":wire_poly(u,(n,k)), "start":regular, "sign":1}
                verify(problem, cert)
                return {"status":"proved", "certificate":cert,
                        "statistics":{"systems":tried,"coefficient_degree":degree,"flux_degree":ud,
                                      "rows":matrix.rows,"columns":matrix.cols,"seconds":perf_counter()-started}}
    return {"status":"unknown", "reason":"first_order_ansatz_exhausted", "certificate":None,
            "statistics":{"systems":tried,"seconds":perf_counter()-started}}


def all_monomials(variables, degree):
    from itertools import product
    return [sp.prod(x**e for x,e in zip(variables, es, strict=True))
            for es in product(range(degree+1), repeat=len(variables)) if sum(es)<=degree]


def ideal_coordinates(q, basis, variables, max_degree=4):
    """Fixed generators => coefficient search is linear, not bilinear.

    Try direct division, then bounded exact polynomial-multiplier synthesis.
    Groebner membership is not itself returned as proof evidence.
    """
    if not basis:
        return [] if sp.expand(q)==0 else None
    quotients, remainder = sp.reduced(q, basis, *variables)
    if remainder == 0 and all(p==0 or sp.Poly(p,*variables).total_degree()<=max_degree for p in quotients):
        return list(quotients)
    for degree in range(max_degree+1):
        mons = all_monomials(variables, degree)
        columns = [sp.Poly(m*b,*variables,domain=sp.QQ) for b in basis for m in mons]
        target = sp.Poly(q,*variables,domain=sp.QQ)
        support = sorted(set(target.monoms()).union(*(set(p.monoms()) for p in columns)))
        matrix = sp.Matrix([[p.coeff_monomial(mon) for p in columns] for mon in support])
        rhs = sp.Matrix([target.coeff_monomial(mon) for mon in support])
        try:
            solution, params = matrix.gauss_jordan_solve(rhs)
        except ValueError:
            continue
        if params.rows:
            solution = solution.subs({p:0 for p in params})
        width = len(mons)
        return [sp.expand(sum(solution[i*width+j]*mon for j,mon in enumerate(mons))) for i in range(len(basis))]
    return None


def ideal_search(problem, limits=ClosureLimits(), multiplier_degree=4):
    """Goal-generated ascending ideal chain, with original-orbit provenance.

    Unbounded ideal discovery terminates by Noetherianity; implemented ceilings
    and bounded multiplier reconstruction can still return unknown.
    """
    started = perf_counter()
    dim = problem["dimension"]
    xs = sp.symbols(f"x0:{dim}")
    initial = [sp.Rational(*q) for q in problem["initial"]]
    trans = [[expression(p,xs) for p in fs] for fs in problem["transitions"]]
    targets = [expression(p,xs) for p in problem["targets"]]
    basis, origins = [], []
    groebner = None
    work = deque((q,j,()) for j,q in enumerate(targets))
    stats = {"membership_queries":0,"groebner_builds":0,"pullbacks":0,"maximum_degree":0}

    def result(status, reason=None, cert=None):
        stats["generators"] = len(basis)
        if cert is not None:
            verify(problem,cert)
        stats["seconds"] = perf_counter()-started
        return {"status":status,"reason":reason,"certificate":cert,"statistics":stats}

    while work:
        q,goal,word=work.popleft()
        p=sp.Poly(q,*xs,domain=sp.QQ)
        degree=0 if p.is_zero else int(p.total_degree())
        stats["maximum_degree"]=max(stats["maximum_degree"],degree)
        if degree>limits.degree or len(p.terms())>limits.terms:
            return result("unknown","polynomial_resource_ceiling")
        if p.eval(dict(zip(xs,initial,strict=True)))!=0:
            return result("refuted",cert={"kind":"transition_word_counterexample_v1","target":goal,"word":list(word)})
        stats["membership_queries"]+=1
        if p.is_zero or (groebner is not None and groebner.contains(q)):
            continue
        if len(basis)>=limits.basis:
            return result("unknown","generator_ceiling")
        basis.append(q)
        origins.append({"target":goal,"word":list(word)})
        groebner=sp.groebner(basis,*xs,domain=sp.QQ,order='grevlex')
        stats["groebner_builds"]+=1
        for a,fs in enumerate(trans):
            if stats["pullbacks"]>=limits.pullbacks:
                return result("unknown","pullback_ceiling")
            qb=sp.expand(q.subs(dict(zip(xs,fs,strict=True)),simultaneous=True))
            stats["pullbacks"]+=1
            work.append((qb,goal,(a,)+word))
    step_rows=[]
    for fs in trans:
        rows=[]
        for q in basis:
            qb=sp.expand(q.subs(dict(zip(xs,fs,strict=True)),simultaneous=True))
            coeffs=ideal_coordinates(qb,basis,xs,multiplier_degree)
            if coeffs is None:
                return result("unknown","multiplier_degree_ceiling")
            rows.append([wire_poly(c,xs) for c in coeffs])
        step_rows.append(rows)
    target_rows=[]
    for q in targets:
        coeffs=ideal_coordinates(q,basis,xs,multiplier_degree)
        if coeffs is None:
            return result("unknown","target_multiplier_ceiling")
        target_rows.append([wire_poly(c,xs) for c in coeffs])
    cert={"kind":"pullback_ideal_v1","basis":[wire_poly(p,xs) for p in basis],
          "steps":step_rows,"targets":target_rows,"origins":origins}
    return result("proved",cert=cert)
