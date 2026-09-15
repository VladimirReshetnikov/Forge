"""Standard-library-only certificate checker; imports no search code.

All polynomial arithmetic below is independent of SymPy (used by the producer).
The input problem is supplied separately; a certificate cannot replace it.
Limits are defense-in-depth for research use, not a hardened hostile-input parser.
"""
from __future__ import annotations
from fractions import Fraction as Q
from typing import Any

MAX_DIM = 32
MAX_TERMS = 50000
MAX_DEGREE = 64
MAX_BITS = 16384
MAX_BASIS = 128
MAX_STATES = 10000

class Invalid(ValueError):
    """Malformed or false certificate, or configured resource ceiling."""


def exact_int(x: Any) -> int:
    if type(x) is not int:
        raise Invalid("expected a literal integer, not bool/float")
    if x.bit_length() > MAX_BITS:
        raise Invalid("integer bit ceiling")
    return x


def rat(x: Any) -> Q:
    if not isinstance(x, list) or len(x) != 2:
        raise Invalid("rational must be [numerator, positive denominator]")
    n, d = map(exact_int, x)
    if d <= 0:
        raise Invalid("denominator must be positive")
    q = Q(n, d)
    if q.numerator != n or q.denominator != d:
        raise Invalid("noncanonical rational")
    return q


def poly(raw: Any, dim: int) -> dict[tuple[int, ...], Q]:
    if type(dim) is not int or not 1 <= dim <= MAX_DIM:
        raise Invalid("bad polynomial dimension")
    if not isinstance(raw, list) or len(raw) > MAX_TERMS:
        raise Invalid("bad polynomial term list")
    out = {}
    for term in raw:
        if not isinstance(term, list) or len(term) != 2:
            raise Invalid("bad polynomial term")
        exps, coefficient = term
        if not isinstance(exps, list) or len(exps) != dim:
            raise Invalid("wrong monomial dimension")
        e = tuple(exact_int(a) for a in exps)
        if any(a < 0 for a in e) or sum(e) > MAX_DEGREE:
            raise Invalid("monomial exponent limit")
        c = rat(coefficient)
        if not c or e in out:
            raise Invalid("zero or duplicate polynomial term")
        out[e] = c
    return out


def clean(p):
    if len(p) > MAX_TERMS:
        raise Invalid("intermediate term ceiling")
    for e, c in p.items():
        if sum(e) > MAX_DEGREE or max(c.numerator.bit_length(), c.denominator.bit_length()) > MAX_BITS:
            raise Invalid("intermediate arithmetic ceiling")
    return {e: c for e, c in p.items() if c}


def add(p, q):
    r = p.copy()
    for e, c in q.items():
        r[e] = r.get(e, Q(0)) + c
    return clean(r)


def scale(c, p):
    return clean({e: c*a for e, a in p.items()})


def mul(p, q):
    r = {}
    for e, a in p.items():
        for f, b in q.items():
            ef = tuple(x+y for x, y in zip(e, f, strict=True))
            if sum(ef) > MAX_DEGREE:
                raise Invalid("product degree ceiling")
            r[ef] = r.get(ef, Q(0)) + a*b
    return clean(r)


def power(p, n, dim):
    r = {(0,)*dim: Q(1)}
    while n:
        if n & 1:
            r = mul(r, p)
        n //= 2
        if n:
            p = mul(p, p)
    return r


def subst(p, images, out_dim):
    r = {}
    for e, c in p.items():
        term = {(0,)*out_dim: c}
        for f, n in zip(images, e, strict=True):
            term = mul(term, power(f, n, out_dim))
        r = add(r, term)
    return r


def evaluate(p, xs):
    result = Q(0)
    for e, c in p.items():
        for x, n in zip(xs, e, strict=True):
            c *= x**n
        result += c
    return result


def lincomb(coeffs, basis):
    r = {}
    for c, b in zip(coeffs, basis, strict=True):
        r = add(r, scale(c, b))
    return r


def matrix(raw, rows, cols):
    if not isinstance(raw, list) or len(raw) != rows:
        raise Invalid("wrong matrix row count")
    result = []
    for row in raw:
        if not isinstance(row, list) or len(row) != cols:
            raise Invalid("wrong matrix column count")
        result.append([rat(c) for c in row])
    return result


def load_closure_problem(problem):
    if problem.get("kind") != "polynomial_transition_system_v1":
        raise Invalid("wrong problem kind")
    dim = exact_int(problem["dimension"])
    initial = [rat(v) for v in problem["initial"]]
    if len(initial) != dim:
        raise Invalid("wrong initial dimension")
    trans = [[poly(p, dim) for p in fs] for fs in problem["transitions"]]
    if not trans or len(trans) > 32 or any(len(fs) != dim for fs in trans):
        raise Invalid("wrong transition dimensions")
    targets = [poly(p, dim) for p in problem["targets"]]
    if not targets or len(targets) > MAX_BASIS:
        raise Invalid("wrong target count")
    return dim, initial, trans, targets


def check_closure(problem, cert):
    dim, initial, trans, targets = load_closure_problem(problem)
    if cert.get("kind") != "pullback_closure_v1":
        raise Invalid("wrong closure certificate kind")
    raw_basis = cert["basis"]
    if not isinstance(raw_basis, list) or len(raw_basis) > MAX_BASIS:
        raise Invalid("basis ceiling")
    basis = [poly(p, dim) for p in raw_basis]
    r = len(basis)
    if any(evaluate(p, initial) != 0 for p in basis):
        raise Invalid("initial invariant violation")
    cs = matrix(cert["targets"], len(targets), r)
    for target, coefficients in zip(targets, cs, strict=True):
        if target != lincomb(coefficients, basis):
            raise Invalid("target not reconstructed")
    if len(cert["steps"]) != len(trans):
        raise Invalid("missing transition certificate")
    for fs, raw in zip(trans, cert["steps"], strict=True):
        hs = matrix(raw, r, r)
        for b, h in zip(basis, hs, strict=True):
            if subst(b, fs, dim) != lincomb(h, basis):
                raise Invalid("pullback identity violated")
    return True


def check_closure_counterexample(problem, cert):
    dim, initial, trans, targets = load_closure_problem(problem)
    if cert.get("kind") != "transition_word_counterexample_v1":
        raise Invalid("wrong negative certificate kind")
    word = cert["word"]
    if not isinstance(word, list) or len(word) > 10000:
        raise Invalid("counterexample word ceiling")
    state = initial
    for a in word:
        a = exact_int(a)
        if not 0 <= a < len(trans):
            raise Invalid("unknown transition label")
        state = [evaluate(p, state) for p in trans[a]]
        if any(max(x.numerator.bit_length(), x.denominator.bit_length()) > MAX_BITS for x in state):
            raise Invalid("counterexample bit ceiling")
    goal = exact_int(cert["target"])
    if not 0 <= goal < len(targets) or evaluate(targets[goal], state) == 0:
        raise Invalid("not a counterexample")
    return True


def machine(m, alphabet):
    transitions = m["transitions"]
    outputs = m["outputs"]
    if not isinstance(transitions, list) or not 1 <= len(transitions) <= MAX_STATES:
        raise Invalid("state ceiling")
    n = len(transitions)
    if len(outputs) != n:
        raise Invalid("output dimension")
    outputs = [exact_int(x) for x in outputs]
    for row in transitions:
        if len(row) != alphabet:
            raise Invalid("incomplete alphabet")
        for j in row:
            if not 0 <= exact_int(j) < n:
                raise Invalid("transition out of range")
    root = exact_int(m["initial"])
    if not 0 <= root < n:
        raise Invalid("initial state out of range")
    return transitions, outputs, root


def load_moore(problem):
    if problem.get("kind") != "moore_equivalence_v1":
        raise Invalid("wrong problem kind")
    k = exact_int(problem["alphabet_size"])
    if not 1 <= k <= 32:
        raise Invalid("alphabet ceiling")
    return k, machine(problem["left"], k), machine(problem["right"], k)


def check_bisimulation(problem, cert):
    k, (tl, ol, il), (tr, or_, ir) = load_moore(problem)
    if cert.get("kind") != "moore_bisimulation_v1":
        raise Invalid("wrong relation certificate kind")
    raw = cert["relation"]
    if not isinstance(raw, list) or len(raw) > MAX_STATES:
        raise Invalid("relation ceiling")
    relation = set()
    for pair in raw:
        if not isinstance(pair, list) or len(pair) != 2:
            raise Invalid("malformed state pair")
        p, q = map(exact_int, pair)
        if not 0 <= p < len(tl) or not 0 <= q < len(tr) or (p, q) in relation:
            raise Invalid("duplicate or invalid pair")
        relation.add((p, q))
    if (il, ir) not in relation:
        raise Invalid("initial pair absent")
    for p, q in relation:
        if ol[p] != or_[q]:
            raise Invalid("unequal observations")
        for a in range(k):
            if (tl[p][a], tr[q][a]) not in relation:
                raise Invalid("relation not successor-closed")
    return True


def check_moore_counterexample(problem, cert):
    k, (tl, ol, il), (tr, or_, ir) = load_moore(problem)
    if cert.get("kind") != "moore_counterexample_v1":
        raise Invalid("wrong word certificate kind")
    word = cert["word"]
    if not isinstance(word, list) or len(word) > MAX_STATES:
        raise Invalid("word ceiling")
    for a in word:
        if not 0 <= exact_int(a) < k:
            raise Invalid("alphabet symbol out of range")
        il, ir = tl[il][a], tr[ir][a]
    if ol[il] == or_[ir]:
        raise Invalid("word does not distinguish outputs")
    return True


def check_telescoper(problem, cert):
    """Check an identity certifying a recurrence for binomial-power moments.

    S(n) = sum_{k=0}^n w(k) choose(n,k)^m.
    The report proves the fixed semantic bridge from this identity to the sum.
    This function checks the entire symbolic identity, not sampled n,k values.
    """
    if problem.get("kind") != "binomial_moment_v1" or cert.get("kind") != "binomial_flux_v1":
        raise Invalid("wrong telescoping kind")
    m = exact_int(problem["power"])
    if not 1 <= m <= 12:
        raise Invalid("binomial power ceiling")
    w = poly(problem["weight"], 1)
    a = poly(cert["a"], 1)
    b = poly(cert["b"], 1)
    u = poly(cert["u"], 2)
    if not a:
        raise Invalid("zero leading recurrence coefficient")
    one = {(0, 0): Q(1)}
    n = {(1, 0): Q(1)}
    k = {(0, 1): Q(1)}
    np1 = add(n, one)
    d = add(np1, scale(Q(-1), k))
    w2 = subst(w, [k], 2)
    a2, b2 = subst(a, [n], 2), subst(b, [n], 2)
    left = mul(add(mul(a2, power(np1, m, 2)), scale(Q(-1), mul(b2, power(d, m, 2)))), w2)
    right = add(mul(power(d, m, 2), subst(u, [n, add(k, one)], 2)), scale(Q(-1), mul(power(k, m, 2), u)))
    if left != right:
        raise Invalid("telescoping polynomial identity violated")
    # This optional certificate proves a(n) nonzero for every n >= start.
    start = exact_int(cert["start"])
    sign = exact_int(cert["sign"])
    if start < 0 or sign not in (-1, 1):
        raise Invalid("invalid recurrence regularity range")
    t = {(1,): Q(1)}
    shifted = scale(Q(sign), subst(a, [add(t, {(0,): Q(start)})], 1))
    if shifted.get((0,), Q(0)) <= 0 or any(c < 0 for c in shifted.values()):
        raise Invalid("leading coefficient positivity proof failed")
    return True


def verify(problem, cert):
    try:
        if not isinstance(problem, dict) or not isinstance(cert, dict):
            raise Invalid("problem and certificate must be objects")
        kind = cert.get("kind")
        dispatch = {
            "pullback_closure_v1": check_closure,
            "pullback_ideal_v1": check_ideal,
            "transition_word_counterexample_v1": check_closure_counterexample,
            "moore_bisimulation_v1": check_bisimulation,
            "moore_counterexample_v1": check_moore_counterexample,
            "binomial_flux_v1": check_telescoper,
        }
        if kind not in dispatch:
            raise Invalid("unsupported certificate kind")
        return dispatch[kind](problem, cert)
    except (KeyError, TypeError, IndexError, OverflowError, AttributeError) as e:
        raise Invalid(f"malformed certificate: {type(e).__name__}") from e


def polynomial_matrix(raw, rows, cols, dim):
    if not isinstance(raw, list) or len(raw) != rows:
        raise Invalid("wrong polynomial matrix row count")
    result = []
    for row in raw:
        if not isinstance(row, list) or len(row) != cols:
            raise Invalid("wrong polynomial matrix column count")
        result.append([poly(p, dim) for p in row])
    return result


def idealcomb(coeffs, basis):
    r = {}
    for c, b in zip(coeffs, basis, strict=True):
        r = add(r, mul(c, b))
    return r


def check_ideal(problem, cert):
    dim, initial, trans, targets = load_closure_problem(problem)
    if cert.get("kind") != "pullback_ideal_v1":
        raise Invalid("wrong ideal certificate kind")
    raw_basis = cert["basis"]
    if not isinstance(raw_basis, list) or len(raw_basis) > MAX_BASIS:
        raise Invalid("ideal basis ceiling")
    basis = [poly(p, dim) for p in raw_basis]
    r = len(basis)
    if any(evaluate(p, initial) != 0 for p in basis):
        raise Invalid("initial ideal violation")
    cs = polynomial_matrix(cert["targets"], len(targets), r, dim)
    for target, coefficients in zip(targets, cs, strict=True):
        if target != idealcomb(coefficients, basis):
            raise Invalid("ideal target identity violated")
    if len(cert["steps"]) != len(trans):
        raise Invalid("missing ideal transition certificate")
    for fs, raw in zip(trans, cert["steps"], strict=True):
        hs = polynomial_matrix(raw, r, r, dim)
        for b, h in zip(basis, hs, strict=True):
            if subst(b, fs, dim) != idealcomb(h, basis):
                raise Invalid("ideal pullback identity violated")
    return True
