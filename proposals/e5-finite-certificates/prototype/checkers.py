"""Independent, standard-library-only certificate replay.

No search, symbolic algebra library, eval, or imported search representation.
The caller supplies the problem separately. A True result is Python validation,
NOT a Lean proof. Resource caps are defensive limits, not a sandbox guarantee.
"""
from __future__ import annotations
from fractions import Fraction as Q
from math import gcd
import json
from pathlib import Path

MAX_DIM = 16
MAX_TERMS = 20000
MAX_DEGREE = 128
MAX_BITS = 4096
MAX_BYTES = 12_000_000
Poly = dict[tuple[int, ...], Q]

class Invalid(ValueError):
    """Malformed or unsupported input, distinct from a false identity."""

def integer(x):
    if type(x) is not int or x.bit_length() > MAX_BITS:
        raise Invalid('expected bounded integer, not bool/float')
    return x

def rat(x):
    if not isinstance(x, list) or len(x) != 2:
        raise Invalid('rational must be [numerator, denominator]')
    a, b = map(integer, x)
    if b <= 0 or gcd(a, b) != 1:
        raise Invalid('rational is not canonical')
    return Q(a, b)

def dim(n):
    integer(n)
    if not 0 <= n <= MAX_DIM:
        raise Invalid('dimension out of bounds')
    return n

def poly(raw, n):
    """Canonical sorted sparse list: [[exponent_vector, rational], ...]."""
    dim(n)
    if not isinstance(raw, list) or len(raw) > MAX_TERMS:
        raise Invalid('invalid polynomial list')
    out: Poly = {}
    prev = None
    for item in raw:
        if not isinstance(item, list) or len(item) != 2:
            raise Invalid('invalid monomial entry')
        es, cr = item
        if not isinstance(es, list) or len(es) != n:
            raise Invalid('incorrect arity')
        e = tuple(integer(i) for i in es)
        if any(i < 0 for i in e) or sum(e) > MAX_DEGREE:
            raise Invalid('invalid exponent')
        if prev is not None and not prev < e:
            raise Invalid('duplicate or unordered monomials')
        c = rat(cr)
        if not c:
            raise Invalid('explicit zero coefficient')
        out[e] = c
        prev = e
    return out

def bounded(p):
    if len(p) > MAX_TERMS:
        raise Invalid('intermediate term cap')
    for e, c in p.items():
        if sum(e) > MAX_DEGREE or max(c.numerator.bit_length(), c.denominator.bit_length()) > MAX_BITS:
            raise Invalid('intermediate degree/coefficient cap')
    return p

def add(p, q):
    r = dict(p)
    for e, c in q.items():
        z = r.get(e, Q(0)) + c
        if z:
            r[e] = z
        else:
            r.pop(e, None)
    return bounded(r)

def neg(p):
    return {e: -c for e, c in p.items()}

def sub(p, q):
    return add(p, neg(q))

def mul(p, q):
    r: Poly = {}
    for e, c in p.items():
        for f, d in q.items():
            g = tuple(x + y for x, y in zip(e, f))
            z = r.get(g, Q(0)) + c*d
            if z:
                r[g] = z
            else:
                r.pop(g, None)
        bounded(r)
    return r

def const(c, n):
    return {(0,)*n: Q(c)} if c else {}

def var(i, n):
    return {tuple(int(j == i) for j in range(n)): Q(1)}

def power(p, a, n):
    r = const(1, n)
    while a:
        if a & 1:
            r = mul(r, p)
        a //= 2
        if a:
            p = mul(p, p)
    return r

def compose(p, values, nout):
    r: Poly = {}
    cache = {(i, 0): const(1, nout) for i in range(len(values))}
    for e, c in p.items():
        if len(e) != len(values):
            raise Invalid('composition arity')
        t = const(c, nout)
        for i, exponent in enumerate(e):
            key = (i, exponent)
            if key not in cache:
                cache[key] = power(values[i], exponent, nout)
            t = mul(t, cache[key])
        r = add(r, t)
    return r

def dot(a, b):
    if len(a) != len(b):
        raise Invalid('dot-product dimension')
    return sum((x*y for x, y in zip(a, b)), Q(0))

def matrix(raw, rows, cols):
    if not isinstance(raw, list) or len(raw) != rows:
        raise Invalid('matrix row count')
    out = []
    for r in raw:
        if not isinstance(r, list) or len(r) != cols:
            raise Invalid('matrix column count')
        out.append([rat(c) for c in r])
    return out

def matmul(a, b, inner, cols):
    if len(b) != inner:
        raise Invalid('matrix inner dimension')
    return [[dot(row, [b[k][j] for k in range(inner)]) for j in range(cols)] for row in a]

def linear(problem, cert):
    if problem.get('kind') != 'linear' or cert.get('kind') != 'linear':
        return False
    n = dim(problem['dimension'])
    if n == 0:
        raise Invalid('empty state')
    q = matrix([problem['target']], 1, n)
    s = matrix([problem['initial']], 1, n)[0]
    acts = [matrix(a, n, n) for a in problem['actions']]
    if not acts or len(acts) > 32:
        raise Invalid('action count')
    r = dim(len(cert['basis']))
    g = matrix(cert['basis'], r, n)
    t = matrix([cert['target_weights']], 1, r)
    cs = cert['action_weights']
    if len(cs) != len(acts):
        return False
    if matmul(t, g, r, n) != q or any(dot(row, s) != 0 for row in g):
        return False
    for a, raw_c in zip(acts, cs):
        c = matrix(raw_c, r, r)
        if matmul(g, a, n, n) != matmul(c, g, r, n):
            return False
    return True

def ideal(problem, cert):
    if problem.get('kind') != 'ideal' or cert.get('kind') != 'ideal':
        return False
    n, k = dim(problem['dimension']), dim(problem['parameters'])
    q = poly(problem['target'], n)
    fs = [[poly(f, n) for f in action] for action in problem['actions']]
    initial = [poly(f, k) for f in problem['initial']]
    if n == 0 or len(initial) != n or not fs or any(len(f) != n for f in fs):
        raise Invalid('polynomial map dimensions')
    g = [poly(p, n) for p in cert['generators']]
    if not 1 <= len(g) <= 32:
        raise Invalid('generator count')
    h = [poly(p, n) for p in cert['target_weights']]
    hs = cert['action_weights']
    if len(h) != len(g) or len(hs) != len(fs):
        return False
    reconstruction: Poly = {}
    for hi, gi in zip(h, g):
        reconstruction = add(reconstruction, mul(hi, gi))
    if reconstruction != q or any(compose(gi, initial, k) for gi in g):
        return False
    for f, raw_h in zip(fs, hs):
        if len(raw_h) != len(g):
            return False
        for gi, raw_row in zip(g, raw_h):
            if len(raw_row) != len(g):
                return False
            rhs: Poly = {}
            for hij, gj in zip(raw_row, g):
                rhs = add(rhs, mul(poly(hij, n), gj))
            if compose(gi, f, n) != rhs:
                return False
    return True

def summation(problem, cert):
    """Check a pole-free order-one recurrence, not a closed form.

Primitive source identity: k*B=(n+1-k)*A for A=C(n,k-1),
B=C(n,k); Pascal supplies C(n+1,k)=A+B. Domain n,k >= 0.
"""
    if problem.get('kind') != 'binomial_sum' or cert.get('kind') != 'binomial_sum':
        return False
    m = integer(problem['power'])
    if not 1 <= m <= 6:
        raise Invalid('power outside prototype fragment')
    weight = poly(problem['weight'], 1)  # variable k
    p0 = poly(cert['p0'], 1)             # variable n
    p1 = poly(cert['p1'], 1)
    r = poly(cert['r'], 2)               # variables n,k
    h = poly(cert['relation_multiplier'], 4) # variables A,B,n,k
    if not p1:
        return False
    A, B, n, k = (var(i, 4) for i in range(4))
    one = const(1, 4)
    wk = compose(weight, [k], 4)
    Bm = power(B, m, 4)
    lhs = mul(wk, add(mul(compose(p1, [n], 4), power(add(A, B), m, 4)),
                      mul(compose(p0, [n], 4), Bm)))
    delta = sub(mul(compose(r, [n, add(k, one)], 4), Bm),
                mul(compose(r, [n, k], 4), power(A, m, 4)))
    relation = sub(mul(sub(add(n, one), k), A), mul(k, B))
    return sub(lhs, delta) == mul(h, relation)

def verify(problem, certificate):
    """Fail closed on malformed input. No invocation of a search algorithm."""
    try:
        return {'linear': linear, 'ideal': ideal, 'binomial_sum': summation}[problem['kind']](problem, certificate)
    except (Invalid, KeyError, TypeError, ValueError, IndexError, OverflowError):
        return False

def counterexample(problem, witness):
    """Concrete replay of a source-IR counterexample, using only Fraction."""
    try:
        word = witness['word']
        if not isinstance(word, list) or len(word) > 10000:
            return False
        for a in word:
            integer(a)
            if not 0 <= a < len(problem['actions']):
                return False
        n = dim(problem['dimension'])
        if problem['kind'] == 'linear':
            state = matrix([problem['initial']], 1, n)[0]
            acts = [matrix(a, n, n) for a in problem['actions']]
            for a in word:
                state = [dot(row, state) for row in acts[a]]
            target = matrix([problem['target']], 1, n)[0]
            value = dot(target, state)
        elif problem['kind'] == 'ideal':
            k = dim(problem['parameters'])
            ps = witness['parameters']
            if not isinstance(ps, list) or len(ps) != k:
                return False
            vals = [const(integer(v), 0) for v in ps]
            state = [compose(poly(f, k), vals, 0) for f in problem['initial']]
            acts = [[poly(f,n) for f in a] for a in problem['actions']]
            if len(state) != n or any(len(a) != n for a in acts):
                return False
            for a in word:
                state = [compose(f, state, 0) for f in acts[a]]
            value = compose(poly(problem['target'], n), state, 0).get((), Q(0))
        else:
            return False
        return value != 0 and value == rat(witness['value'])
    except (Invalid, KeyError, TypeError, ValueError, IndexError, OverflowError):
        return False

def unique_pairs(pairs):
    out = {}
    for k, v in pairs:
        if k in out:
            raise Invalid('duplicate JSON key')
        out[k] = v
    return out

def load_bundle(path):
    p = Path(path)
    if p.stat().st_size > MAX_BYTES:
        raise Invalid('input byte cap')
    return json.loads(p.read_text(), object_pairs_hook=unique_pairs,
                      parse_float=lambda _: (_ for _ in ()).throw(Invalid('float token')))

if __name__ == '__main__':
    import argparse, sys
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('paths', nargs='+', type=Path)
    args = parser.parse_args()
    paths = []
    for path in args.paths:
        paths.extend(sorted(path.glob('*.json')) if path.is_dir() else [path])
    failures = []
    for path in paths:
        try:
            b = load_bundle(path)
            ok = (verify(b['problem'], b['certificate']) if 'certificate' in b
                  else counterexample(b['problem'], b['counterexample']))
        except (OSError, Invalid, ValueError, KeyError):
            ok = False
        print(f'{"PASS" if ok else "FAIL"} {path.name}')
        if not ok:
            failures.append(str(path))
    print(json.dumps({'checked': len(paths), 'failed': failures, 'site_packages_enabled': not sys.flags.no_site}))
    sys.exit(bool(failures) or not paths)
