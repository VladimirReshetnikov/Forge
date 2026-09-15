"""Independent, standard-library-only certificate replay.

This is an executable research checker, NOT a Lean kernel or a verified parser.
Problems are supplied separately from certificates; a certificate cannot change
its target, transitions, ratios, or defining relations. No eval/exec is used.
"""
from __future__ import annotations
from fractions import Fraction as Q
import json
from pathlib import Path
import sys
from typing import Any

MAX_TERMS = 20000
MAX_ITEMS = 10000
MAX_DEGREE = 32
MAX_BITS = 16384
MAX_PRODUCTS = 2000000

class Reject(ValueError):
    pass

class Work:
    def __init__(self) -> None:
        self.left = MAX_PRODUCTS
    def spend(self, n: int = 1) -> None:
        self.left -= n
        if self.left < 0:
            raise Reject('replay product budget exceeded')

def fields(x: Any, expected: set[str]) -> dict:
    if type(x) is not dict or set(x) != expected:
        raise Reject('unexpected or missing fields')
    return x

def nat(x: Any, cap: int = MAX_DEGREE) -> int:
    if type(x) is not int or not 0 <= x <= cap:
        raise Reject('invalid bounded natural')
    return x

def rational(x: Any) -> Q:
    if type(x) is not str or len(x) > 5000:
        raise Reject('rational must be a bounded canonical string')
    try:
        q = Q(x)
    except (ValueError, ZeroDivisionError) as exc:
        raise Reject('invalid rational') from exc
    if str(q) != x or max(abs(q.numerator).bit_length(), q.denominator.bit_length()) > MAX_BITS:
        raise Reject('noncanonical or excessive rational')
    return q

def seq(x: Any, cap: int = MAX_ITEMS) -> list:
    if type(x) is not list or len(x) > cap:
        raise Reject('invalid or oversized list')
    return x

def poly(raw: Any, arity: int, word: bool = False) -> dict[tuple[int, ...], Q]:
    out = {}
    previous = None
    for entry in seq(raw, MAX_TERMS):
        fields(entry, {'m', 'c'})
        m = tuple(seq(entry['m'], MAX_DEGREE if word else 8))
        if word:
            for letter in m:
                nat(letter, arity - 1)
        else:
            if len(m) != arity:
                raise Reject('monomial has wrong arity')
            for e in m:
                nat(e)
            if sum(m) > MAX_DEGREE:
                raise Reject('degree cap exceeded')
        q = rational(entry['c'])
        if q == 0 or (previous is not None and m <= previous):
            raise Reject('duplicate, unsorted, or zero monomial')
        previous = m
        out[m] = q
    return out

def clean(p: dict) -> dict:
    out = {m: c for m, c in p.items() if c}
    if len(out) > MAX_TERMS:
        raise Reject('expanded polynomial too large')
    if any(max(abs(c.numerator).bit_length(), c.denominator.bit_length()) > MAX_BITS for c in out.values()):
        raise Reject('expanded coefficient too large')
    return out

def add(p: dict, q: dict) -> dict:
    r = p.copy()
    for m, c in q.items():
        r[m] = r.get(m, Q(0)) + c
    return clean(r)

def scale(p: dict, c: Q) -> dict:
    return clean({m: v*c for m, v in p.items()})

def mul(p: dict, q: dict, work: Work, word: bool = False) -> dict:
    work.spend(len(p)*len(q))
    r = {}
    for a, c in p.items():
        for b, d in q.items():
            m = a+b if word else tuple(x+y for x, y in zip(a, b, strict=True))
            if (len(m) if word else sum(m)) > MAX_DEGREE:
                raise Reject('expanded degree cap exceeded')
            r[m] = r.get(m, Q(0)) + c*d
    return clean(r)

def power(p: dict, e: int, arity: int, work: Work) -> dict:
    r = {(0,)*arity: Q(1)}
    for _ in range(e):
        r = mul(r, p, work)
    return r

def subst(p: dict, values: list[dict], out_arity: int, work: Work) -> dict:
    out = {}
    for m, c in p.items():
        t = {(0,)*out_arity: c}
        for i, e in enumerate(m):
            t = mul(t, power(values[i], e, out_arity, work), work)
        out = add(out, t)
    return out

def shift(p: dict, arity: int, axis: int, work: Work) -> dict:
    values = []
    for i in range(arity):
        e = [0]*arity
        e[i] = 1
        t = {tuple(e): Q(1)}
        if i == axis:
            t[(0,)*arity] = Q(1)
        values.append(t)
    return subst(p, values, arity, work)

def combination(ps: list[dict], coeffs: Any) -> dict:
    cs = seq(coeffs)
    if len(ps) != len(cs):
        raise Reject('wrong linear-combination length')
    out = {}
    for p, c in zip(ps, cs, strict=True):
        out = add(out, scale(p, rational(c)))
    return out

def invariant(problem: dict, cert: dict, work: Work) -> None:
    fields(problem, {'kind', 'arity', 'param_arity', 'initial', 'transitions', 'target'})
    fields(cert, {'kind', 'basis', 'matrices', 'target_coeffs'})
    n, u = nat(problem['arity'], 8), nat(problem['param_arity'], 8)
    if not n:
        raise Reject('empty state')
    initial = [poly(p, u) for p in seq(problem['initial'], 8)]
    transitions = [[poly(p, n) for p in seq(t, 8)] for t in seq(problem['transitions'], 32)]
    if len(initial) != n or not transitions or any(len(t) != n for t in transitions):
        raise Reject('invalid transition dimensions')
    basis = [poly(p, n) for p in seq(cert['basis'], 256)]
    hs = seq(cert['matrices'], 32)
    if len(hs) != len(transitions):
        raise Reject('missing transition proof')
    for p in basis:
        if subst(p, initial, u, work):
            raise Reject('initial condition fails')
    for t, h in zip(transitions, hs, strict=True):
        rows = seq(h, 256)
        if len(rows) != len(basis):
            raise Reject('matrix has wrong height')
        for p, row in zip(basis, rows, strict=True):
            if subst(p, t, n, work) != combination(basis, row):
                raise Reject('closure identity fails')
    if poly(problem['target'], n) != combination(basis, cert['target_coeffs']):
        raise Reject('target not certified by basis')

def gosper(problem: dict, cert: dict, work: Work) -> None:
    """Checks a rational identity only. Sequence/domain bridges are NOT proved."""
    fields(problem, {'kind', 'A', 'B'})
    fields(cert, {'kind', 'U', 'V'})
    A, B = poly(problem['A'], 1), poly(problem['B'], 1)
    U, V = poly(cert['U'], 1), poly(cert['V'], 1)
    if not A or not B or not V:
        raise Reject('zero ratio or certificate denominator')
    up, vp = shift(U, 1, 0, work), shift(V, 1, 0, work)
    left = add(mul(mul(A, up, work), V, work), scale(mul(mul(B, U, work), vp, work), Q(-1)))
    right = mul(mul(B, V, work), vp, work)
    if left != right:
        raise Reject('antidifference identity fails')

def telescoper(problem: dict, cert: dict, work: Work) -> None:
    """Order-one algebraic telescoper. Boundary/ratio lifting is a separate task."""
    fields(problem, {'kind', 'An', 'Bn', 'Ak', 'Bk'})
    fields(cert, {'kind', 'c0', 'c1', 'U', 'V'})
    An, Bn, Ak, Bk = [poly(problem[k], 2) for k in ['An', 'Bn', 'Ak', 'Bk']]
    c0, c1, U, V = [poly(cert[k], 2) for k in ['c0', 'c1', 'U', 'V']]
    if not An or not Bn or not Ak or not Bk or not V or not c1:
        raise Reject('degenerate telescoper')
    if any(m[1] for p in [c0, c1] for m in p):
        raise Reject('recurrence coefficients depend on summation variable')
    up, vp = shift(U, 2, 1, work), shift(V, 2, 1, work)
    left = mul(mul(mul(add(mul(c0, Bn, work), mul(c1, An, work)), Bk, work), V, work), vp, work)
    right = mul(Bn, add(mul(mul(Ak, up, work), V, work), scale(mul(mul(Bk, U, work), vp, work), Q(-1))), work)
    if left != right:
        raise Reject('creative-telescoping identity fails')

def two_sided(problem: dict, cert: dict, work: Work) -> None:
    fields(problem, {'kind', 'alphabet', 'relations', 'target'})
    fields(cert, {'kind', 'terms'})
    a = nat(problem['alphabet'], 8)
    if not a:
        raise Reject('empty alphabet')
    rs = [poly(p, a, True) for p in seq(problem['relations'], 64)]
    target = poly(problem['target'], a, True)
    out = {}
    for t in seq(cert['terms']):
        fields(t, {'relation', 'left', 'right', 'coefficient'})
        i = nat(t['relation'], len(rs)-1)
        left, right = seq(t['left'], MAX_DEGREE), seq(t['right'], MAX_DEGREE)
        for j in left+right:
            nat(j, a-1)
        part = mul(mul({tuple(left): Q(1)}, rs[i], work, True), {tuple(right): Q(1)}, work, True)
        out = add(out, scale(part, rational(t['coefficient'])))
    if out != target:
        raise Reject('two-sided identity fails')

CHECKS = {'invariant': invariant, 'gosper': gosper, 'telescoper': telescoper, 'two_sided': two_sided}

def verify(problem: Any, cert: Any) -> tuple[bool, str]:
    try:
        if type(problem) is not dict or type(cert) is not dict:
            raise Reject('object required')
        kind = problem.get('kind')
        if kind not in CHECKS or cert.get('kind') != kind:
            raise Reject('kind mismatch')
        CHECKS[kind](problem, cert, Work())
        return True, 'exact identity certificate accepted'
    except (Reject, KeyError, IndexError, TypeError, OverflowError, RecursionError, ValueError) as exc:
        return False, str(exc)

def unique_object(pairs: list[tuple[str, Any]]) -> dict:
    d = {}
    for k, v in pairs:
        if k in d:
            raise Reject('duplicate JSON key')
        d[k] = v
    return d

def load(path: Path) -> Any:
    if path.stat().st_size > 16*1024*1024:
        raise Reject('input file too large')
    return json.loads(path.read_text(), object_pairs_hook=unique_object,
                      parse_float=lambda _: (_ for _ in ()).throw(Reject('JSON floats forbidden')),
                      parse_constant=lambda _: (_ for _ in ()).throw(Reject('nonfinite JSON number')))

def main() -> int:
    root = Path(__file__).resolve().parents[1] / 'results'
    problems = load(Path(sys.argv[1]) if len(sys.argv)>1 else root/'problems.json')
    certificates = load(Path(sys.argv[2]) if len(sys.argv)>2 else root/'certificates.json')
    if set(problems) != set(certificates):
        raise Reject('problem/certificate ID sets differ')
    failures = []
    counts = {}
    for name, p in problems.items():
        ok, reason = verify(p, certificates[name])
        counts[p['kind']] = counts.get(p['kind'], 0) + 1
        if not ok:
            failures.append({'id': name, 'reason': reason})
    print(json.dumps({'accepted': len(problems)-len(failures), 'families': counts,
                      'failures': failures, 'status': 'PYTHON_REPLAY_ONLY'}, indent=2))
    return int(bool(failures))

if __name__ == '__main__':
    raise SystemExit(main())
