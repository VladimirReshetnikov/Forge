"""Typed first-order terms and deterministic rewrite traces.

PROVENANCE
  BASE  p9-proof-planner/forge_lab/terms.py -- sorted signature, '?'-prefixed
        match variables, '$'-prefixed rigid constants, well_typed gate, match /
        subst / at / replace, Step traces, replay (checking, never searching),
        and normalize (searching).
  FOLD  p3-planner-certificate-layer/prototype/induction.py -- its Nat sort,
        together with the add / length / lenAcc defining equations.
  FOLD  p4-theory-cooperation/prototype/forge_cert/induction.py -- Rule gains an
        optional `flexible` variable set; None means "every variable of the lhs",
        which is exactly p9's behaviour, so p9 rules are unchanged.

This is a small object logic, not Lean and not a general rewriting engine.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Mapping

SORTS = ('List', 'Elem', 'U', 'Nat')

SIG = {
    'nil': ((), 'List'), 'cons': (('Elem', 'List'), 'List'),
    'app': (('List', 'List'), 'List'), 'rev': (('List',), 'List'),
    'revAcc': (('List', 'List'), 'List'),
    'a': ((), 'U'), 'f': (('U',), 'U'), 'g': (('U',), 'U'),
    # p3's Nat fragment.
    'z': ((), 'Nat'), 's': (('Nat',), 'Nat'),
    'add': (('Nat', 'Nat'), 'Nat'),
    'length': (('List',), 'Nat'), 'lenAcc': (('List', 'Nat'), 'Nat'),
}


@dataclass(frozen=True)
class T:
    sym: str
    args: tuple['T', ...] = ()
    sort: str = 'List'

    @property
    def variable(self) -> bool:
        return self.sym.startswith('?')

    @property
    def rigid(self) -> bool:
        return self.sym.startswith('$')

    @property
    def size(self) -> int:
        return 1 + sum(a.size for a in self.args)

    def __str__(self) -> str:
        if not self.args:
            return self.sym
        return self.sym + '(' + ', '.join(map(str, self.args)) + ')'

    def json(self) -> dict:
        return {'symbol': self.sym, 'sort': self.sort, 'args': [a.json() for a in self.args]}


def V(name: str, sort: str = 'List') -> T:
    return T('?' + name, (), sort)


def rigid(name: str, sort: str = 'List') -> T:
    return T('$' + name, (), sort)


def F(name: str, *args: T) -> T:
    ins, out = SIG[name]
    if tuple(a.sort for a in args) != ins:
        raise ValueError('Ill-sorted application: ' + name)
    return T(name, tuple(args), out)


def well_typed(t: T) -> bool:
    if t.sym.startswith(('?', '$')):
        return not t.args and t.sort in SORTS
    if t.sym not in SIG:
        return False
    ins, out = SIG[t.sym]
    return out == t.sort and tuple(a.sort for a in t.args) == ins and all(map(well_typed, t.args))


def vars_of(t: T) -> dict[str, str]:
    out = {t.sym: t.sort} if t.variable else {}
    for a in t.args:
        for k, s in vars_of(a).items():
            if k in out and out[k] != s:
                raise ValueError('Variable occurs at incompatible sorts')
            out[k] = s
    return out


def subst(t: T, env: Mapping[str, T]) -> T:
    if t.variable and t.sym in env:
        if env[t.sym].sort != t.sort:
            raise ValueError('Ill-sorted substitution')
        return env[t.sym]
    return T(t.sym, tuple(subst(a, env) for a in t.args), t.sort)


def match(pattern: T, term: T, env: dict[str, T] | None = None,
          allowed: frozenset[str] | None = None) -> dict[str, T] | None:
    """Match `pattern` against `term`.

    `allowed` (p4) restricts which pattern variables may be instantiated; every
    other variable is rigid and must occur literally. None means "all of them".
    """
    env = {} if env is None else dict(env)
    if pattern.sort != term.sort:
        return None
    if pattern.variable and (allowed is None or pattern.sym in allowed):
        if pattern.sym in env:
            return env if env[pattern.sym] == term else None
        env[pattern.sym] = term
        return env
    if pattern.sym != term.sym or len(pattern.args) != len(term.args):
        return None
    for a, b in zip(pattern.args, term.args):
        env = match(a, b, env, allowed)
        if env is None:
            return None
    return env


@dataclass(frozen=True)
class Rule:
    name: str
    lhs: T
    rhs: T
    flexible: frozenset[str] | None = None

    def instantiable(self) -> frozenset[str]:
        return frozenset(vars_of(self.lhs)) if self.flexible is None else self.flexible

    def valid_shape(self) -> bool:
        try:
            return (well_typed(self.lhs) and well_typed(self.rhs)
                    and self.lhs.sort == self.rhs.sort
                    and set(vars_of(self.rhs)) <= set(vars_of(self.lhs))
                    and self.instantiable() <= set(vars_of(self.lhs)))
        except ValueError:
            return False


def make_rule(name: str, lhs: T, rhs: T, flexible=None) -> Rule:
    r = Rule(name, lhs, rhs, None if flexible is None else frozenset(flexible))
    if not r.valid_shape():
        raise ValueError('invalid oriented equation')
    return r


@dataclass(frozen=True)
class Step:
    path: tuple[int, ...]
    rule: str

    def json(self) -> dict:
        return {'path': list(self.path), 'rule': self.rule}


def at(t: T, path: tuple[int, ...]) -> T:
    for i in path:
        if type(i) is not int or i < 0 or i >= len(t.args):
            raise ValueError('Invalid path')
        t = t.args[i]
    return t


def replace(t: T, path: tuple[int, ...], new: T) -> T:
    if not path:
        if t.sort != new.sort:
            raise ValueError('Ill-sorted replacement')
        return new
    i, *rest = path
    at(t, (i,))
    args = list(t.args)
    args[i] = replace(args[i], tuple(rest), new)
    return T(t.sym, tuple(args), t.sort)


def positions(t: T, path: tuple[int, ...] = ()):
    for i, a in enumerate(t.args):
        yield from positions(a, path + (i,))
    yield path


def replay(start: T, steps: tuple[Step, ...], rules: Mapping[str, Rule]) -> T | None:
    """Check each exact local equality step; this is not a search procedure."""
    try:
        if not well_typed(start):
            return None
        t = start
        for st in steps:
            r = rules[st.rule]
            if not r.valid_shape():
                return None
            env = match(r.lhs, at(t, st.path), None, r.instantiable())
            if env is None:
                return None
            t = replace(t, st.path, subst(r.rhs, env))
        return t
    except (KeyError, ValueError, IndexError):
        return None


def normalize(start: T, rules: tuple[Rule, ...], budget: int = 1000) -> tuple[T, tuple[Step, ...]]:
    t = start
    trace: list[Step] = []

    def visit(path: tuple[int, ...]) -> None:
        nonlocal t
        for i in range(len(at(t, path).args)):
            visit(path + (i,))
        while True:
            for r in rules:
                env = match(r.lhs, at(t, path), None, r.instantiable())
                if env is None:
                    continue
                new = subst(r.rhs, env)
                if new == at(t, path):
                    continue
                if len(trace) >= budget:
                    raise RuntimeError('Rewrite budget exceeded')
                t = replace(t, path, new)
                trace.append(Step(path, r.name))
                for i in range(len(new.args)):
                    visit(path + (i,))
                break
            else:
                return

    visit(())
    return t, tuple(trace)


def parse_term(o, depth: int = 0) -> T:
    """Decode a term from T.json() output, rejecting anything ill-sorted."""
    if depth > 128 or not isinstance(o, dict) or set(o) != {'symbol', 'sort', 'args'}:
        raise ValueError('Bad term object')
    if not isinstance(o['symbol'], str) or not isinstance(o['args'], list):
        raise ValueError('Bad term object')
    t = T(o['symbol'], tuple(parse_term(a, depth + 1) for a in o['args']), o['sort'])
    if not well_typed(t):
        raise ValueError('Ill-sorted term')
    return t


x, xs, ys, acc = V('x', 'Elem'), V('xs'), V('ys'), V('acc')
m, k = V('m', 'Nat'), V('k', 'Nat')
NIL = F('nil')
ZERO = F('z')

DEFINITIONS = (
    Rule('app.nil', F('app', NIL, ys), ys),
    Rule('app.cons', F('app', F('cons', x, xs), ys), F('cons', x, F('app', xs, ys))),
    Rule('rev.nil', F('rev', NIL), NIL),
    Rule('rev.cons', F('rev', F('cons', x, xs)), F('app', F('rev', xs), F('cons', x, NIL))),
    Rule('revAcc.nil', F('revAcc', NIL, acc), acc),
    Rule('revAcc.cons', F('revAcc', F('cons', x, xs), acc), F('revAcc', xs, F('cons', x, acc))),
    Rule('add.z', F('add', ZERO, m), m),
    Rule('add.s', F('add', F('s', k), m), F('s', F('add', k, m))),
    Rule('length.nil', F('length', NIL), ZERO),
    Rule('length.cons', F('length', F('cons', x, xs)), F('s', F('length', xs))),
    Rule('lenAcc.nil', F('lenAcc', NIL, m), m),
    Rule('lenAcc.cons', F('lenAcc', F('cons', x, xs), m), F('lenAcc', xs, F('s', m))),
)
