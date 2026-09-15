"""Typed first-order terms and deterministic rewrite traces for the list fragment."""
from __future__ import annotations
from dataclasses import dataclass
from typing import Mapping

SIG = {
    'nil': ((), 'List'), 'cons': (('Elem', 'List'), 'List'),
    'app': (('List', 'List'), 'List'), 'rev': (('List',), 'List'),
    'revAcc': (('List', 'List'), 'List'),
    'a': ((), 'U'), 'f': (('U',), 'U'), 'g': (('U',), 'U'),
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
        return not t.args and t.sort in ('List', 'Elem', 'U')
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


def match(pattern: T, term: T, env: dict[str, T] | None = None) -> dict[str, T] | None:
    env = {} if env is None else dict(env)
    if pattern.sort != term.sort:
        return None
    if pattern.variable:
        if pattern.sym in env:
            return env if env[pattern.sym] == term else None
        env[pattern.sym] = term
        return env
    if pattern.sym != term.sym or len(pattern.args) != len(term.args):
        return None
    for a, b in zip(pattern.args, term.args):
        env = match(a, b, env)
        if env is None:
            return None
    return env

@dataclass(frozen=True)
class Rule:
    name: str
    lhs: T
    rhs: T

    def valid_shape(self) -> bool:
        return (well_typed(self.lhs) and well_typed(self.rhs)
                and self.lhs.sort == self.rhs.sort
                and set(vars_of(self.rhs)) <= set(vars_of(self.lhs)))

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


def replay(start: T, steps: tuple[Step, ...], rules: Mapping[str, Rule]) -> T | None:
    """Check each exact local equality step; not a search procedure."""
    try:
        if not well_typed(start):
            return None
        t = start
        for st in steps:
            r = rules[st.rule]
            if not r.valid_shape():
                return None
            env = match(r.lhs, at(t, st.path))
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
                env = match(r.lhs, at(t, path))
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

x, xs, ys, acc = V('x', 'Elem'), V('xs'), V('ys'), V('acc')
NIL = F('nil')
DEFINITIONS = (
    Rule('app.nil', F('app', NIL, ys), ys),
    Rule('app.cons', F('app', F('cons', x, xs), ys), F('cons', x, F('app', xs, ys))),
    Rule('rev.nil', F('rev', NIL), NIL),
    Rule('rev.cons', F('rev', F('cons', x, xs)), F('app', F('rev', xs), F('cons', x, NIL))),
    Rule('revAcc.nil', F('revAcc', NIL, acc), acc),
    Rule('revAcc.cons', F('revAcc', F('cons', x, xs), acc), F('revAcc', xs, F('cons', x, acc))),
)
