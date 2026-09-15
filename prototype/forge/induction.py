"""Structural induction over the list/Nat fragment, with replayed rewrite traces.

PROVENANCE
  BASE  p4-theory-cooperation/prototype/forge_cert/induction.py -- the `flexible`
        variable set carried by every rule (so the induction hypothesis can be
        restricted to the generalised parameters while its tail stays rigid),
        the trace format that records each substitution explicitly, and
        verify_bundle's anti-circularity checks.  Retargeted onto forge/terms.py.
  FOLD  p2-obligation-controller/prototype/forge_proto/induction.py --
        discover_accumulator_lemma and the typed enumerate_list_terms grammar.
  FOLD  p9-proof-planner/forge_lab/induction.py -- TheoremBank (append-only,
        cycle-free) and the specialisation re-derivation, which re-proves the
        original goal from the accepted general lemma instead of assuming it.

Bounded sampling only ever REJECTS a candidate. Acceptance is always a replayed
proof from the defining equations plus previously verified lemmas.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import product
from typing import Iterable, Mapping, Sequence
from .terms import (T, V, F, NIL, ZERO, SIG, Rule, Step, DEFINITIONS, at, replace,
                    positions, match, subst, vars_of, well_typed, make_rule,
                    parse_term, normalize as rewrite_normalize)

DEFS = list(DEFINITIONS)
RESERVED = ('?_head', '?_tail')


# ---------------------------------------------------------------------------
# Rewriting with explicit substitutions (p4).
# ---------------------------------------------------------------------------
def normalize(t: T, rules: Sequence[Rule], limit: int = 1000):
    """Innermost-leftmost normalisation, recording every instantiation."""
    trace: list[dict] = []
    for _ in range(limit):
        step = None
        for path in positions(t):
            sub = at(t, path)
            for r in rules:
                env = match(r.lhs, sub, None, r.instantiable())
                if env is None:
                    continue
                if set(env) != set(r.instantiable()):
                    continue
                value = subst(r.rhs, env)
                if value != sub:
                    step = (path, r, env, value)
                    break
            if step:
                break
        if step is None:
            return t, trace
        path, r, env, value = step
        trace.append({'path': list(path), 'rule': r.name,
                      'subst': {k: v.json() for k, v in sorted(env.items())}})
        t = replace(t, path, value)
    return None, trace


def replay(start: T, trace: Iterable[Mapping], rules: Sequence[Rule]) -> T:
    """The checker does not search or normalise: it checks supplied substitutions."""
    table = {r.name: r for r in rules}
    if len(table) != len(rules):
        raise ValueError('duplicate rule name')
    current = start
    if not well_typed(current):
        raise ValueError('ill-sorted starting term')
    for s in trace:
        r = table[s['rule']]
        if not r.valid_shape():
            raise ValueError('malformed rule')
        env = {k: parse_term(v) for k, v in s['subst'].items()}
        if set(env) != set(r.instantiable()):
            raise ValueError('illegal or missing instantiation')
        sorts = vars_of(r.lhs)
        if any(k not in sorts or env[k].sort != sorts[k] for k in env):
            raise ValueError('bad instantiation sort')
        path = tuple(s['path'])
        if any(type(i) is not int for i in path):
            raise ValueError('bad path')
        if at(current, path) != subst(r.lhs, env):
            raise ValueError('left side mismatch')
        current = replace(current, path, subst(r.rhs, env))
    return current


# ---------------------------------------------------------------------------
# Induction goals (p4).
# ---------------------------------------------------------------------------
def mutation_positions() -> dict[str, set[int]]:
    """Read recursive definitions to find modified nonrecursive arguments."""
    out: dict[str, set[int]] = {}
    for r in DEFS:
        op = r.lhs.sym
        for path in positions(r.rhs):
            call = at(r.rhs, path)
            if call.sym == op:
                for i, (before, after) in enumerate(zip(r.lhs.args, call.args)):
                    if before.variable and before != after:
                        out.setdefault(op, set()).add(i)
    return out


def suggest_generalization(lhs: T, rhs: T, induct: str) -> list[str]:
    mut = mutation_positions()
    out: set[str] = set()
    for term in (lhs, rhs):
        for path in positions(term):
            call = at(term, path)
            for i in mut.get(call.sym, ()):
                out.update(vars_of(call.args[i]))
    return sorted((out & set(vars_of(lhs))) - {induct})


def branches(lhs: T, rhs: T, induct: str, generalized: Sequence[str]):
    vs = dict(vars_of(lhs))
    for k, s in vars_of(rhs).items():
        if k in vs and vs[k] != s:
            raise ValueError('inconsistent variable sort')
        vs[k] = s
    if (not well_typed(lhs) or not well_typed(rhs) or lhs.sort != rhs.sort
            or vs.get(induct) != 'List' or induct in generalized
            or len(set(generalized)) != len(generalized)
            or not set(generalized) <= set(vars_of(lhs)) - {induct}):
        raise ValueError('invalid induction/generalization')
    head, tail = V('_head', 'Elem'), V('_tail')
    if head.sym in vs or tail.sym in vs:
        raise ValueError('reserved fresh-name collision')
    base = (subst(lhs, {induct: NIL}), subst(rhs, {induct: NIL}))
    env = {induct: F('cons', head, tail)}
    step = (subst(lhs, env), subst(rhs, env))
    # The tail is rigid even inside the IH: only generalised parameters may vary.
    ih = make_rule('IH', subst(lhs, {induct: tail}), subst(rhs, {induct: tail}),
                   generalized)
    return base, step, ih


def prove(lhs: T, rhs: T, lemmas: Sequence[Rule] = (), induct: str = '?xs',
          generalize: bool = True) -> dict | None:
    try:
        generalized = suggest_generalization(lhs, rhs, induct) if generalize else []
        base, step, ih = branches(lhs, rhs, induct, generalized)
    except (ValueError, KeyError):
        return None
    rules = DEFS + list(lemmas)
    cert = {'induct': induct, 'generalized': generalized, 'branches': []}
    for (l, r), rs in ((base, rules), (step, rules + [ih])):
        ln, lt = normalize(l, rs)
        rn, rt = normalize(r, rs)
        if ln is None or rn is None or ln != rn:
            return None
        cert['branches'].append({'left': lt, 'right': rt})
    return cert if verify(lhs, rhs, cert, lemmas) else None


def verify(lhs: T, rhs: T, cert: Mapping, lemmas: Sequence[Rule] = ()) -> bool:
    """Prior lemmas must themselves have been verified in an acyclic registry."""
    try:
        base, step, ih = branches(lhs, rhs, cert['induct'], cert['generalized'])
        if len(cert['branches']) != 2:
            return False
        for (l, r), b, rs in zip((base, step), cert['branches'],
                                 (DEFS + list(lemmas), DEFS + list(lemmas) + [ih])):
            if replay(l, b['left'], rs) != replay(r, b['right'], rs):
                return False
        return True
    except (ValueError, KeyError, IndexError, TypeError, RecursionError):
        return False


# ---------------------------------------------------------------------------
# Evaluation oracle used only to reject candidates (p4/p2).
# ---------------------------------------------------------------------------
def eval_term(t: T, env: Mapping[str, object]):
    if t.variable or t.rigid:
        return env[t.sym]
    args = [eval_term(a, env) for a in t.args]
    if t.sym == 'nil':
        return ()
    if t.sym == 'cons':
        return (args[0],) + args[1]
    if t.sym == 'app':
        return args[0] + args[1]
    if t.sym == 'rev':
        return args[0][::-1]
    if t.sym == 'revAcc':
        return args[0][::-1] + args[1]
    if t.sym == 'z':
        return 0
    if t.sym == 's':
        return args[0] + 1
    if t.sym == 'add':
        return args[0] + args[1]
    if t.sym == 'length':
        return len(args[0])
    if t.sym == 'lenAcc':
        return len(args[0]) + args[1]
    raise ValueError('unknown function symbol in candidate evaluation')


def _domain(sort: str):
    if sort == 'List':
        return [(), (0,), (1,), (0, 1)]
    if sort == 'Elem':
        return [0, 1]
    if sort == 'Nat':
        return [0, 1, 2]
    raise ValueError('no sampling domain for sort ' + sort)


def sampled_counterexample(lhs: T, rhs: T) -> dict | None:
    vs = dict(vars_of(lhs))
    vs.update(vars_of(rhs))
    names = sorted(vs)
    for vals in product(*[_domain(vs[v]) for v in names]):
        env = dict(zip(names, vals))
        if eval_term(lhs, env) != eval_term(rhs, env):
            return env
    return None


def candidate_lemmas():
    """Identity/associativity schemas generated from the signature itself."""
    x, y, z = V('x'), V('y'), V('z')
    for op, (ins, out) in SIG.items():
        if ins == ('List', 'List') and out == 'List':
            yield op + '_right_id', F(op, x, NIL), x
            yield op + '_assoc', F(op, F(op, x, y), z), F(op, x, F(op, y, z))
    # The reversal/append anti-homomorphism is an additional explicit schema.
    yield 'rev_app', F('rev', F('app', x, y)), F('app', F('rev', y), F('rev', x))


def synthesize_lemmas():
    verified: list[Rule] = []
    records: list[dict] = []
    for name, lhs, rhs in candidate_lemmas():
        if sampled_counterexample(lhs, rhs) is not None:
            records.append({'name': name, 'status': 'rejected_by_counterexample'})
            continue
        cert = prove(lhs, rhs, verified, induct='?x')
        if cert is None:
            records.append({'name': name, 'status': 'unknown'})
            continue
        if not verify(lhs, rhs, cert, verified):
            raise AssertionError('bad generated proof')
        verified.append(make_rule(name, lhs, rhs))
        records.append({'name': name, 'status': 'proved', 'lhs': lhs.json(),
                        'rhs': rhs.json(), 'certificate': cert})
    return verified, records


def verify_bundle(records: Sequence[Mapping], required: Sequence[str] = ()) -> bool:
    """Replay a topologically ordered lemma bundle from the definitions only.

    Only proved entries are admitted; each entry may use earlier entries, never
    itself or a later conjecture. Definition names and the local IH are reserved.
    Every name in `required` must actually be proved, not merely listed.
    """
    checked: list[Rule] = []
    names = {r.name for r in DEFS} | {'IH'}
    try:
        for rec in records:
            if rec['status'] != 'proved':
                continue
            name = rec['name']
            if not isinstance(name, str) or name in names:
                return False
            lhs, rhs = parse_term(rec['lhs']), parse_term(rec['rhs'])
            lv, rv = vars_of(lhs), vars_of(rhs)
            if lhs.sort != rhs.sort or any(lv[k] != rv[k] for k in lv.keys() & rv.keys()):
                return False
            if not verify(lhs, rhs, rec['certificate'], checked):
                return False
            checked.append(make_rule(name, lhs, rhs))
            names.add(name)
        return set(required) <= {r.name for r in checked}
    except (KeyError, ValueError, TypeError, IndexError, RecursionError):
        return False


# ---------------------------------------------------------------------------
# p9: append-only theorem bank with anti-cyclic admission.
# ---------------------------------------------------------------------------
class TheoremBank:
    """Append-only verified dependency order; self/cyclic lemma uses rejected."""

    def __init__(self) -> None:
        self._rules: list[Rule] = []
        self.certificates: dict[str, tuple[T, T, dict]] = {}

    @property
    def rules(self) -> tuple[Rule, ...]:
        return tuple(self._rules)

    def add(self, name: str, lhs: T, rhs: T, cert: Mapping) -> bool:
        if name == 'IH' or name in {r.name for r in DEFS} | {r.name for r in self._rules}:
            return False
        try:
            rule = make_rule(name, lhs, rhs)
        except (ValueError, KeyError):
            return False
        if not verify(lhs, rhs, cert, self._rules):
            return False
        self._rules.append(rule)
        self.certificates[name] = (lhs, rhs, dict(cert))
        return True


def standard_bank() -> TheoremBank:
    bank = TheoremBank()
    x, y, z = V('xs'), V('ys'), V('zs')
    goals = [('app_right_nil', F('app', x, NIL), x),
             ('app_assoc', F('app', F('app', x, y), z), F('app', x, F('app', y, z)))]
    for name, lhs, rhs in goals:
        cert = prove(lhs, rhs, bank.rules)
        if cert is None or not bank.add(name, lhs, rhs, cert):
            raise RuntimeError('Foundational list certificate failed')
    return bank


def specialize(lhs: T, rhs: T, bank: TheoremBank) -> tuple[bool, dict]:
    """Re-derive a specialised goal from the bank instead of assuming it (p9)."""
    rules = tuple(DEFINITIONS) + bank.rules
    l, lt = rewrite_normalize(lhs, rules)
    r, rt = rewrite_normalize(rhs, rules)
    table = {x.name: x for x in rules}
    from .terms import replay as trace_replay
    ok = (l == r and trace_replay(lhs, lt, table) is not None
          and trace_replay(lhs, lt, table) == trace_replay(rhs, rt, table))
    return ok, {'goal': {'lhs': lhs.json(), 'rhs': rhs.json()},
                'left': [s.json() for s in lt], 'right': [s.json() for s in rt]}


# ---------------------------------------------------------------------------
# p2: accumulator-lemma discovery over a typed grammar.
# ---------------------------------------------------------------------------
def changed_recursive_arguments(symbol: str) -> set[int]:
    """Non-constructor-pattern arguments changed at recursive call sites."""
    if symbol not in SIG:
        raise ValueError('unknown symbol')
    changing: set[int] = set()
    for rule in DEFS:
        if rule.lhs.sym != symbol:
            continue
        for path in positions(rule.rhs):
            call = at(rule.rhs, path)
            if call.sym != symbol:
                continue
            for i, (old, new) in enumerate(zip(rule.lhs.args, call.args)):
                if old.variable and new != old:
                    changing.add(i)
    return changing


def enumerate_list_terms(atoms: Iterable[T], max_size: int):
    """Typed grammar L ::= atom | rev(L) | app(L,L), enumerated by node count."""
    base = sorted(set(atoms), key=str)
    for t in base:
        if t.sort != 'List':
            raise ValueError('list atoms required')
    levels: dict[int, list[T]] = {1: base}
    yield from base
    for size in range(2, max_size + 1):
        terms = {F('rev', t) for t in levels.get(size - 1, [])}
        for left_size in range(1, size - 1):
            right_size = size - 1 - left_size
            terms.update(F('app', a, b) for a in levels.get(left_size, [])
                         for b in levels.get(right_size, []))
        levels[size] = sorted(terms, key=str)
        yield from levels[size]


@dataclass
class DiscoveryResult:
    lhs: T | None
    rhs: T | None
    certificate: dict | None
    enumerated: int
    sample_survivors: int
    changed_arguments: tuple[int, ...]


def discover_accumulator_lemma(goal_lhs: T, goal_rhs: T, lemmas: Sequence[Rule] = (),
                               induct: str = '?xs', max_size: int = 5) -> DiscoveryResult:
    """Generalise changed nil arguments, then synthesise the RHS by a grammar.

    Bounded candidate testing only filters. The returned candidate must pass an
    exact induction replay before it is reported as a discovered theorem.
    """
    if goal_lhs.sym not in SIG:
        raise ValueError('a function application is required')
    changed = changed_recursive_arguments(goal_lhs.sym)
    args = list(goal_lhs.args)
    names = dict(vars_of(goal_lhs))
    names.update(vars_of(goal_rhs))
    generated = []
    for index in sorted(changed):
        if args[index] == NIL:
            name = '?acc%d' % index
            while name in names:
                name += '_'
            args[index] = T(name, (), 'List')
            names[name] = 'List'
            generated.append(name)
    if not generated:
        return DiscoveryResult(None, None, None, 0, 0, tuple(sorted(changed)))
    lhs = T(goal_lhs.sym, tuple(args), goal_lhs.sort)
    parameters = sorted(vars_of(lhs))
    if any(vars_of(lhs)[name] != 'List' for name in parameters):
        raise ValueError('this synthesis grammar supports only list parameters')
    lists = [tuple(bits) for n in range(3) for bits in product((0, 1), repeat=n)]
    samples = [dict(zip(parameters, vals)) for vals in product(lists, repeat=len(parameters))]
    signature = tuple(eval_term(lhs, s) for s in samples)
    count = survivors = 0
    for rhs in enumerate_list_terms([NIL, *(T(p, (), 'List') for p in parameters)], max_size):
        count += 1
        if tuple(eval_term(rhs, s) for s in samples) != signature:
            continue
        survivors += 1
        cert = prove(lhs, rhs, lemmas, induct)
        if cert is not None:
            return DiscoveryResult(lhs, rhs, cert, count, survivors, tuple(sorted(changed)))
    return DiscoveryResult(None, None, None, count, survivors, tuple(sorted(changed)))


def synthesize_accumulator(max_size: int = 5) -> tuple[TheoremBank, dict]:
    """Full pipeline: seed bank -> generalise -> synthesise -> specialise (p9/p2)."""
    bank = standard_bank()
    xs = V('xs')
    original_lhs, original_rhs = F('revAcc', xs, NIL), F('rev', xs)
    direct = prove(original_lhs, original_rhs, bank.rules)
    found = discover_accumulator_lemma(original_lhs, original_rhs, bank.rules)
    if found.certificate is None:
        return bank, {'status': 'no_certificate', 'candidate_count': found.enumerated,
                      'sample_survivors': found.sample_survivors}
    if not bank.add('revAcc_spec', found.lhs, found.rhs, found.certificate):
        return bank, {'status': 'bank_rejected'}
    ok, trace = specialize(original_lhs, original_rhs, bank)
    return bank, {'status': 'certified',
                  'direct_induction_succeeded': direct is not None,
                  'candidate_count': found.enumerated,
                  'sample_survivors': found.sample_survivors,
                  'changed_arguments': list(found.changed_arguments),
                  'lemma': str(found.lhs) + ' = ' + str(found.rhs),
                  'specialization_checked': ok, 'specialization': trace}
