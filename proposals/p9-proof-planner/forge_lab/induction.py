"""Accumulator-lemma synthesis with explicit, independently replayed induction.

The checker is specific to the freely generated List datatype and the fixed
recursive definitions in terms.py. It is not a general Lean proof checker.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import product
from time import perf_counter
from .terms import T, V, F, NIL, rigid, vars_of, subst, Rule, Step
from .terms import DEFINITIONS, normalize, replay, well_typed

@dataclass(frozen=True)
class EqGoal:
    lhs: T
    rhs: T

    def json(self) -> dict:
        return {'lhs': self.lhs.json(), 'rhs': self.rhs.json()}

@dataclass(frozen=True)
class InductionCertificate:
    variable: str
    generalized: tuple[str, ...]
    nil_left: tuple[Step, ...]
    nil_right: tuple[Step, ...]
    cons_left: tuple[Step, ...]
    cons_right: tuple[Step, ...]

    def json(self) -> dict:
        return {'kind': 'list_induction', 'variable': self.variable,
                'generalized': list(self.generalized),
                'cases': {k: [s.json() for s in getattr(self, k)]
                          for k in ('nil_left', 'nil_right', 'cons_left', 'cons_right')}}


def case_data(goal: EqGoal, variable: str, generalized: tuple[str, ...]):
    lv, rv = vars_of(goal.lhs), vars_of(goal.rhs)
    if any(lv[v] != rv[v] for v in lv.keys() & rv.keys()):
        raise ValueError('Inconsistent variable sorts across equality')
    vs = lv | rv
    # No external rigid constants: all eigenvariables are introduced here.
    def contains_rigid(t: T) -> bool:
        return t.sym.startswith('$') or any(contains_rigid(a) for a in t.args)
    if (not well_typed(goal.lhs) or not well_typed(goal.rhs)
            or goal.lhs.sort != goal.rhs.sort or contains_rigid(goal.lhs) or contains_rigid(goal.rhs)
            or vs.get(variable) != 'List' or variable in generalized
            or len(set(generalized)) != len(generalized)
            or not set(generalized) <= set(vs)):
        raise ValueError('Invalid induction request')
    fixed = {v: rigid('param.' + v[1:], s) for v, s in vs.items() if v != variable}
    tail, head = rigid('tail'), rigid('head', 'Elem')
    zero = fixed | {variable: NIL}
    succ = fixed | {variable: F('cons', head, tail)}
    # The tail is rigid, even inside the IH. Only generalised parameters match.
    ih_env = {v: t for v, t in fixed.items() if v not in generalized} | {variable: tail}
    ih = Rule('IH', subst(goal.lhs, ih_env), subst(goal.rhs, ih_env))
    return (EqGoal(subst(goal.lhs, zero), subst(goal.rhs, zero)),
            EqGoal(subst(goal.lhs, succ), subst(goal.rhs, succ)), ih)


def prove_induction(goal: EqGoal, variable: str, lemmas: tuple[Rule, ...] = (),
                    generalized: tuple[str, ...] = ()) -> InductionCertificate | None:
    try:
        base, step, ih = case_data(goal, variable, generalized)
        rules = DEFINITIONS + lemmas
        a, at = normalize(base.lhs, rules)
        b, bt = normalize(base.rhs, rules)
        if a != b:
            return None
        c, ct = normalize(step.lhs, rules + (ih,))
        d, dt = normalize(step.rhs, rules + (ih,))
        if c != d:
            return None
        return InductionCertificate(variable, generalized, at, bt, ct, dt)
    except (ValueError, RuntimeError, RecursionError):
        return None


def check_induction(goal: EqGoal, cert: InductionCertificate,
                    accepted_lemmas: tuple[Rule, ...] = ()) -> bool:
    """Accepted lemmas MUST come from an already checked acyclic theorem bank."""
    try:
        base, step, ih = case_data(goal, cert.variable, cert.generalized)
        rules = {r.name: r for r in DEFINITIONS + accepted_lemmas}
        if 'IH' in rules or len(rules) != len(DEFINITIONS) + len(accepted_lemmas):
            return False
        a = replay(base.lhs, cert.nil_left, rules)
        b = replay(base.rhs, cert.nil_right, rules)
        # The base case never receives an induction hypothesis.
        rules['IH'] = ih
        c = replay(step.lhs, cert.cons_left, rules)
        d = replay(step.rhs, cert.cons_right, rules)
        return a is not None and a == b and c is not None and c == d
    except (ValueError, TypeError):
        return False


class TheoremBank:
    """Append-only verified dependency order; self/cyclic lemma uses rejected."""
    def __init__(self):
        self._rules: list[Rule] = []
        self.certificates: dict[str, tuple[EqGoal, InductionCertificate]] = {}

    @property
    def rules(self) -> tuple[Rule, ...]:
        return tuple(self._rules)

    def add(self, name: str, goal: EqGoal, cert: InductionCertificate) -> bool:
        if name == 'IH' or name in {r.name for r in DEFINITIONS + self.rules}:
            return False
        r = Rule(name, goal.lhs, goal.rhs)
        if not r.valid_shape() or not check_induction(goal, cert, self.rules):
            return False
        self._rules.append(r)
        self.certificates[name] = (goal, cert)
        return True


def eval_list(t: T, env: dict[str, tuple]) -> tuple:
    if t.variable:
        return env[t.sym]
    if t.sym == 'nil':
        return ()
    if t.sym == 'app':
        return eval_list(t.args[0], env) + eval_list(t.args[1], env)
    if t.sym == 'rev':
        return eval_list(t.args[0], env)[::-1]
    if t.sym == 'revAcc':
        return eval_list(t.args[0], env)[::-1] + eval_list(t.args[1], env)
    raise ValueError('Unsupported grammar term in candidate evaluation')


def enumerate_rhs(max_size: int = 6):
    by_size: dict[int, list[T]] = {1: [V('xs'), V('acc'), NIL]}
    yield from by_size[1]
    for size in range(2, max_size + 1):
        ts = [F('rev', t) for t in by_size.get(size - 1, [])]
        for i in range(1, size - 1):
            for a in by_size.get(i, []):
                for b in by_size.get(size - 1 - i, []):
                    ts.append(F('app', a, b))
        by_size[size] = ts
        yield from ts


def standard_bank() -> TheoremBank:
    bank = TheoremBank()
    xs, ys, zs = V('xs'), V('ys'), V('zs')
    goals = [
        ('app_right_nil', EqGoal(F('app', xs, NIL), xs), ()),
        ('app_assoc', EqGoal(F('app', F('app', xs, ys), zs), F('app', xs, F('app', ys, zs))), ('?ys', '?zs')),
    ]
    for name, goal, gen in goals:
        cert = prove_induction(goal, '?xs', bank.rules, gen)
        if cert is None or not bank.add(name, goal, cert):
            raise RuntimeError('Foundational list certificate failed')
    return bank


def synthesize_accumulator(max_size: int = 6) -> tuple[TheoremBank, dict]:
    """Synthesize a RHS after detecting a changing accumulator in revAcc.

    The generalization trigger is restricted to revAcc's structural equation;
    RHS discovery is genuine size-ordered grammar enumeration, not a hard-coded
    return of the desired right-hand side.
    """
    start = perf_counter()
    bank = standard_bank()
    xs, acc = V('xs'), V('acc')
    original = EqGoal(F('revAcc', xs, NIL), F('rev', xs))
    direct = prove_induction(original, '?xs', bank.rules)
    # Detect the non-structural second argument changing in the recursive call.
    rec_eq = next(r for r in DEFINITIONS if r.name == 'revAcc.cons')
    changed = rec_eq.lhs.args[1] != rec_eq.rhs.args[1]
    if not changed:
        raise RuntimeError('No accumulator generalization opportunity')
    target = F('revAcc', xs, acc)
    lists = [tuple(bits) for n in range(3) for bits in product((0, 1), repeat=n)]
    samples = [{'?xs': a, '?acc': b} for a in lists for b in lists]
    count = survivors = 0
    for rhs in enumerate_rhs(max_size):
        count += 1
        if any(eval_list(rhs, e) != eval_list(target, e) for e in samples):
            continue
        survivors += 1
        goal = EqGoal(target, rhs)
        cert = prove_induction(goal, '?xs', bank.rules, ('?acc',))
        if cert is not None and bank.add('revAcc_spec', goal, cert):
            # Specialize the accepted general lemma; do not assume the original.
            l, lt = normalize(original.lhs, DEFINITIONS + bank.rules)
            r, rt = normalize(original.rhs, DEFINITIONS + bank.rules)
            rules = {x.name: x for x in DEFINITIONS + bank.rules}
            specialized = (l == r and replay(original.lhs, lt, rules) == replay(original.rhs, rt, rules))
            return bank, {'status': 'certified', 'direct_induction_succeeded': direct is not None,
                          'candidate_count': count, 'sample_count': len(samples),
                          'sample_survivors': survivors, 'lemma': str(target) + ' = ' + str(rhs),
                          'specialization_checked': specialized, 'seconds': perf_counter() - start,
                          'specialization': {'goal': original.json(),
                                             'left': [s.json() for s in lt], 'right': [s.json() for s in rt]}}
    return bank, {'status': 'no_certificate', 'candidate_count': count,
                  'sample_survivors': survivors, 'seconds': perf_counter() - start}
