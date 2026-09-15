"""A tiny, typed equational prover for finite lists, with replayable induction.

This is deliberately NOT a Lean emulator. It checks structural induction over a
fixed first-order signature and captures the accumulator-generalization failure
mode without conflating test-set agreement with a proof. Search and replay use
the same syntax/matching substrate, but replay does not invoke proof search.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import product
from typing import Iterable, Mapping

SIG = {"nil": ((), "L"), "cons": (("E", "L"), "L"),
       "app": (("L", "L"), "L"), "rev": (("L",), "L"),
       "revacc": (("L", "L"), "L")}


@dataclass(frozen=True)
class Term:
    op: str
    args: tuple[Term, ...] = ()
    name: str = ""
    sort: str = "L"

    def __post_init__(self):
        if self.op in ("var", "free"):
            if self.args or not self.name or self.sort not in ("L", "E"):
                raise ValueError("invalid variable")
        else:
            if self.op not in SIG:
                raise ValueError("unknown symbol")
            ins, out = SIG[self.op]
            if self.name or tuple(a.sort for a in self.args) != ins or self.sort != out:
                raise ValueError("ill-sorted term")

    def __str__(self):
        if self.op in ("var", "free"):
            return self.name
        if self.op == "nil":
            return "[]"
        return f"{self.op}({', '.join(map(str, self.args))})"

    def to_json(self):
        return {"op": self.op, "args": [a.to_json() for a in self.args], "name": self.name, "sort": self.sort}


def V(name, sort="L"): return Term("var", name=name, sort=sort)
def F(name, sort="L"): return Term("free", name=name, sort=sort)
def N(): return Term("nil")
def C(h, t): return Term("cons", (h, t))
def A(x, y): return Term("app", (x, y))
def R(x): return Term("rev", (x,))
def RA(x, y): return Term("revacc", (x, y))


def variables(t: Term) -> dict[str, str]:
    d = {t.name: t.sort} if t.op == "var" else {}
    for a in t.args:
        for name, sort in variables(a).items():
            if name in d and d[name] != sort:
                raise ValueError("variable used at different sorts")
            d[name] = sort
    return d


def has_free(t: Term) -> bool:
    return t.op == "free" or any(has_free(a) for a in t.args)


def subst(t: Term, sigma: Mapping[str, Term]) -> Term:
    if t.op == "var" and t.name in sigma:
        value = sigma[t.name]
        if t.sort != value.sort:
            raise ValueError("ill-sorted substitution")
        return value
    if not t.args:
        return t
    return Term(t.op, tuple(subst(a, sigma) for a in t.args), t.name, t.sort)


def match(pattern: Term, actual: Term, sigma: dict[str, Term] | None = None):
    """Only 'var' nodes are match variables. 'free' induction tails are RIGID."""
    sigma = {} if sigma is None else dict(sigma)
    if pattern.sort != actual.sort:
        return None
    if pattern.op == "var":
        if pattern.name in sigma and sigma[pattern.name] != actual:
            return None
        sigma[pattern.name] = actual
        return sigma
    if (pattern.op, pattern.name, len(pattern.args)) != (actual.op, actual.name, len(actual.args)):
        return None
    for p, a in zip(pattern.args, actual.args):
        sigma = match(p, a, sigma)
        if sigma is None:
            return None
    return sigma


@dataclass(frozen=True)
class Equation:
    left: Term
    right: Term

    def __post_init__(self):
        if self.left.sort != self.right.sort:
            raise ValueError("heterogeneous equation")
        # Check repeated names across both sides, too.
        sorts = variables(self.left)
        for name, sort in variables(self.right).items():
            if name in sorts and sorts[name] != sort:
                raise ValueError("ill-sorted equation variable")

    def instantiate(self, sigma):
        return Equation(subst(self.left, sigma), subst(self.right, sigma))

    def to_json(self):
        return {"left": self.left.to_json(), "right": self.right.to_json()}

    def __str__(self):
        return f"{self.left} = {self.right}"


@dataclass(frozen=True)
class Rule:
    name: str
    eq: Equation

    def __post_init__(self):
        if not set(variables(self.eq.right)) <= set(variables(self.eq.left)):
            raise ValueError("RHS contains unmatched variables")


def definitions() -> list[Rule]:
    x, y, h, a = V("x"), V("y"), V("h", "E"), V("a")
    return [Rule("def.app.nil", Equation(A(N(), y), y)),
            Rule("def.app.cons", Equation(A(C(h, x), y), C(h, A(x, y)))),
            Rule("def.rev.nil", Equation(R(N()), N())),
            Rule("def.rev.cons", Equation(R(C(h, x)), A(R(x), C(h, N())))),
            Rule("def.revacc.nil", Equation(RA(N(), a), a)),
            Rule("def.revacc.cons", Equation(RA(C(h, x), a), RA(x, C(h, a))))]


def positions(t: Term, prefix=()):
    # Bottom-up left-to-right normalization.
    for i, a in enumerate(t.args):
        yield from positions(a, prefix + (i,))
    yield prefix


def at(t: Term, path: tuple[int, ...]) -> Term:
    for i in path:
        if type(i) is not int or i < 0 or i >= len(t.args):
            raise ValueError("invalid rewrite path")
        t = t.args[i]
    return t


def replace(t: Term, path: tuple[int, ...], value: Term) -> Term:
    if not path:
        if t.sort != value.sort:
            raise ValueError("replacement sort mismatch")
        return value
    i, *rest = path
    if type(i) is not int or i < 0 or i >= len(t.args):
        raise ValueError("invalid rewrite path")
    args = list(t.args)
    args[i] = replace(args[i], tuple(rest), value)
    return Term(t.op, tuple(args), t.name, t.sort)


@dataclass(frozen=True)
class RewriteStep:
    rule: str
    path: tuple[int, ...]

    def to_json(self): return {"rule": self.rule, "path": list(self.path)}


@dataclass(frozen=True)
class EqualityTrace:
    left: tuple[RewriteStep, ...]
    right: tuple[RewriteStep, ...]

    def to_json(self):
        return {"left": [s.to_json() for s in self.left], "right": [s.to_json() for s in self.right]}


def normalize(t: Term, rules: Iterable[Rule], fuel=2000):
    rules, steps = list(rules), []
    for _ in range(fuel):
        chosen = None
        for path in positions(t):
            subterm = at(t, path)
            for rule in rules:
                sigma = match(rule.eq.left, subterm)
                if sigma is not None:
                    value = subst(rule.eq.right, sigma)
                    if value != subterm:
                        chosen = rule.name, path, value
                        break
            if chosen is not None:
                break
        if chosen is None:
            return t, tuple(steps)
        name, path, value = chosen
        t = replace(t, path, value)
        steps.append(RewriteStep(name, path))
    raise RuntimeError("rewrite fuel exhausted")


def prove_equality(eq: Equation, rules: Iterable[Rule], fuel=2000) -> EqualityTrace | None:
    rules = list(rules)
    try:
        l, lt = normalize(eq.left, rules, fuel)
        r, rt = normalize(eq.right, rules, fuel)
        return EqualityTrace(lt, rt) if l == r else None
    except RuntimeError:
        return None


def check_equality(eq: Equation, trace: EqualityTrace, rules: Iterable[Rule], max_steps=20000) -> bool:
    """Replay supplied paths. No normalization, enumeration, or search occurs."""
    rules = list(rules)
    known = {r.name: r for r in rules}
    if len(known) != len(rules) or len(trace.left) + len(trace.right) > max_steps:
        return False

    def replay(t, steps):
        for step in steps:
            if step.rule not in known:
                raise ValueError("unproved or out-of-scope rule")
            rule = known[step.rule]
            source = at(t, step.path)
            sigma = match(rule.eq.left, source)
            if sigma is None:
                raise ValueError("rule does not match")
            t = replace(t, step.path, subst(rule.eq.right, sigma))
        return t

    try:
        return replay(eq.left, trace.left) == replay(eq.right, trace.right)
    except (ValueError, TypeError, IndexError, KeyError):
        return False


@dataclass(frozen=True)
class InductionCertificate:
    equation: Equation
    variable: str
    base: EqualityTrace
    step: EqualityTrace

    def to_json(self):
        return {"equation": self.equation.to_json(), "variable": self.variable,
                "base": self.base.to_json(), "step": self.step.to_json()}


def induction_obligations(eq: Equation, variable: str):
    sorts = variables(eq.left)
    sorts.update(variables(eq.right))
    if sorts.get(variable) != "L" or has_free(eq.left) or has_free(eq.right):
        raise ValueError("induction requires a universally quantified list variable")
    params = {name: F("param:" + name, sort) for name, sort in sorts.items() if name != variable}
    base = eq.instantiate({**params, variable: N()})
    tail, head = F("induction:tail"), F("induction:head", "E")
    step = eq.instantiate({**params, variable: C(head, tail)})
    # Crucial: tail is fixed; all other variables remain quantified in the IH.
    ih = Rule("local.IH", eq.instantiate({variable: tail}))
    return base, step, ih


class Theory:
    """Library entries can be added only after structural-induction checking."""
    def __init__(self):
        self._proved: dict[str, Rule] = {}
        self.certificates: dict[str, InductionCertificate] = {}

    def rules(self):
        return [*definitions(), *self._proved.values()]

    def search(self, equation: Equation, variable: str) -> InductionCertificate | None:
        try:
            base, step, ih = induction_obligations(equation, variable)
            bt = prove_equality(base, self.rules())
            st = prove_equality(step, [*self.rules(), ih])
            if bt is None or st is None:
                return None
            cert = InductionCertificate(equation, variable, bt, st)
            return cert if self.check(cert) else None
        except ValueError:
            return None

    def check(self, cert: InductionCertificate) -> bool:
        try:
            base, step, ih = induction_obligations(cert.equation, cert.variable)
            return check_equality(base, cert.base, self.rules()) and check_equality(step, cert.step, [*self.rules(), ih])
        except (ValueError, TypeError):
            return False

    def install(self, name: str, cert: InductionCertificate) -> bool:
        if (name.startswith(("def.", "local.")) or name in self._proved
                or not self.check(cert)):
            return False
        try:
            rule = Rule(name, cert.equation)
        except ValueError:
            return False
        self._proved[name] = rule
        self.certificates[name] = cert
        return True


def evaluation(t: Term, values: Mapping[str, tuple | int]):
    if t.op in ("var", "free"):
        return values[t.name]
    args = [evaluation(a, values) for a in t.args]
    if t.op == "nil": return ()
    if t.op == "cons": return (args[0],) + args[1]
    if t.op == "app": return args[0] + args[1]
    if t.op == "rev": return args[0][::-1]
    if t.op == "revacc": return args[0][::-1] + args[1]
    raise ValueError("unknown term")


def list_samples(max_length=2):
    return [xs for n in range(max_length + 1) for xs in product((0, 1), repeat=n)]


def enumerate_list_terms(atoms: Iterable[Term], max_size: int):
    """Typed grammar L ::= atom | rev(L) | app(L,L), enumerated by node count."""
    levels = {1: sorted(set(atoms), key=str)}
    for t in levels[1]:
        if t.sort != "L":
            raise ValueError("list atoms required")
        yield t
    for size in range(2, max_size + 1):
        terms = {R(t) for t in levels.get(size - 1, [])}
        for left_size in range(1, size - 1):
            right_size = size - 1 - left_size
            terms.update(A(a, b) for a in levels.get(left_size, []) for b in levels.get(right_size, []))
        levels[size] = sorted(terms, key=str)
        yield from levels[size]


def changed_recursive_arguments(symbol: str) -> set[int]:
    """Detect non-constructor-pattern arguments changed at recursive call sites."""
    if symbol not in SIG:
        raise ValueError("unknown symbol")
    changing = set()
    for rule in definitions():
        if rule.eq.left.op != symbol:
            continue
        for path in positions(rule.eq.right):
            call = at(rule.eq.right, path)
            if call.op != symbol:
                continue
            for i, (old, new) in enumerate(zip(rule.eq.left.args, call.args)):
                if old.op == "var" and new != old:
                    changing.add(i)
    return changing


@dataclass
class DiscoveryResult:
    equation: Equation | None
    certificate: InductionCertificate | None
    enumerated: int
    sample_survivors: int
    changed_arguments: tuple[int, ...]


def discover_accumulator_lemma(theory: Theory, goal: Equation, induction_variable="xs", max_size=5):
    """Generalize changed nil arguments, then synthesize the RHS by a typed grammar.

    Bounded candidate testing only filters. The returned candidate must pass
    exact induction replay before it is reported as a discovered theorem.
    """
    if goal.left.op not in SIG:
        raise ValueError("a function application is required")
    changed = changed_recursive_arguments(goal.left.op)
    args = list(goal.left.args)
    names = variables(goal.left) | variables(goal.right)
    generated = []
    for index in sorted(changed):
        if args[index] == N():
            name = f"acc{index}"
            while name in names:
                name += "_"
            args[index] = V(name)
            names[name] = "L"
            generated.append(name)
    if not generated:
        return DiscoveryResult(None, None, 0, 0, tuple(sorted(changed)))
    left = Term(goal.left.op, tuple(args))
    parameters = sorted(variables(left))
    if any(variables(left)[name] != "L" for name in parameters):
        raise ValueError("this synthesis grammar supports only list parameters")
    samples = [dict(zip(parameters, values)) for values in product(list_samples(), repeat=len(parameters))]
    target_signature = tuple(evaluation(left, s) for s in samples)
    count, survivors = 0, 0
    for right in enumerate_list_terms([N(), *(V(p) for p in parameters)], max_size):
        count += 1
        if tuple(evaluation(right, s) for s in samples) != target_signature:
            continue
        survivors += 1
        equation = Equation(left, right)
        cert = theory.search(equation, induction_variable)
        if cert is not None:
            return DiscoveryResult(equation, cert, count, survivors, tuple(sorted(changed)))
    return DiscoveryResult(None, None, count, survivors, tuple(sorted(changed)))


def demonstration_theory():
    """Seed STATEMENTS are supplied; their proofs are all searched and checked."""
    t = Theory()
    x, y, z = V("xs"), V("ys"), V("zs")
    goals = [
        ("append_assoc", Equation(A(A(x, y), z), A(x, A(y, z)))),
        ("append_right_nil", Equation(A(x, N()), x)),
        ("reverse_append", Equation(R(A(x, y)), A(R(y), R(x)))),
        ("reverse_involution", Equation(R(R(x)), x)),
    ]
    for name, eq in goals:
        cert = t.search(eq, "xs")
        if cert is None or not t.install(name, cert):
            raise RuntimeError(f"could not prove seed statement: {name}")
    return t
