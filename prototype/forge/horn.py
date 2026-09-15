"""Demand-directed first-order Horn search with a replayable proof DAG.

PROVENANCE
  BASE  p5-certificate-first/prototype/forge/demand.py -- genuinely first-order
        terms, true body joins in the forward engine, a tabled fixed point (so a
        cycle alone never proves anything), the ProofNode DAG checker, and trim.
  FOLD  p8-obligation-broker/prototype/horn.py -- the `stop_at_goal` knob and
        proof minimisation.
  FOLD  p9-proof-planner/forge_lab/horn.py -- abstention when a rule instance
        leaves a body atom non-ground (the engine never invents values).
  FOLD  p3-planner-certificate-layer/prototype/horn.py -- the index-vs-search
        timing split in the reported statistics, and chain_problem(length, decoys).

Scope: one-sorted first-order terms, exact syntactic matching, explicit term
depth / fact bounds. No E-matching, no unification modulo equality, no Lean.
"""
from __future__ import annotations
from collections import defaultdict, deque
from dataclasses import dataclass
from time import perf_counter


@dataclass(frozen=True, order=True)
class Term:
    symbol: str
    args: tuple['Term', ...] = ()

    def __post_init__(self):
        if not self.symbol or (self.symbol.startswith('?') and self.args):
            raise ValueError('variables must be leaves')

    @property
    def variable(self) -> bool:
        return self.symbol.startswith('?')

    @property
    def depth(self) -> int:
        return 0 if not self.args else 1 + max(t.depth for t in self.args)

    def variables(self) -> set[str]:
        if self.variable:
            return {self.symbol}
        return set().union(*(t.variables() for t in self.args)) if self.args else set()

    def subst(self, s: dict) -> 'Term':
        if self.variable:
            return s.get(self.symbol, self)
        return Term(self.symbol, tuple(t.subst(s) for t in self.args))

    def text(self) -> str:
        return self.symbol if not self.args else \
            f"{self.symbol}({','.join(a.text() for a in self.args)})"


@dataclass(frozen=True, order=True)
class Atom:
    predicate: str
    args: tuple[Term, ...]

    def variables(self) -> set[str]:
        return set().union(*(a.variables() for a in self.args)) if self.args else set()

    @property
    def depth(self) -> int:
        return max((a.depth for a in self.args), default=0)

    def subst(self, s: dict) -> 'Atom':
        return Atom(self.predicate, tuple(a.subst(s) for a in self.args))

    def text(self) -> str:
        return f"{self.predicate}({','.join(a.text() for a in self.args)})"


@dataclass(frozen=True)
class Rule:
    name: str
    head: Atom
    body: tuple[Atom, ...]

    @property
    def head_covered(self) -> bool:
        """True when every body variable occurs in the head.

        p5 raised here. The merged engine ABSTAINS instead (p9): such a rule may
        be stated, but no engine will invent bindings for its free body variables.
        """
        used = set().union(*(p.variables() for p in self.body)) if self.body else set()
        return used <= self.head.variables()


def match_term(pattern: Term, ground: Term, s: dict) -> bool:
    if pattern.variable:
        if pattern.symbol in s:
            return s[pattern.symbol] == ground
        s[pattern.symbol] = ground
        return True
    return (pattern.symbol == ground.symbol and len(pattern.args) == len(ground.args)
            and all(match_term(p, g, s) for p, g in zip(pattern.args, ground.args)))


def match_atom(pattern: Atom, ground: Atom, subst=None) -> dict | None:
    s = dict(subst or {})
    if (pattern.predicate != ground.predicate or len(pattern.args) != len(ground.args)
            or not all(match_term(p, g, s) for p, g in zip(pattern.args, ground.args))):
        return None
    return s


@dataclass(frozen=True)
class ProofNode:
    conclusion: Atom
    rule: int | None
    substitution: tuple[tuple[str, Term], ...] = ()
    premises: tuple[int, ...] = ()


@dataclass(frozen=True)
class HornCertificate:
    nodes: tuple[ProofNode, ...]
    root: int


def check_horn(facts: tuple[Atom, ...], rules: tuple[Rule, ...], goal: Atom,
               c: HornCertificate) -> bool:
    """Validate only ground instances and an acyclic proof DAG; no search calls."""
    try:
        if goal.variables() or any(f.variables() for f in facts):
            return False
        if type(c.root) is not int or not 0 <= c.root < len(c.nodes):
            return False
        factset = set(facts)
        for i, node in enumerate(c.nodes):
            if node.conclusion.variables():
                return False
            if node.rule is None:
                if node.substitution or node.premises or node.conclusion not in factset:
                    return False
                continue
            if type(node.rule) is not int or not 0 <= node.rule < len(rules):
                return False
            rule = rules[node.rule]
            keys = [k for k, _ in node.substitution]
            if len(keys) != len(set(keys)) or set(keys) != rule.head.variables():
                return False
            s = dict(node.substitution)
            if any(v.variables() for v in s.values()):
                return False
            if rule.head.subst(s) != node.conclusion or len(node.premises) != len(rule.body):
                return False
            for prem, j in zip(rule.body, node.premises):
                if type(j) is not int or not 0 <= j < i or prem.subst(s) != c.nodes[j].conclusion:
                    return False
        return c.nodes[c.root].conclusion == goal
    except (ValueError, TypeError, IndexError, AttributeError):
        return False


def trim(nodes: list[ProofNode], root: int) -> HornCertificate:
    used: set[int] = set()
    todo = [root]
    while todo:
        i = todo.pop()
        if i not in used:
            used.add(i)
            todo.extend(nodes[i].premises)
    order = sorted(used)
    mapping = {old: new for new, old in enumerate(order)}
    new = tuple(ProofNode(nodes[i].conclusion, nodes[i].rule, nodes[i].substitution,
                          tuple(mapping[j] for j in nodes[i].premises)) for i in order)
    return HornCertificate(new, mapping[root])


def minimize(cert: HornCertificate) -> HornCertificate:
    """p8's minimisation: keep only ancestors of the root, renumbered."""
    return trim(list(cert.nodes), cert.root)


@dataclass
class HornResult:
    status: str
    certificate: HornCertificate | None
    terms_or_facts: int
    instances: int
    reason: str = ''
    index_seconds: float = 0.0
    search_seconds: float = 0.0


def demand_prove(facts: tuple[Atom, ...], rules: tuple[Rule, ...], goal: Atom,
                 *, max_depth: int = 40, max_demands: int = 100000,
                 stop_at_goal: bool = True) -> HornResult:
    if goal.variables() or any(f.variables() for f in facts):
        raise ValueError('ground input required')
    started = perf_counter()
    demands: set[Atom] = set()
    queue = deque([goal])
    instances: list[tuple] = []
    limited = False
    by_head = defaultdict(list)
    for j, r in enumerate(rules):
        by_head[r.head.predicate].append((j, r))
    index_seconds = perf_counter() - started
    search_started = perf_counter()
    while queue:
        a = queue.popleft()
        if a in demands:
            continue
        if a.depth > max_depth or len(demands) >= max_demands:
            limited = True
            continue
        demands.add(a)
        if a in facts:
            continue  # no need to expand proved base facts
        for j, r in by_head[a.predicate]:
            s = match_atom(r.head, a)
            if s is None:
                continue
            body = tuple(p.subst(s) for p in r.body)
            if any(p.variables() for p in body):
                continue  # p9: abstain rather than invent a binding
            instances.append((a, j, tuple(sorted(s.items())), body))
            queue.extend(body)
    # Tabled fixed point, not DFS cycle-as-failure. A cycle alone never proves.
    nodes: list[ProofNode] = []
    proved: dict[Atom, int] = {}
    waiters = defaultdict(list)
    remaining: list[set] = []
    done = deque()
    for f in facts:
        if f in demands and f not in proved:
            proved[f] = len(nodes)
            nodes.append(ProofNode(f, None))
            done.append(f)
    for idx, (_, _, _, body) in enumerate(instances):
        pending = set(body) - proved.keys()
        remaining.append(pending)
        for p in pending:
            waiters[p].append(idx)
    ready = deque(i for i, p in enumerate(remaining) if not p)
    while ready or done:
        while ready:
            k = ready.popleft()
            a, j, s, body = instances[k]
            if a not in proved and all(p in proved for p in body):
                proved[a] = len(nodes)
                nodes.append(ProofNode(a, j, s, tuple(proved[p] for p in body)))
                done.append(a)
        if stop_at_goal and goal in proved:
            break
        if done:
            f = done.popleft()
            for k in waiters[f]:
                remaining[k].discard(f)
                if not remaining[k]:
                    ready.append(k)
    search_seconds = perf_counter() - search_started
    if goal in proved:
        cert = trim(nodes, proved[goal])
        if not check_horn(facts, rules, goal, cert):
            raise AssertionError('internal proof replay failure')
        return HornResult('proved', cert, len(demands), len(instances), 'checked_python',
                          index_seconds, search_seconds)
    return HornResult('unknown', None, len(demands), len(instances),
                      'demand budget reached' if limited else 'demand closure has no proof',
                      index_seconds, search_seconds)


def forward_prove(facts: tuple[Atom, ...], rules: tuple[Rule, ...], goal: Atom,
                  *, max_depth: int = 40, max_facts: int = 100000,
                  stop_at_goal: bool = True) -> HornResult:
    """Fair agenda-based semi-naive forward chaining, with real body joins."""
    if goal.variables() or any(f.variables() for f in facts):
        raise ValueError('ground input required')
    started = perf_counter()
    nodes: list[ProofNode] = []
    known: dict[Atom, int] = {}
    index = defaultdict(list)
    queue = deque()
    fired: set = set()
    for f in facts:
        if f not in known:
            known[f] = len(nodes)
            nodes.append(ProofNode(f, None))
            index[f.predicate].append(f)
            queue.append(f)
    index_seconds = perf_counter() - started
    search_started = perf_counter()
    if stop_at_goal and goal in known:
        return HornResult('proved', trim(nodes, known[goal]), len(known), 0,
                          'checked_python', index_seconds, perf_counter() - search_started)
    # Ground empty-body clauses are seeded; universally quantified empty-body
    # rules would require term enumeration and are outside this implementation.
    for j, r in enumerate(rules):
        if not r.body and not r.head.variables() and r.head not in known:
            known[r.head] = len(nodes)
            nodes.append(ProofNode(r.head, j))
            index[r.head.predicate].append(r.head)
            queue.append(r.head)
    instances = 0
    limited = False
    while queue:
        newest = queue.popleft()
        for j, r in enumerate(rules):
            if not r.head_covered:
                continue  # p9: abstain on unbound body variables
            for selected, pattern in enumerate(r.body):
                s = match_atom(pattern, newest)
                if s is None:
                    continue
                states = [(s, {selected: newest})]
                for k, p in enumerate(r.body):
                    if k == selected:
                        continue
                    nxt = []
                    for sub, used in states:
                        for f in index[p.predicate]:
                            ns = match_atom(p, f, sub)
                            if ns is not None:
                                nxt.append((ns, {**used, k: f}))
                    states = nxt
                for s, used in states:
                    head = r.head.subst(s)
                    if head.variables():
                        continue
                    key = (j, tuple(sorted(s.items())))
                    if key in fired:
                        continue
                    fired.add(key)
                    instances += 1
                    if head in known:
                        continue
                    if head.depth > max_depth or len(known) >= max_facts:
                        limited = True
                        continue
                    known[head] = len(nodes)
                    nodes.append(ProofNode(head, j, key[1],
                                           tuple(known[used[k]] for k in range(len(r.body)))))
                    index[head.predicate].append(head)
                    queue.append(head)
                    if stop_at_goal and head == goal:
                        cert = trim(nodes, known[head])
                        if not check_horn(facts, rules, goal, cert):
                            raise AssertionError('internal proof replay failure')
                        return HornResult('proved', cert, len(known), instances,
                                          'checked_python', index_seconds,
                                          perf_counter() - search_started)
    search_seconds = perf_counter() - search_started
    if goal in known:
        return HornResult('proved', trim(nodes, known[goal]), len(known), instances,
                          'checked_python', index_seconds, search_seconds)
    return HornResult('unknown', None, len(known), instances,
                      'fact/depth budget reached' if limited else 'saturated without proof',
                      index_seconds, search_seconds)


def chain_problem(length: int, decoys: int):
    """p3's adversarial workload: decoy rules deliberately precede the chain."""
    if length < 1 or decoys < 0:
        raise ValueError('Bad problem size')
    a = Term('a')
    P = lambda name, t=a: Atom(name, (t,))
    rules = [Rule(f'junk{j}', P(f'junk{j}'), (P('p0'),)) for j in range(decoys)]
    rules += [Rule(f'chain{i}', P(f'p{i + 1}'), (P(f'p{i}'),)) for i in range(length)]
    return (P('p0'),), tuple(rules), P(f'p{length}')
