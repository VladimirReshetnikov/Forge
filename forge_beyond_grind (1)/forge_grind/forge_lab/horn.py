"""Demand-directed, ground, monomorphic Horn search and its DAG checker.

This is NOT an implementation, emulation, or benchmark of Lean's grind.
Body variables absent from the rule head are deliberately unsupported by the
backward engine. In that case the engine abstains rather than inventing values.
"""
from __future__ import annotations
from dataclasses import dataclass
from .terms import T, V, F, match, subst, vars_of, well_typed

@dataclass(frozen=True)
class Atom:
    pred: str
    arg: T

    def json(self) -> dict:
        return {'predicate': self.pred, 'argument': self.arg.json()}

@dataclass(frozen=True)
class HornRule:
    name: str
    body: tuple[Atom, ...]
    head: Atom

@dataclass(frozen=True)
class Node:
    fact: Atom
    rule: str  # '@fact' for a premise
    parents: tuple[int, ...] = ()

    def json(self) -> dict:
        return {'fact': self.fact.json(), 'rule': self.rule, 'parents': list(self.parents)}


def ground(a: Atom) -> bool:
    return well_typed(a.arg) and not vars_of(a.arg)


def check_horn(goal: Atom, facts: tuple[Atom, ...], rules: tuple[HornRule, ...],
               trace: tuple[Node, ...]) -> bool:
    names = {r.name: r for r in rules}
    if (not trace or len(names) != len(rules) or '@fact' in names
            or not ground(goal) or any(not ground(a) for a in facts)):
        return False
    for i, node in enumerate(trace):
        if not ground(node.fact):
            return False
        if node.rule == '@fact':
            if node.parents or node.fact not in facts:
                return False
            continue
        if node.rule not in names:
            return False
        r = names[node.rule]
        if (r.head.pred != node.fact.pred or len(r.body) != len(node.parents)
                or any(type(j) is not int or not 0 <= j < i for j in node.parents)):
            return False
        env = match(r.head.arg, node.fact.arg)
        if env is None:
            return False
        for a, j in zip(r.body, node.parents):
            if a.pred != trace[j].fact.pred:
                return False
            env = match(a.arg, trace[j].fact.arg, env)
            if env is None:
                return False
    return trace[-1].fact == goal


def backward(goal: Atom, facts: tuple[Atom, ...], rules: tuple[HornRule, ...],
             max_depth: int = 100) -> tuple[tuple[Node, ...] | None, dict]:
    nodes: list[Node] = []
    memo: dict[Atom, int] = {}
    active: set[Atom] = set()
    stats = {'requests': 0, 'rule_attempts': 0}
    index: dict[str, list[HornRule]] = {}
    for r in rules:
        index.setdefault(r.head.pred, []).append(r)
    def go(a: Atom, depth: int) -> int | None:
        stats['requests'] += 1
        if a in memo:
            return memo[a]
        if a in active or depth > max_depth or not ground(a):
            return None
        if a in facts:
            memo[a] = len(nodes)
            nodes.append(Node(a, '@fact'))
            return memo[a]
        active.add(a)
        for r in index.get(a.pred, []):
            stats['rule_attempts'] += 1
            env = match(r.head.arg, a.arg)
            if env is None:
                continue
            body = tuple(Atom(b.pred, subst(b.arg, env)) for b in r.body)
            if any(not ground(b) for b in body):
                continue
            parents: list[int] = []
            for b in body:
                j = go(b, depth + 1)
                if j is None:
                    break
                parents.append(j)
            else:
                active.remove(a)
                memo[a] = len(nodes)
                nodes.append(Node(a, r.name, tuple(parents)))
                return memo[a]
        active.remove(a)
        return None
    root = go(goal, 0)
    if root is None:
        return None, {**stats, 'proof_nodes': len(nodes), 'status': 'no_certificate'}
    # Keep only ancestors of the accepted root, then topologically renumber.
    used: set[int] = set()
    def visit(i: int):
        if i not in used:
            used.add(i)
            for j in nodes[i].parents:
                visit(j)
    visit(root)
    order = sorted(used)
    ren = {old: new for new, old in enumerate(order)}
    out = tuple(Node(nodes[i].fact, nodes[i].rule, tuple(ren[j] for j in nodes[i].parents)) for i in order)
    return out, {**stats, 'proof_nodes': len(out), 'status': 'certified'}


def forward(goal: Atom, facts: tuple[Atom, ...], rules: tuple[HornRule, ...],
            rounds: int = 20, node_cap: int = 100000) -> tuple[tuple[Node, ...] | None, dict]:
    """Semi-naive forward baseline for unary-body rules, stopping on discovery."""
    if any(len(r.body) != 1 for r in rules):
        raise ValueError('Forward baseline supports unary bodies only')
    nodes = [Node(a, '@fact') for a in facts]
    memo = {a: i for i, a in enumerate(facts)}
    frontier = list(range(len(nodes)))
    attempts = 0
    def result(root: int):
        used = []
        while True:
            used.append(root)
            if not nodes[root].parents:
                break
            root = nodes[root].parents[0]
        used.reverse()
        return tuple(Node(nodes[i].fact, nodes[i].rule, (k - 1,) if k else ()) for k, i in enumerate(used))
    for round_no in range(rounds + 1):
        if goal in memo:
            return result(memo[goal]), {'generated': len(nodes), 'rule_attempts': attempts, 'status': 'certified'}
        newfront = []
        for i in frontier:
            a = nodes[i].fact
            for r in rules:
                if a.pred != r.body[0].pred:
                    continue
                attempts += 1
                env = match(r.body[0].arg, a.arg)
                if env is None:
                    continue
                b = Atom(r.head.pred, subst(r.head.arg, env))
                if not ground(b) or b in memo:
                    continue
                if len(nodes) >= node_cap:
                    return None, {'generated': len(nodes), 'rule_attempts': attempts, 'status': 'node_cap'}
                memo[b] = len(nodes)
                nodes.append(Node(b, r.name, (i,)))
                newfront.append(memo[b])
                if b == goal:
                    return result(memo[b]), {'generated': len(nodes), 'rule_attempts': attempts, 'status': 'certified'}
        frontier = newfront
        if not frontier:
            break
    return None, {'generated': len(nodes), 'rule_attempts': attempts, 'status': 'round_limit_or_saturated'}


def branching_problem(depth: int):
    x = V('x', 'U')
    facts = (Atom('P', F('a')),)
    rules = (HornRule('step.f', (Atom('P', x),), Atom('P', F('f', x))),
             HornRule('step.g', (Atom('P', x),), Atom('P', F('g', x))))
    target = F('a')
    for _ in range(depth):
        target = F('f', target)
    return Atom('P', target), facts, rules
