"""Finite ground-Horn demand slicing with independently replayed derivations.

This isolates scheduling, not Lean E-matching. Every rule is already ground.
Backward reachability computes a relevance slice; indexed forward chaining on
that slice is a complete decision procedure for this finite Horn fragment.
"""
from __future__ import annotations
from dataclasses import dataclass
from collections import defaultdict, deque

@dataclass(frozen=True)
class Rule:
    premises: tuple[str, ...]
    conclusion: str

@dataclass(frozen=True)
class Step:
    rule: int
    conclusion: str


def derive(rules: list[Rule], target: str, demand: bool = False):
    indices = list(range(len(rules)))
    if demand:
        by_head = defaultdict(list)
        for i, r in enumerate(rules): by_head[r.conclusion].append(i)
        seen = {target}; todo = [target]; relevant = set()
        while todo:
            h = todo.pop()
            for i in by_head[h]:
                relevant.add(i)
                for p in rules[i].premises:
                    if p not in seen: seen.add(p); todo.append(p)
        indices = sorted(relevant)
    waiting = defaultdict(list); remaining = {}; queue = deque()
    for i in indices:
        ps = set(rules[i].premises); remaining[i] = len(ps)
        for p in ps: waiting[p].append(i)
        if not ps: queue.append(i)
    facts = set(); proof = []; fired = 0
    while queue:
        i = queue.popleft(); r = rules[i]; fired += 1
        if r.conclusion in facts: continue
        facts.add(r.conclusion); proof.append(Step(i, r.conclusion))
        if r.conclusion == target:
            return proof, {'indexed_rules': len(rules), 'active_rules': len(indices),
                           'firings': fired, 'facts': len(facts)}
        for j in waiting[r.conclusion]:
            remaining[j] -= 1
            if remaining[j] == 0: queue.append(j)
    return None, {'indexed_rules': len(rules), 'active_rules': len(indices),
                  'firings': fired, 'facts': len(facts)}


def check(rules: list[Rule], target: str, proof: list[Step]) -> bool:
    facts = set()
    try:
        for step in proof:
            if type(step.rule) is not int or not 0 <= step.rule < len(rules): return False
            rule = rules[step.rule]
            if step.conclusion != rule.conclusion: return False
            if any(p not in facts for p in rule.premises): return False
            facts.add(rule.conclusion)
        return target in facts
    except (TypeError, IndexError): return False
