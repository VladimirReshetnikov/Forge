"""Demand slicing of finite ground positive Horn programs, with proof replay.

This is NOT E-matching, a dependent-type theorem prover, or a model of grind's
implementation. It isolates a scheduler experiment with an exact finite domain.
"""
from collections import defaultdict, deque
from dataclasses import dataclass
from time import perf_counter

@dataclass(frozen=True)
class Rule:
    head: str
    body: tuple[str, ...]

@dataclass(frozen=True)
class Proof:
    # Topological steps: (derived atom, original rule index). Facts are external.
    steps: tuple[tuple[str, int], ...]

@dataclass(frozen=True)
class Result:
    proved: bool
    proof: Proof | None
    firings: int
    selected_rules: int
    seconds: float

class Program:
    def __init__(self, rules: tuple[Rule, ...]):
        self.rules = rules
        self.by_head = defaultdict(list)
        for i,r in enumerate(rules):
            if len(set(r.body)) != len(r.body):
                raise ValueError('rule bodies must be deduplicated')
            self.by_head[r.head].append(i)

    def slice(self, goal: str) -> set[int]:
        selected, seen, todo = set(), set(), [goal]
        while todo:
            a = todo.pop()
            if a in seen: continue
            seen.add(a)
            for i in self.by_head.get(a, ()):
                selected.add(i)
                todo.extend(self.rules[i].body)
        return selected

    def solve(self, facts: tuple[str, ...], goal: str, *, demand: bool=False,
              stop_at_goal: bool=True) -> Result:
        start = perf_counter()
        selected = sorted(self.slice(goal)) if demand else range(len(self.rules))
        waiting = defaultdict(list)
        missing = {}
        for i in selected:
            missing[i] = len(self.rules[i].body)
            for a in self.rules[i].body: waiting[a].append(i)
        known = set(facts)
        queue = deque(dict.fromkeys(facts))
        steps, firings = [], 0
        def fire(i):
            nonlocal firings
            firings += 1
            h = self.rules[i].head
            if h not in known:
                known.add(h); queue.append(h); steps.append((h,i))
        for i in selected:
            if missing[i] == 0: fire(i)
        while queue and not (stop_at_goal and goal in known):
            a = queue.popleft()
            for i in waiting[a]:
                missing[i] -= 1
                if missing[i] == 0: fire(i)
        proved = goal in known
        proof = Proof(tuple(steps)) if proved else None
        return Result(proved, proof, firings, len(selected), perf_counter()-start)


def replay(rules: tuple[Rule,...], facts: tuple[str,...], goal: str, proof: Proof) -> bool:
    try:
        known = set(facts)
        for atom,i in proof.steps:
            if type(i) is not int or not 0 <= i < len(rules): return False
            r = rules[i]
            if r.head != atom or not all(a in known for a in r.body): return False
            known.add(atom)
        return goal in known
    except (ValueError,TypeError,AttributeError):
        return False


def minimize(rules: tuple[Rule,...], facts: tuple[str,...], goal: str, proof: Proof) -> Proof:
    if not replay(rules,facts,goal,proof):
        raise ValueError('cannot minimize invalid proof')
    used = {goal}
    kept = []
    for a,i in reversed(proof.steps):
        if a in used:
            kept.append((a,i)); used.update(rules[i].body)
    result = Proof(tuple(reversed(kept)))
    if not replay(rules,facts,goal,result): raise AssertionError('minimization failed')
    return result
