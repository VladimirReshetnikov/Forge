"""Educational proof-logging CDCL(T) for Boolean CNF + integer difference logic.

Search: scanning propagation, static branching, first-UIP learning and backjumping.
No restarts, watched literals, clause deletion, or theory propagation are implemented.
Certificates: RUP additions + signed negative-cycle lemmas. The replay checker below
uses separate unit propagation and checks theory certificates algebraically.
Python 3.10+, standard library only. This is NOT a Lean kernel checker.
"""
from __future__ import annotations
from dataclasses import dataclass, asdict
from typing import Optional, Sequence

Clause = tuple[int, ...]

@dataclass(frozen=True)
class DiffAtom:
    """The Boolean atom x - y <= c over mathematical integers."""
    x: int
    y: int
    c: int

    def __post_init__(self):
        if any(type(v) is not int for v in (self.x, self.y, self.c)):
            raise ValueError("integer variable ids and bound required")
        if self.x < 0 or self.y < 0:
            raise ValueError("negative variable id")


def normalize_clause(c: Sequence[int], n: int) -> Optional[Clause]:
    if any(type(x) is not int or x == 0 or abs(x) > n for x in c):
        raise ValueError("literal outside 1..n")
    s = set(c)
    if any(-x in s for x in s):
        return None  # A tautology can be discarded.
    return tuple(sorted(s, key=lambda x: (abs(x), x < 0)))


def edge(atom: DiffAtom, signed_literal: int) -> tuple[int, int, int]:
    # x-y<=c is an edge y -> x with weight c. Over Z its negation is
    # y-x<=-c-1. Do NOT reuse this complement rule over Q or R.
    return ((atom.y, atom.x, atom.c) if signed_literal > 0 else
            (atom.x, atom.y, -atom.c - 1))


def negative_cycle(atoms: dict[int, DiffAtom], assignment: list[int]):
    """Bellman-Ford from an implicit super-source; return signed atom IDs."""
    if not atoms:
        return None
    n = 1 + max(max(a.x, a.y) for a in atoms.values())
    es = [(edge(a, k if assignment[k] > 0 else -k),
           k if assignment[k] > 0 else -k)
          for k, a in sorted(atoms.items()) if assignment[k]]
    d = [0] * n
    pred = [None] * n
    changed = None
    for _ in range(n):
        changed = None
        for (u, v, w), lit in es:
            if d[v] > d[u] + w:
                d[v] = d[u] + w
                pred[v] = (u, lit)
                changed = v
        if changed is None:
            return None
    v = changed
    for _ in range(n):
        assert pred[v] is not None
        v = pred[v][0]
    start = v
    cycle = []
    while True:
        assert pred[v] is not None
        u, lit = pred[v]
        cycle.append(lit)
        v = u
        if v == start:
            break
        if len(cycle) > n:
            raise RuntimeError("invalid Bellman-Ford predecessor cycle")
    return cycle


@dataclass
class Stats:
    decisions: int = 0
    conflicts: int = 0
    learned: int = 0
    theory_lemmas: int = 0
    backjumps: int = 0
    nonchronological_backjumps: int = 0
    propagations: int = 0


class Solver:
    def __init__(self, n: int, clauses: Sequence[Sequence[int]],
                 atoms: Optional[dict[int, DiffAtom]] = None,
                 conflict_limit: int = 1_000_000):
        if type(n) is not int or n < 0:
            raise ValueError("n must be a nonnegative integer")
        self.n = n
        self.clauses = []
        for c in clauses:
            q = normalize_clause(c, n)
            if q is not None:
                self.clauses.append(q)
        self.original = list(self.clauses)
        self.atoms = atoms or {}
        for k, a in self.atoms.items():
            if not 1 <= k <= n or a.x < 0 or a.y < 0:
                raise ValueError("invalid difference atom")
        self.a = [0] * (n + 1)
        self.level = [0] * (n + 1)
        self.reason = [None] * (n + 1)
        self.trail = []
        self.dl = 0
        self.proof = []
        self.stats = Stats()
        self.conflict_limit = conflict_limit
        self.order = list(range(1, n + 1))

    def enqueue(self, lit: int, reason: Optional[int]) -> None:
        v = abs(lit)
        val = 1 if lit > 0 else -1
        if self.a[v]:
            if self.a[v] != val:
                raise RuntimeError("contradictory enqueue")
            return
        self.a[v] = val
        self.level[v] = self.dl
        self.reason[v] = reason
        self.trail.append(lit)
        if reason is not None:
            self.stats.propagations += 1

    def propagate(self) -> Optional[int]:
        while True:
            changed = False
            for i, c in enumerate(self.clauses):
                if any(self.a[abs(l)] == (1 if l > 0 else -1) for l in c):
                    continue
                unassigned = [l for l in c if not self.a[abs(l)]]
                if not unassigned:
                    return i
                if len(unassigned) == 1:
                    self.enqueue(unassigned[0], i)
                    changed = True
            if not changed:
                break
        cycle = negative_cycle(self.atoms, self.a)
        if cycle is not None:
            c = normalize_clause([-l for l in cycle], self.n)
            assert c is not None
            self.proof.append({"kind": "theory", "clause": list(c), "cycle": cycle})
            self.clauses.append(c)
            self.stats.theory_lemmas += 1
            return len(self.clauses) - 1
        return None

    def analyze(self, conflict: int) -> tuple[Clause, int, int]:
        """Resolve latest current-level implications until a single UIP remains."""
        c = set(self.clauses[conflict])
        while sum(self.level[abs(l)] == self.dl for l in c) > 1:
            involved = {abs(l) for l in c if self.level[abs(l)] == self.dl}
            lit = next(l for l in reversed(self.trail) if abs(l) in involved)
            v = abs(lit)
            r = self.reason[v]
            if r is None:
                raise RuntimeError("decision encountered before first UIP")
            # c contains -lit (it is false); reason contains lit.
            c.remove(-lit)
            c.update(l for l in self.clauses[r] if l != lit)
            if any(-l in c for l in c):
                raise RuntimeError("tautological conflict resolvent")
        current = [l for l in c if self.level[abs(l)] == self.dl]
        if not current:
            # All contributing assignments can be at older levels only if an
            # asynchronous theory solver is used. This implementation is eager.
            raise RuntimeError("conflict lacks current-level assignment")
        uip = current[0]
        back = max((self.level[abs(l)] for l in c if l != uip), default=0)
        return tuple(sorted(c, key=lambda x: (abs(x), x < 0))), back, uip

    def backtrack(self, level: int) -> None:
        while self.trail and self.level[abs(self.trail[-1])] > level:
            v = abs(self.trail.pop())
            self.a[v] = 0
            self.level[v] = 0
            self.reason[v] = None
        self.dl = level

    def solve(self) -> Optional[bool]:
        """True=SAT, False=UNSAT, None=resource limit. Never conflates them."""
        while True:
            ci = self.propagate()
            if ci is not None:
                self.stats.conflicts += 1
                if self.dl == 0:
                    self.proof.append({"kind": "rup", "clause": []})
                    return False
                if self.stats.conflicts >= self.conflict_limit:
                    return None
                c, back, uip = self.analyze(ci)
                self.proof.append({"kind": "rup", "clause": list(c)})
                self.stats.learned += 1
                self.stats.backjumps += 1
                if back < self.dl - 1:
                    self.stats.nonchronological_backjumps += 1
                self.backtrack(back)
                self.clauses.append(c)
                self.enqueue(uip, len(self.clauses) - 1)
            else:
                v = next((v for v in self.order if not self.a[v]), None)
                if v is None:
                    return True
                self.dl += 1
                self.stats.decisions += 1
                self.enqueue(v, None)


def rup_check(db: Sequence[Clause], clause: Clause) -> bool:
    """Independent RUP checker: negate the candidate, then unit propagate."""
    env = {}
    for lit in clause:
        v, val = abs(lit), lit < 0
        if v in env and env[v] != val:
            return True
        env[v] = val
    while True:
        units = []
        for c in db:
            remaining = []
            satisfied = False
            for lit in c:
                v = abs(lit)
                if v not in env:
                    remaining.append(lit)
                elif env[v] == (lit > 0):
                    satisfied = True
                    break
            if satisfied:
                continue
            if not remaining:
                return True
            if len(remaining) == 1:
                units.append(remaining[0])
        if not units:
            return False
        progress = False
        for lit in units:
            v, val = abs(lit), lit > 0
            if v in env:
                if env[v] != val:
                    return True
            else:
                env[v] = val
                progress = True
        if not progress:
            return False


def check_cycle(atoms: dict[int, DiffAtom], clause: Clause,
                cycle: Sequence[int]) -> bool:
    """Check by telescoping coefficients, not by rerunning Bellman-Ford."""
    if not cycle or set(clause) != {-l for l in cycle}:
        return False
    balance = {}
    bound = 0
    for lit in cycle:
        if abs(lit) not in atoms:
            return False
        a = atoms[abs(lit)]
        # Deliberately duplicate the semantic rule instead of calling edge().
        x, y, c = ((a.x, a.y, a.c) if lit > 0 else
                   (a.y, a.x, -a.c - 1))
        balance[x] = balance.get(x, 0) + 1
        balance[y] = balance.get(y, 0) - 1
        bound += c
    return bound < 0 and all(c == 0 for c in balance.values())


def replay(n: int, original, atoms, proof) -> bool:
    db = []
    for c in original:
        q = normalize_clause(c, n)
        if q is not None:
            db.append(q)
    for i, event in enumerate(proof):
        try:
            c = normalize_clause(event["clause"], n)
            if c is None:
                return False
            kind = event["kind"]
            if kind == "theory":
                valid = check_cycle(atoms, c, event["cycle"])
            elif kind == "rup":
                valid = rup_check(db, c)
            else:
                return False
            if not valid:
                return False
            db.append(c)
            if not c:
                return i == len(proof) - 1
        except (KeyError, TypeError, ValueError):
            return False
    return False


def floyd_consistent(atoms: dict[int, DiffAtom], bits: Sequence[bool]) -> bool:
    """Independent theory oracle used by exhaustive differential tests."""
    if not atoms:
        return True
    n = 1 + max(max(a.x, a.y) for a in atoms.values())
    # None represents no path; a finite sentinel would be wrong for large ints.
    d = [[0 if i == j else None for j in range(n)] for i in range(n)]
    for k, a in atoms.items():
        if bits[k - 1]:
            u, v, w = a.y, a.x, a.c
        else:
            u, v, w = a.x, a.y, -a.c - 1
        d[u][v] = w if d[u][v] is None else min(d[u][v], w)
    for k in range(n):
        for i in range(n):
            for j in range(n):
                if d[i][k] is not None and d[k][j] is not None:
                    candidate = d[i][k] + d[k][j]
                    d[i][j] = candidate if d[i][j] is None else min(d[i][j], candidate)
    return all(d[i][i] >= 0 for i in range(n))


def dpll(n: int, clauses, node_limit=1_000_000):
    """Chronological, unit-propagating baseline; same static variable order."""
    stats = {"decisions": 0, "conflicts": 0, "nodes": 0}
    cs = [q for c in clauses if (q := normalize_clause(c, n)) is not None]
    def go(env):
        stats["nodes"] += 1
        if stats["nodes"] > node_limit:
            raise TimeoutError("DPLL node limit")
        while True:
            changed = False
            for c in cs:
                if any(env.get(abs(l)) == (l > 0) for l in c):
                    continue
                us = [l for l in c if abs(l) not in env]
                if not us:
                    stats["conflicts"] += 1
                    return False
                if len(us) == 1:
                    env[abs(us[0])] = us[0] > 0
                    changed = True
            if not changed:
                break
        v = next((v for v in range(1, n + 1) if v not in env), None)
        if v is None:
            return True
        stats["decisions"] += 1
        return go({**env, v: True}) or go({**env, v: False})
    try:
        result = go({})
    except TimeoutError:
        result = None
    return result, stats
