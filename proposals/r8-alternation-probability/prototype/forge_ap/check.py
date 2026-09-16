"""Local exact checkers. Deliberately imports no search, flow, or matrix solver.

A successful return establishes only acceptance by this research Python program.
Soundness arguments are in the article; no Lean-kernel acceptance is claimed.
"""
from __future__ import annotations
from fractions import Fraction as Q
from .models import (Arena, Transport, MDP, Simulation, Invalid, need, keys,
                     integer, array, ids, rational)


def parity(p: Arena, c: dict) -> None:
    keys(c, {"regions"})
    regions = array(c["regions"], 2)
    seen = set()
    for player, cert in enumerate(regions):
        keys(cert, {"player", "vertices", "strategy", "ranks"})
        need(integer(cert["player"], 0, 1) == player, "player mismatch")
        w = set(ids(cert["vertices"], p.n)); need(not seen & w, "overlapping regions")
        seen |= w
        strategy = [integer(v, -1, p.n - 1) for v in array(cert["strategy"], p.n)]
        edges = []
        for v in range(p.n):
            if v in w and p.owner[v] == player:
                t = strategy[v]
                need(t in p.edges[v] and t in w, "illegal strategy or region escape")
                edges.append((v, t))
            else:
                need(strategy[v] == -1, "spurious strategy entry")
                if v in w:
                    need(all(t in w for t in p.edges[v]), "opponent can leave region")
                    edges.extend((v, t) for t in p.edges[v])
        bad = sorted({p.priority[v] for v in w if p.priority[v] % 2 != player})
        ranks = array(cert["ranks"], len(bad))
        for priority, record in zip(bad, ranks):
            keys(record, {"priority", "values"})
            need(integer(record["priority"], 0, 10000) == priority, "missing threshold")
            r = [integer(x, 0, p.n) for x in array(record["values"], p.n)]
            for v in range(p.n):
                if v not in w or p.priority[v] > priority:
                    need(r[v] == 0, "noncanonical irrelevant rank")
            for v, t in edges:
                if max(p.priority[v], p.priority[t]) <= priority:
                    need(r[v] >= r[t] + int(p.priority[v] == priority),
                         "parity rank inequality")
    need(seen == set(range(p.n)), "partition is incomplete")


def hall(p: Transport, subset) -> Q:
    a = ids(subset, len(p.mu))
    neighbors = {j for i in a for j in range(len(p.nu)) if p.relation[i][j]}
    return sum((p.mu[i] for i in a), Q(0)) - sum((p.nu[j] for j in neighbors), Q(0))


def transport(p: Transport, c: dict) -> Q:
    keys(c, {"joint", "bad_mass", "hall_subset"})
    g = [tuple(rational(t) for t in array(row, len(p.nu)))
         for row in array(c["joint"], len(p.mu))]
    need(all(t >= 0 for row in g for t in row), "negative joint mass")
    need(all(sum(g[i]) == p.mu[i] for i in range(len(p.mu))), "row marginal")
    need(all(sum(g[i][j] for i in range(len(p.mu))) == p.nu[j]
             for j in range(len(p.nu))), "column marginal")
    bad = sum((g[i][j] for i in range(len(p.mu)) for j in range(len(p.nu))
               if not p.relation[i][j]), Q(0))
    need(rational(c["bad_mass"]) == bad, "wrong bad mass")
    need(hall(p, c["hall_subset"]) == bad, "primal/dual gap")
    return bad


def mdp(p: MDP, c: dict) -> str:
    need(type(c) is dict and "outcome" in c, "missing outcome")
    n = p.n; terminal = set(p.terminal)
    if c["outcome"] == "optimal_bound":
        keys(c, {"outcome", "region", "values", "policy"})
        region = set(ids(c["region"], n, False)); need(p.start in region, "start omitted")
        vals = [rational(t) for t in array(c["values"], n)]
        policy = [integer(t, -1, 1000000) for t in array(c["policy"], n)]
        for s in range(n):
            if s not in region or s in terminal:
                need(vals[s] == 0 and policy[s] == -1, "noncanonical unused entry")
            else:
                need(vals[s] >= 0, "negative potential")
                need(policy[s] < len(p.actions[s]) and policy[s] >= 0, "bad policy")
            if s in region:
                need(all(d[t] == 0 for d in p.actions[s] for t in range(n)
                         if t not in region), "region is not universally closed")
            if s in region and s not in terminal:
                for a, d in enumerate(p.actions[s]):
                    rhs = 1 + sum((d[t] * vals[t] for t in range(n)), Q(0))
                    need(vals[s] >= rhs, "Bellman upper inequality")
                    if a == policy[s]:
                        need(vals[s] == rhs, "policy is not tight")
        return "optimal_bound"
    if c["outcome"] == "nontermination":
        keys(c, {"outcome", "trap", "policy", "path", "probability_lower"})
        trap = set(ids(c["trap"], n, False)); need(not trap & terminal, "terminal in trap")
        pol = [integer(t, -1, 1000000) for t in array(c["policy"], n)]
        for s in range(n):
            if s in trap:
                need(0 <= pol[s] < len(p.actions[s]), "invalid trap action")
                need(all(p.actions[s][pol[s]][t] == 0 for t in range(n) if t not in trap),
                     "trap is not closed under selected action")
            else:
                need(pol[s] == -1, "spurious trap action")
        cur, prob = p.start, Q(1)
        for e in array(c["path"]):
            a, t = array(e, 2)
            a = integer(a, 0, len(p.actions[cur]) - 1); t = integer(t, 0, n - 1)
            mass = p.actions[cur][a][t]; need(mass > 0, "zero-probability path")
            prob *= mass; cur = t
        need(cur in trap, "path misses trap")
        need(rational(c["probability_lower"]) == prob and prob > 0, "path probability")
        return "nontermination"
    raise Invalid("unknown MDP certificate outcome")


def simulation(p: Simulation, c: dict) -> set[tuple[int, int]]:
    keys(c, {"removed", "survivors", "matches"})
    m, n = len(p.left), len(p.right)
    live = {(i, j) for i in range(m) for j in range(n) if p.base[i][j]}
    def relation():
        return tuple(tuple((i, j) in live for j in range(n)) for i in range(m))
    for rec in array(c["removed"]):
        keys(rec, {"pair", "left_action", "obstructions"})
        pair = array(rec["pair"], 2)
        s, t = integer(pair[0], 0, m-1), integer(pair[1], 0, n-1)
        need((s, t) in live, "removed pair absent or duplicated")
        a = integer(rec["left_action"], 0, len(p.left[s])-1)
        obs = array(rec["obstructions"], len(p.right[t]))
        r = relation()
        for b, subset in enumerate(obs):
            problem = Transport(p.left[s][a], p.right[t][b], r)
            need(hall(problem, subset) > 0, "non-strict Hall obstruction")
        live.remove((s, t))
    survivors = []
    for pair in array(c["survivors"]):
        pair = array(pair, 2)
        survivors.append((integer(pair[0], 0, m-1), integer(pair[1], 0, n-1)))
    need(survivors == sorted(live), "survivor relation mismatch")
    expected = [(s, t, a) for s, t in sorted(live) for a in range(len(p.left[s]))]
    matches = array(c["matches"], len(expected)); r = relation()
    for (s, t, a), rec in zip(expected, matches):
        keys(rec, {"pair", "left_action", "right_action", "coupling"})
        pair = array(rec["pair"], 2)
        need(integer(pair[0], 0, m-1) == s and integer(pair[1], 0, n-1) == t,
             "matching pair order")
        need(integer(rec["left_action"], 0, len(p.left[s])-1) == a,
             "left action coverage")
        b = integer(rec["right_action"], 0, len(p.right[t])-1)
        need(transport(Transport(p.left[s][a], p.right[t][b], r), rec["coupling"]) == 0,
             "matching coupling leaves survivor relation")
    return live


def check_record(record: dict) -> None:
    keys(record, {"id", "problem", "certificate"})
    need(type(record["id"]) is str, "record id type")
    obj, c = record["problem"], record["certificate"]
    need(type(obj) is dict and "kind" in obj, "problem kind absent")
    kind = obj["kind"]
    if kind == "parity": parity(Arena.read(obj), c)
    elif kind == "transport": transport(Transport.read(obj), c)
    elif kind == "mdp": mdp(MDP.read(obj), c)
    elif kind == "simulation": simulation(Simulation.read(obj), c)
    else: raise Invalid("unsupported problem kind")
