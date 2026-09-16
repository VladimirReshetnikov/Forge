"""Untrusted deterministic Schreier--Sims search, with original-generator DAGs.

Uses only the standard library.  Composition is (a*b)(x) = a(b(x)).
The independently written verifier does not import this module.
"""
from __future__ import annotations
from collections import deque, Counter
from dataclasses import dataclass
from math import prod, factorial
from typing import Any, Iterable

Perm = tuple[int, ...]

class SearchLimit(RuntimeError):
    """No certified answer was produced within an operational resource budget."""


def mul(a: Perm, b: Perm) -> Perm:
    return tuple(a[x] for x in b)


def inv(a: Perm) -> Perm:
    result = [0] * len(a)
    for x, y in enumerate(a):
        result[y] = x
    return tuple(result)


def action(g: Perm, colors: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(colors[j] for j in inv(g))


def first_moved(p: Perm) -> int:
    return next((i for i, x in enumerate(p) if i != x), len(p))


def validate_problem(problem: dict[str, Any]) -> tuple[int, list[Perm]]:
    if set(problem) != {"degree", "generators"}:
        raise ValueError("problem must contain degree and generators only")
    n = problem["degree"]
    if type(n) is not int or not 0 <= n <= 256:
        raise ValueError("degree must be an integer in [0, 256]")
    if type(problem["generators"]) is not list:
        raise ValueError("generators must be a list")
    generators = []
    for raw in problem["generators"]:
        if type(raw) is not list or len(raw) != n:
            raise ValueError("wrong permutation degree")
        if any(type(x) is not int for x in raw) or sorted(raw) != list(range(n)):
            raise ValueError("not a permutation")
        generators.append(tuple(raw))
    return n, generators


class WordDAG:
    """Intern evaluated permutations, retaining one exact original-generator word."""
    def __init__(self, n: int, generators: list[Perm], max_nodes: int = 200_000):
        self.n, self.generators, self.max_nodes = n, generators, max_nodes
        self.nodes: list[list[Any]] = [["id"]]
        self.values: list[Perm] = [tuple(range(n))]
        self.index: dict[Perm, int] = {self.values[0]: 0}

    def intern(self, value: Perm, node: list[Any]) -> int:
        if value in self.index:
            return self.index[value]
        if len(self.nodes) >= self.max_nodes:
            raise SearchLimit("word DAG node budget exhausted")
        k = len(self.nodes)
        self.index[value] = k
        self.nodes.append(node)
        self.values.append(value)
        return k

    def generator(self, k: int) -> int:
        return self.intern(self.generators[k], ["gen", k])

    def multiply(self, a: int, b: int) -> int:
        return self.intern(mul(self.values[a], self.values[b]), ["mul", a, b])

    def inverse(self, a: int) -> int:
        return self.intern(inv(self.values[a]), ["inv", a])

    def trim(self, roots: list[int]) -> tuple[list[list[Any]], list[int]]:
        live: set[int] = {0}
        pending = list(roots)
        while pending:
            k = pending.pop()
            if k in live:
                continue
            live.add(k)
            op, *args = self.nodes[k]
            if op in ("mul", "inv"):
                pending.extend(args)
        old = sorted(live)
        renumber = {k: j for j, k in enumerate(old)}
        trimmed = []
        for k in old:
            op, *args = self.nodes[k]
            trimmed.append([op, *(renumber[a] for a in args)]
                           if op in ("mul", "inv") else [op, *args])
        return trimmed, [renumber[k] for k in roots]


@dataclass
class SearchChain:
    n: int
    generators: list[Perm]
    dag: WordDAG
    strong: list[int]
    tables: list[dict[int, int]]
    edges: list[list[list[int | None]]]
    insertions: int
    schreier_checks: int

    @property
    def order(self) -> int:
        return prod(len(t) for t in self.tables)

    def export(self) -> dict[str, Any]:
        nodes, roots = self.dag.trim(self.strong)
        return {"format": "forge.symmetry.chain.v1", "word_dag": nodes,
                "strong": roots, "levels": self.edges, "order": self.order}


def build_chain(problem: dict[str, Any], *, max_steps: int = 5_000_000,
                max_nodes: int = 200_000) -> SearchChain:
    """Complete deterministic construction when resource limits are not reached.

    Add a failed Schreier residual, not every raw Schreier generator.  Each
    insertion grows an orbit at its first moved base point.  The full base is
    0,...,n-1, avoiding any assumption that a partial base is faithful.
    """
    n, generators = validate_problem(problem)
    dag = WordDAG(n, generators, max_nodes)
    strong = list(dict.fromkeys(dag.generator(k) for k in range(len(generators))))
    strong = [k for k in strong if first_moved(dag.values[k]) < n]
    insertion_count = checks = 0

    def tables_for() -> tuple[list[dict[int, int]], list[list[list[int | None]]]]:
        tables, edges = [], []
        for level in range(n):
            allowed: list[tuple[int, int]] = []
            for j, node in enumerate(strong):
                if first_moved(dag.values[node]) >= level:
                    allowed.extend(((j + 1, node), (-(j + 1), dag.inverse(node))))
            table = {level: 0}
            tree: list[list[int | None]] = [[level, None, None]]
            point_index = {level: 0}
            queue = deque([level])
            while queue:
                x = queue.popleft()
                for label, s in allowed:
                    y = dag.values[s][x]
                    if y not in table:
                        table[y] = dag.multiply(s, table[x])
                        point_index[y] = len(tree)
                        tree.append([y, point_index[x], label])
                        queue.append(y)
            tables.append(table)
            edges.append(tree)
        return tables, edges

    def sift_node(node: int, start: int, tables: list[dict[int, int]]) -> int:
        for level in range(start, n):
            x = dag.values[node][level]
            if x not in tables[level]:
                return node
            node = dag.multiply(dag.inverse(tables[level][x]), node)
        return node

    while True:
        tables, edges = tables_for()
        added = None
        for level in range(n - 1, -1, -1):
            allowed = []
            for s in strong:
                if first_moved(dag.values[s]) >= level:
                    allowed.extend((s, dag.inverse(s)))
            for s in dict.fromkeys(allowed):
                for x, t in tables[level].items():
                    checks += 1
                    if checks > max_steps:
                        raise SearchLimit("Schreier search budget exhausted")
                    y = dag.values[s][x]
                    r = dag.multiply(dag.inverse(tables[level][y]), dag.multiply(s, t))
                    r = sift_node(r, level + 1, tables)
                    if dag.values[r] != tuple(range(n)):
                        if r in strong:
                            raise AssertionError("a strong generator failed to sift")
                        added = r
                        break
                if added is not None:
                    break
            if added is not None:
                break
        if added is None:
            return SearchChain(n, generators, dag, strong, tables, edges,
                               insertion_count, checks)
        strong.append(added)
        insertion_count += 1
        if insertion_count > n * (n - 1) // 2:
            raise AssertionError("monotone orbit-growth bound violated")


def enumerate_bfs(problem: dict[str, Any], *, max_order: int = 100_000) -> list[Perm]:
    """Untrusted group enumeration, deliberately not normal-form enumeration."""
    n, generators = validate_problem(problem)
    identity = tuple(range(n))
    found = {identity}
    queue = deque([identity])
    while queue:
        p = queue.popleft()
        for g in generators:
            q = mul(g, p)
            if q not in found:
                if len(found) >= max_order:
                    raise SearchLimit("explicit group enumeration budget exhausted")
                found.add(q)
                queue.append(q)
    return sorted(found)


def cycle_lengths(p: Perm) -> tuple[int, ...]:
    unseen = set(range(len(p)))
    result = []
    while unseen:
        start = min(unseen)
        point, length = start, 0
        while point in unseen:
            unseen.remove(point)
            point = p[point]
            length += 1
        result.append(length)
    return tuple(sorted(result))


def burnside_certificate(problem: dict[str, Any], *, max_order: int = 100_000) -> dict[str, Any]:
    elements = enumerate_bfs(problem, max_order=max_order)
    census = Counter(cycle_lengths(p) for p in elements)
    return {"format": "forge.symmetry.burnside.v1", "order": len(elements),
            "inventory": [[list(lengths), count] for lengths, count in sorted(census.items())]}


def _lower_orbit_colors(chain: SearchChain, colors: tuple[int, ...]) -> list[tuple[int, ...]]:
    """Producer uses union-find.  Verifier instead computes graph components."""
    all_rows = []
    for level in range(chain.n + 1):
        parents = list(range(chain.n))
        def root(x: int) -> int:
            while x != parents[x]:
                parents[x] = parents[parents[x]]
                x = parents[x]
            return x
        for node in chain.strong:
            p = chain.dag.values[node]
            if first_moved(p) >= level:
                for x, y in enumerate(p):
                    parents[root(x)] = root(y)
        minima: dict[int, int] = {}
        for x, c in enumerate(colors):
            r = root(x)
            minima[r] = min(minima.get(r, c), c)
        all_rows.append(tuple(minima[root(x)] for x in range(chain.n)))
    return all_rows


def canonical_certificate(chain: SearchChain, colors: list[int], *, max_nodes: int = 200_000) -> tuple[dict[str, Any], dict[str, int]]:
    """Find an exact lexicographic minimum and a complete coset-cover proof.

    The independent checker reconstructs every coset prefix.  A cut is allowed
    only if a point-orbit lower bound is at least the claimed minimum.
    """
    if len(colors) != chain.n or any(type(x) is not int or x < 0 for x in colors):
        raise ValueError("colors must be nonnegative integers at the original degree")
    source = tuple(colors)
    lower = _lower_orbit_colors(chain, source)
    identity = tuple(range(chain.n))
    best, transporter = source, identity
    search_nodes = proof_nodes = 0
    def bound(level: int, p: Perm) -> tuple[int, ...]:
        return action(p, lower[level])

    def search(level: int, p: Perm) -> None:
        nonlocal best, transporter, search_nodes
        search_nodes += 1
        if search_nodes > max_nodes:
            raise SearchLimit("canonical-image search budget exhausted")
        low = bound(level, p)
        if low >= best:
            return
        if level == chain.n:
            best, transporter = low, p
            return
        children = [mul(p, chain.dag.values[t]) for t in chain.tables[level].values()]
        children.sort(key=lambda q: bound(level + 1, q))
        for q in children:
            search(level + 1, q)
    search(0, identity)

    def cover(level: int, p: Perm) -> list[Any]:
        nonlocal proof_nodes
        proof_nodes += 1
        if proof_nodes > max_nodes:
            raise SearchLimit("canonical-image proof budget exhausted")
        if bound(level, p) >= best:
            return ["cut"]
        if level == chain.n:
            raise AssertionError("search returned a non-minimal image")
        return ["split", [cover(level + 1, mul(p, chain.dag.values[t]))
                          for t in chain.tables[level].values()]]
    tree = cover(0, identity)
    return ({"format": "forge.symmetry.canonical.v1", "best": list(best),
             "transporter": list(transporter), "cover": tree},
            {"search_nodes": search_nodes, "proof_nodes": proof_nodes})


def named_problem(family: str, n: int) -> dict[str, Any]:
    if n < 0:
        raise ValueError("negative degree")
    identity = tuple(range(n))
    def cycle(points: list[int]) -> Perm:
        p = list(identity)
        if points:
            for x, y in zip(points, points[1:] + points[:1]):
                p[x] = y
        return tuple(p)
    if family == "S":
        gens = [cycle(list(range(n))), cycle([0, 1])] if n >= 2 else []
    elif family == "A":
        gens = [cycle([0, 1, k]) for k in range(2, n)]
    elif family == "C":
        gens = [cycle(list(range(n)))] if n else []
    elif family == "D":
        # Actual image of the polygon action; order is not 2n when n < 3.
        gens = [cycle(list(range(n))), tuple((-i) % n for i in range(n))] if n else []
    elif family == "trivial":
        gens = []
    else:
        raise ValueError("unknown named family")
    return {"degree": n, "generators": [list(g) for g in gens]}


def canonical_family_certificate(chain: SearchChain, colors: list[int], family: str) -> dict[str, Any]:
    """Linear-size transport certificate; intended for recognized S_n / A_n.

    Search-time recognition is not authority: checker repeats the order/parity
    gates and independently derives the expected least image.
    """
    if len(colors) != chain.n or any(type(c) is not int or c < 0 for c in colors):
        raise ValueError("invalid coloring")
    if family not in {"S", "A"}:
        raise ValueError("unsupported canonical family")
    if family == "A" and chain.n < 2:
        raise ValueError("alternating shortcut requires n >= 2")
    target = sorted(colors)
    destinations: dict[int, deque[int]] = {}
    for i, c in enumerate(target):
        destinations.setdefault(c, deque()).append(i)
    transporter = [destinations[c].popleft() for c in colors]
    parity = sum(transporter[i] > transporter[j] for i in range(chain.n) for j in range(i + 1, chain.n)) % 2
    if family == "A" and parity:
        first: dict[int, int] = {}
        duplicate = None
        for i, c in enumerate(colors):
            if c in first:
                duplicate = (first[c], i)
                break
            first[c] = i
        if duplicate is not None:
            i, j = duplicate
            transporter[i], transporter[j] = transporter[j], transporter[i]
        else:
            a, b = chain.n - 2, chain.n - 1
            transporter = [b if x == a else a if x == b else x for x in transporter]
    best = action(tuple(transporter), tuple(colors))
    return {"format": "forge.symmetry.canonical-family.v1", "family": family,
            "best": list(best), "transporter": transporter}
