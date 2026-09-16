"""Untrusted certificate producer for binary-automatic first-order relations.
Pure standard library. Every DFA is explicit and complete. The checker is a
separate executable and imports none of this file or formula.py.
"""
from __future__ import annotations
import argparse
from collections import deque
from copy import deepcopy
from dataclasses import dataclass
import json
from pathlib import Path
from typing import Any, Callable, Hashable

class BudgetExceeded(RuntimeError):
    pass

@dataclass(frozen=True)
class Limits:
    max_states: int = 8192
    max_tracks: int = 8
    max_nodes: int = 4096
    max_cells: int = 2_000_000

class Compiler:
    def __init__(self, limits: Limits = Limits(), minimize: bool = True):
        self.limits = limits
        self.minimize_enabled = minimize
        self.nodes: list[dict[str, Any]] = []
        self.cache: dict[str, int] = {}
        self.cells = 0

    def explore(self, k: int, start: Hashable,
                step: Callable[[Hashable, int], Hashable],
                final: Callable[[Hashable], bool]) -> tuple[dict, list]:
        if k > self.limits.max_tracks:
            raise BudgetExceeded("track limit")
        states = [start]
        indices = {start: 0}
        rows: list[list[int]] = []
        i = 0
        alphabet = 1 << k
        while i < len(states):
            row = []
            for a in range(alphabet):
                t = step(states[i], a)
                if t not in indices:
                    if len(states) >= self.limits.max_states:
                        raise BudgetExceeded("state limit")
                    indices[t] = len(states)
                    states.append(t)
                row.append(indices[t])
            rows.append(row)
            i += 1
            if self.cells + len(rows) * alphabet > self.limits.max_cells:
                raise BudgetExceeded("transition-cell limit")
        return {"k": k, "start": 0, "trans": rows,
                "final": [bool(final(q)) for q in states]}, states

    def add(self, kind: str, ctx: list[str], f: dict, dfa: dict,
            **evidence: Any) -> int:
        if len(self.nodes) >= self.limits.max_nodes:
            raise BudgetExceeded("node limit")
        self.cells += len(dfa["trans"]) * (1 << dfa["k"])
        if self.cells > self.limits.max_cells:
            raise BudgetExceeded("total transition-cell limit")
        i = len(self.nodes)
        self.nodes.append({"kind": kind, "ctx": list(ctx),
                           "formula": deepcopy(f), "dfa": dfa, **evidence})
        return i

    def atom(self, f: dict, ctx: list[str]) -> int:
        op, k = f["op"], len(ctx)
        if len(set(ctx)) != k or any(type(v) is not str for v in ctx):
            raise ValueError("invalid variable context")
        labels: list
        if op in ("eq", "le", "cong"):
            if type(f["rhs"]) is not int or not isinstance(f["coeff"], dict):
                raise ValueError("linear atoms require exact integers")
            if any(v not in ctx or type(c) is not int
                   for v, c in f["coeff"].items()):
                raise ValueError("unknown variable or noninteger coefficient")
            coeff = [f["coeff"].get(v, 0) for v in ctx]
            sums = [sum(c * ((a >> j) & 1) for j, c in enumerate(coeff))
                    for a in range(1 << k)]
            b = f["rhs"]
            if op == "eq":
                def step(q, a):
                    if q is None or (q + sums[a]) % 2:
                        return None
                    return (q + sums[a]) // 2
                dfa, labels = self.explore(k, -b, step, lambda q: q == 0)
            elif op == "le":
                dfa, labels = self.explore(k, -b - 1,
                    lambda q, a: (q + sums[a]) // 2, lambda q: q < 0)
            else:
                m = f["modulus"]
                if type(m) is not int or m <= 0:
                    raise ValueError("modulus must be a positive integer")
                dfa, labels = self.explore(k, ((-b) % m, 1 % m),
                    lambda q, a: ((q[0] + q[1] * sums[a]) % m,
                                  (2 * q[1]) % m), lambda q: q[0] == 0)
        elif op == "const":
            if type(f["value"]) is not bool:
                raise ValueError("constant is not Boolean")
            dfa, labels = self.explore(k, 0, lambda q, a: 0,
                                      lambda q: f["value"])
        elif op in ("parity", "pow2"):
            j = ctx.index(f["var"])
            if op == "parity":
                if type(f["value"]) is not int or f["value"] not in (0, 1):
                    raise ValueError("parity must be 0 or 1")
                dfa, labels = self.explore(k, 0,
                    lambda q, a: q ^ ((a >> j) & 1),
                    lambda q: q == f["value"])
            else:
                dfa, labels = self.explore(k, 0,
                    lambda q, a: min(2, q + ((a >> j) & 1)),
                    lambda q: q == 1)
        elif op in ("bitand", "bitxor"):
            if len(f["vars"]) != 3:
                raise ValueError("bit relation needs three variables")
            i, j, z = [ctx.index(v) for v in f["vars"]]
            def step(q, a):
                x, y, v = ((a >> t) & 1 for t in (i, j, z))
                r = (x & y) if op == "bitand" else (x ^ y)
                return int(bool(q) or r != v)
            dfa, labels = self.explore(k, 0, step, lambda q: q == 0)
        else:
            raise ValueError(f"unsupported atom: {op}")
        return self.add("atom", ctx, f, dfa,
                        labels=[list(q) if isinstance(q, tuple) else q for q in labels])

    def quotient(self, child: int) -> int:
        node = self.nodes[child]
        d = node["dfa"]
        n = len(d["trans"])
        part = [int(v) for v in d["final"]]
        while True:
            signatures: dict[tuple, int] = {}
            new = []
            for q in range(n):
                sig = (d["final"][q], tuple(part[t] for t in d["trans"][q]))
                if sig not in signatures:
                    signatures[sig] = len(signatures)
                new.append(signatures[sig])
            if new == part:
                break
            part = new
        classes = max(part) + 1
        if classes == n:
            return child
        representatives = [part.index(i) for i in range(classes)]
        target = {"k": d["k"], "start": part[d["start"]],
                  "trans": [[part[t] for t in d["trans"][q]] for q in representatives],
                  "final": [d["final"][q] for q in representatives]}
        return self.add("quotient", node["ctx"], node["formula"], target,
                        child=child, mapping=part)

    @staticmethod
    def zero_tail(source: dict) -> tuple[list, list]:
        """Backward BFS before determinization: distances and hidden-bit choices."""
        k = source["k"] - 1
        n = len(source["trans"])
        incoming: list[list[tuple[int, int]]] = [[] for _ in range(n)]
        for q, row in enumerate(source["trans"]):
            for bit in (0, 1):
                incoming[row[bit << k]].append((q, bit))
        rank: list[int | None] = [None] * n
        choices: list[int | None] = [None] * n
        todo = deque()
        for q in range(n):
            if source["final"][q]:
                rank[q] = 0
                todo.append(q)
        while todo:
            t = todo.popleft()
            for q, bit in incoming[t]:
                if rank[q] is None:
                    rank[q] = rank[t] + 1
                    choices[q] = bit
                    todo.append(q)
        return rank, choices

    def project(self, f: dict, ctx: list[str], child: int) -> int:
        d = self.nodes[child]["dfa"]
        k = len(ctx)
        ranks, choices = self.zero_tail(d)
        def step(states, a):
            return tuple(sorted({d["trans"][q][a | (bit << k)]
                                 for q in states for bit in (0, 1)}))
        out, subsets = self.explore(k, (d["start"],), step,
            lambda states: any(ranks[q] is not None for q in states))
        return self.add("exists", ctx, f, out, child=child,
                        subsets=[list(s) for s in subsets],
                        tail_rank=ranks, tail_choice=choices)

    def compile(self, f: dict, ctx: list[str]) -> int:
        if not isinstance(f, dict) or type(f.get("op")) is not str:
            raise ValueError("formula must be an explicit object")
        if len(ctx) > self.limits.max_tracks:
            raise BudgetExceeded("track limit")
        key = json.dumps([ctx, f], sort_keys=True, separators=(",", ":"))
        if key in self.cache:
            return self.cache[key]
        op = f["op"]
        if op == "not":
            child = self.compile(f["arg"], ctx)
            source = self.nodes[child]["dfa"]
            target = {**source, "final": [not v for v in source["final"]]}
            i = self.add("not", ctx, f, target, child=child)
        elif op in ("and", "or", "iff"):
            left, right = self.compile(f["left"], ctx), self.compile(f["right"], ctx)
            a, b = self.nodes[left]["dfa"], self.nodes[right]["dfa"]
            def final(pair):
                x, y = a["final"][pair[0]], b["final"][pair[1]]
                return (x and y) if op == "and" else ((x or y) if op == "or" else x == y)
            target, pairs = self.explore(len(ctx), (a["start"], b["start"]),
                lambda p, s: (a["trans"][p[0]][s], b["trans"][p[1]][s]), final)
            i = self.add("product", ctx, f, target, left=left, right=right,
                         pairs=[list(p) for p in pairs])
        elif op == "exists":
            v = f["var"]
            if type(v) is not str or not v or v in ctx:
                raise ValueError("binder is invalid or shadows an active variable")
            child = self.compile(f["arg"], ctx + [v])
            i = self.project(f, ctx, child)
        else:
            i = self.atom(f, ctx)
        if self.minimize_enabled:
            i = self.quotient(i)
        self.cache[key] = i
        return i

    def bundle(self, formula: dict, context: list[str]) -> dict:
        root = self.compile(formula, context)
        return {"schema": "forge-auto-1", "query": {"context": context, "formula": formula},
                "nodes": self.nodes, "root": root,
                "verdict": verdict(self.nodes[root]["dfa"])}

def verdict(d: dict) -> dict:
    start = d["start"]
    todo = deque([start])
    parent: dict[int, tuple[int, int] | None] = {start: None}
    while todo:
        q = todo.popleft()
        if not d["final"][q]:
            word = []
            cur = q
            while parent[cur] is not None:
                prev, letter = parent[cur]
                word.append(letter)
                cur = prev
            word.reverse()
            return {"kind": "counterexample", "word": word,
                    "values": decode(word, d["k"])}
        for letter, t in enumerate(d["trans"][q]):
            if t not in parent:
                parent[t] = (q, letter)
                todo.append(t)
    return {"kind": "valid", "invariant": sorted(parent)}

def encode(values: list[int], padding: int = 0) -> list[int]:
    if any(type(x) is not int or x < 0 for x in values) or type(padding) is not int or padding < 0:
        raise ValueError("encoding requires naturals")
    n = max((x.bit_length() for x in values), default=0) + padding
    return [sum(((x >> j) & 1) << i for i, x in enumerate(values)) for j in range(n)]

def decode(word: list[int], k: int) -> list[int]:
    return [sum(((a >> i) & 1) << j for j, a in enumerate(word)) for i in range(k)]

def accepts(d: dict, values: list[int], padding: int = 0) -> bool:
    q = d["start"]
    for a in encode(values, padding):
        q = d["trans"][q][a]
    return d["final"][q]

def extract_witness(source: dict, values: list[int]) -> dict | None:
    """Return one last-track witness, including a checked-source trace.
    With a least-graph source the returned witness is necessarily the minimum.
    """
    if len(values) + 1 != source["k"]:
        raise ValueError("incorrect witness context")
    k = len(values)
    visible = encode(values)
    rank, choice = Compiler.zero_tail(source)
    layers: list[dict[int, tuple[int, int]]] = []
    current = {source["start"]}
    for a in visible:
        nxt = {}
        for q in sorted(current):
            for b in (0, 1):
                t = source["trans"][q][a | (b << k)]
                nxt.setdefault(t, (q, b))
        layers.append(nxt)
        current = set(nxt)
    live = [q for q in current if rank[q] is not None]
    if not live:
        return None
    q = min(live, key=lambda t: (rank[t], t))
    tail_start = q
    bits = []
    for layer in reversed(layers):
        q, b = layer[q]
        bits.append(b)
    bits.reverse()
    q = tail_start
    while rank[q] != 0:
        b = choice[q]
        bits.append(b)
        q = source["trans"][q][b << k]
    padded = visible + [0] * (len(bits) - len(visible))
    word = [a | (b << k) for a, b in zip(padded, bits)]
    trace = [source["start"]]
    for a in word:
        trace.append(source["trans"][trace[-1]][a])
    return {"inputs": values, "witness": sum(b << i for i, b in enumerate(bits)),
            "word": word, "trace": trace}

def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("query", type=Path)
    p.add_argument("output", type=Path)
    p.add_argument("--max-states", type=int, default=8192)
    p.add_argument("--no-minimize", action="store_true")
    args = p.parse_args()
    q = json.loads(args.query.read_text())
    c = Compiler(Limits(max_states=args.max_states), not args.no_minimize)
    try:
        result = c.bundle(q["formula"], q["context"])
    except BudgetExceeded as e:
        result = {"schema": "forge-auto-1", "status": "unknown", "reason": str(e)}
    args.output.write_text(json.dumps(result, separators=(",", ":")) + "\n")
    print(result.get("verdict", result.get("status")))

if __name__ == "__main__":
    main()
