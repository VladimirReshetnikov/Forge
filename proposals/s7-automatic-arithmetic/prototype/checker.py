"""Independent, standard-library-only replay of forge-auto-1 certificates.
No imports from the producer, no graph exploration, no minimization, and no
formula compilation. Exact local identities check every supplied construction.
This is a research checker, not a formally verified Lean checker.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
from typing import Any

class Rejected(ValueError):
    pass

def require(p: bool, message: str) -> None:
    if not p:
        raise Rejected(message)

def integer(x: Any) -> bool:
    return type(x) is int

def same(a: Any, b: Any) -> bool:
    # Python's structural equality equates True with 1; our wire format does not.
    return json.dumps(a, sort_keys=True, separators=(",", ":")) == json.dumps(b, sort_keys=True, separators=(",", ":"))

def keys(obj: dict, expected: set[str], name: str) -> None:
    require(type(obj) is dict and set(obj) == expected, f"invalid {name} keys")

def context(ctx: Any) -> None:
    require(type(ctx) is list and len(ctx) <= 8, "invalid context")
    require(all(type(v) is str and 0 < len(v) <= 256 for v in ctx), "invalid variable name")
    require(len(set(ctx)) == len(ctx), "duplicate variables")

def syntax(f: Any, ctx: list[str], depth: int = 0) -> None:
    require(depth <= 128, "formula depth limit")
    require(type(f) is dict and type(f.get("op")) is str, "invalid formula")
    op = f["op"]
    if op in ("eq", "le", "cong"):
        keys(f, {"op", "coeff", "rhs"} | ({"modulus"} if op == "cong" else set()), "linear atom")
        require(type(f["coeff"]) is dict and integer(f["rhs"]), "noninteger linear atom")
        require(all(v in ctx and integer(c) for v, c in f["coeff"].items()), "bad linear coefficient")
        if op == "cong":
            require(integer(f["modulus"]) and f["modulus"] > 0, "invalid modulus")
    elif op in ("pow2", "parity"):
        keys(f, {"op", "var"} | ({"value"} if op == "parity" else set()), op)
        require(type(f["var"]) is str and f["var"] in ctx, "unknown digit variable")
        if op == "parity":
            require(integer(f["value"]) and f["value"] in (0, 1), "invalid parity")
    elif op in ("bitand", "bitxor"):
        keys(f, {"op", "vars"}, op)
        require(type(f["vars"]) is list and len(f["vars"]) == 3, "bit relation arity")
        require(all(type(v) is str and v in ctx for v in f["vars"]), "unknown bit variable")
    elif op == "const":
        keys(f, {"op", "value"}, op)
        require(type(f["value"]) is bool, "invalid Boolean constant")
    elif op == "not":
        keys(f, {"op", "arg"}, op)
        syntax(f["arg"], ctx, depth + 1)
    elif op in ("and", "or", "iff"):
        keys(f, {"op", "left", "right"}, op)
        syntax(f["left"], ctx, depth + 1)
        syntax(f["right"], ctx, depth + 1)
    elif op == "exists":
        keys(f, {"op", "var", "arg"}, op)
        require(type(f["var"]) is str and f["var"] and f["var"] not in ctx, "invalid binder")
        context(ctx + [f["var"]])
        syntax(f["arg"], ctx + [f["var"]], depth + 1)
    else:
        raise Rejected("unsupported formula operation")

def dfa_shape(d: Any, k: int) -> int:
    keys(d, {"k", "start", "trans", "final"}, "DFA")
    require(integer(d["k"]) and d["k"] == k, "DFA alphabet mismatch")
    require(type(d["trans"]) is list and 0 < len(d["trans"]) <= 20000, "DFA state limit")
    n = len(d["trans"])
    require(integer(d["start"]) and 0 <= d["start"] < n, "bad initial state")
    require(type(d["final"]) is list and len(d["final"]) == n, "bad accepting array")
    require(all(type(x) is bool for x in d["final"]), "non-Boolean acceptance")
    for row in d["trans"]:
        require(type(row) is list and len(row) == (1 << k), "DFA is not complete")
        require(all(integer(t) and 0 <= t < n for t in row), "transition out of range")
    return n

def atom(node: dict) -> None:
    f, ctx, d, lab = node["formula"], node["ctx"], node["dfa"], node.get("labels")
    n, k, op = len(d["trans"]), len(ctx), f["op"]
    require(type(lab) is list and len(lab) == n, "invalid atomic labels")
    if op in ("eq", "le", "cong"):
        coefficients = [f["coeff"].get(v, 0) for v in ctx]
        b = f["rhs"]
        if op == "eq":
            require(all(x is None or integer(x) for x in lab), "bad equality carry")
            initial = -b
        elif op == "le":
            require(all(integer(x) for x in lab), "bad inequality carry")
            initial = -b - 1
        else:
            m = f["modulus"]
            require(all(type(x) is list and len(x) == 2 and
                        all(integer(v) and 0 <= v < m for v in x) for x in lab), "bad residue label")
            initial = [(-b) % m, 1 % m]
    elif op == "const":
        require(all(integer(x) and x == 0 for x in lab), "bad constant label")
        initial = 0
    elif op in ("parity", "pow2", "bitand", "bitxor"):
        allowed = (0, 1, 2) if op == "pow2" else (0, 1)
        require(all(integer(x) and x in allowed for x in lab), "bad digit label")
        initial = 0
    else:
        raise Rejected("not an atom")
    require(same(lab[d["start"]], initial), "atomic initial label")
    for q in range(n):
        value = lab[q]
        if op == "eq":
            accept = value == 0
        elif op == "le":
            accept = value < 0
        elif op == "cong":
            accept = value[0] == 0
        elif op == "const":
            accept = f["value"]
        elif op == "parity":
            accept = value == f["value"]
        elif op == "pow2":
            accept = value == 1
        else:
            accept = value == 0
        require(d["final"][q] == accept, "atomic final condition")
        for symbol, target in enumerate(d["trans"][q]):
            bits = [(symbol // (2 ** j)) % 2 for j in range(k)]
            if op in ("eq", "le", "cong"):
                s = sum(a * bit for a, bit in zip(coefficients, bits))
            if op == "eq":
                expected = None if value is None or (value + s) % 2 != 0 else (value + s) // 2
            elif op == "le":
                expected = (value + s) // 2
            elif op == "cong":
                expected = [(value[0] + value[1] * s) % m, (2 * value[1]) % m]
            elif op == "const":
                expected = 0
            elif op == "parity":
                expected = (value + bits[ctx.index(f["var"])]) % 2
            elif op == "pow2":
                expected = min(2, value + bits[ctx.index(f["var"])])
            else:
                x, y, z = (bits[ctx.index(v)] for v in f["vars"])
                result = x * y if op == "bitand" else (x + y) % 2
                expected = 1 if value == 1 or result != z else 0
            require(same(lab[target], expected), "atomic transition equation")

def verify(bundle: Any, expected_query: dict) -> dict:
    keys(expected_query, {"context", "formula"}, "query")
    context(expected_query["context"])
    syntax(expected_query["formula"], expected_query["context"])
    require(type(bundle) is dict and bundle.get("schema") == "forge-auto-1", "unknown schema")
    require("status" not in bundle, "UNKNOWN is not proof evidence")
    require(same(bundle.get("query"), expected_query), "certificate belongs to another query")
    nodes = bundle.get("nodes")
    require(type(nodes) is list and 0 < len(nodes) <= 4096, "invalid node array")
    total_cells = 0
    def earlier(index: Any, now: int) -> dict:
        require(integer(index) and 0 <= index < now, "cyclic or out-of-range dependency")
        return nodes[index]
    for i, node in enumerate(nodes):
        require(type(node) is dict, "invalid node")
        ctx, f, d, kind = node.get("ctx"), node.get("formula"), node.get("dfa"), node.get("kind")
        context(ctx)
        syntax(f, ctx)
        n = dfa_shape(d, len(ctx))
        total_cells += n * (1 << len(ctx))
        require(total_cells <= 2_000_000, "replay transition-cell limit")
        if kind == "atom":
            atom(node)
            continue
        if kind in ("not", "quotient", "exists"):
            child = earlier(node.get("child"), i)
            a = child["dfa"]
            if kind != "exists":
                require(ctx == child["ctx"], "context changed")
        if kind == "not":
            require(same(f, {"op": "not", "arg": child["formula"]}), "negation formula mismatch")
            require(d["start"] == a["start"] and d["trans"] == a["trans"], "negation changed transitions")
            require(d["final"] == [not v for v in a["final"]], "incorrect complement")
        elif kind == "product":
            left, right = earlier(node.get("left"), i), earlier(node.get("right"), i)
            require(ctx == left["ctx"] == right["ctx"], "product context mismatch")
            require(f["op"] in ("and", "or", "iff") and
                    same(f, {"op": f["op"], "left": left["formula"], "right": right["formula"]}), "product formula mismatch")
            a, b, pairs = left["dfa"], right["dfa"], node.get("pairs")
            require(type(pairs) is list and len(pairs) == n, "bad product labels")
            for pair in pairs:
                require(type(pair) is list and len(pair) == 2 and all(integer(x) for x in pair), "bad pair")
                require(0 <= pair[0] < len(a["trans"]) and 0 <= pair[1] < len(b["trans"]), "pair out of bounds")
            require(pairs[d["start"]] == [a["start"], b["start"]], "product initial pair")
            for q, (x, y) in enumerate(pairs):
                u, v = a["final"][x], b["final"][y]
                accept = (u and v) if f["op"] == "and" else ((u or v) if f["op"] == "or" else u == v)
                require(d["final"][q] == accept, "product acceptance")
                for letter, target in enumerate(d["trans"][q]):
                    require(pairs[target] == [a["trans"][x][letter], b["trans"][y][letter]], "product transition")
        elif kind == "quotient":
            require(same(f, child["formula"]), "quotient changed formula")
            mapping = node.get("mapping")
            require(type(mapping) is list and len(mapping) == len(a["trans"]), "bad quotient mapping")
            require(all(integer(q) and 0 <= q < n for q in mapping), "quotient index")
            require(mapping[a["start"]] == d["start"], "quotient initial equation")
            for q, image in enumerate(mapping):
                require(a["final"][q] == d["final"][image], "quotient acceptance equation")
                for letter, target in enumerate(a["trans"][q]):
                    require(mapping[target] == d["trans"][image][letter], "quotient transition equation")
        elif kind == "exists":
            require(f["op"] == "exists" and
                    same(f, {"op": "exists", "var": f["var"], "arg": child["formula"]}), "existential formula mismatch")
            require(child["ctx"] == ctx + [f["var"]], "projected track mismatch")
            count, k = len(a["trans"]), len(ctx)
            ranks, choices = node.get("tail_rank"), node.get("tail_choice")
            require(type(ranks) is list and type(choices) is list and len(ranks) == len(choices) == count, "bad tail receipt")
            require(all(r is None or (integer(r) and 0 <= r < count) for r in ranks), "invalid tail rank")
            for q, rank in enumerate(ranks):
                successors = [a["trans"][q][0], a["trans"][q][2 ** k]]
                if a["final"][q]:
                    require(rank is not None, "old final omitted from tail closure")
                if rank is None:
                    require(choices[q] is None and all(ranks[t] is None for t in successors), "tail complement not closed")
                elif rank == 0:
                    require(a["final"][q] and choices[q] is None, "rank-zero state is not final")
                else:
                    bit = choices[q]
                    require(integer(bit) and bit in (0, 1), "invalid tail choice")
                    t = successors[bit]
                    require(ranks[t] is not None and ranks[t] < rank, "tail does not descend")
            subsets = node.get("subsets")
            require(type(subsets) is list and len(subsets) == n, "bad subset labels")
            for states in subsets:
                require(type(states) is list and all(integer(q) and 0 <= q < count for q in states), "bad subset member")
                require(states == sorted(set(states)), "noncanonical subset")
            require(subsets[d["start"]] == [a["start"]], "subset initial equation")
            for q, states in enumerate(subsets):
                require(d["final"][q] == any(ranks[t] is not None for t in states), "subset acceptance equation")
                for letter, target in enumerate(d["trans"][q]):
                    image = sorted({a["trans"][t][letter + bit * (2 ** k)] for t in states for bit in (0, 1)})
                    require(subsets[target] == image, "subset transition equation")
        else:
            raise Rejected("unknown certificate rule")
    root = bundle.get("root")
    require(integer(root) and 0 <= root < len(nodes), "bad root")
    node = nodes[root]
    require(same({"context": node["ctx"], "formula": node["formula"]}, expected_query), "root statement mismatch")
    d = node["dfa"]
    result = bundle.get("verdict")
    require(type(result) is dict, "missing verdict")
    if result.get("kind") == "valid":
        inv = result.get("invariant")
        require(type(inv) is list and all(integer(q) and 0 <= q < len(d["trans"]) for q in inv), "bad invariant")
        require(inv == sorted(set(inv)) and d["start"] in inv, "invalid invariant initial state")
        states = set(inv)
        for q in inv:
            require(d["final"][q] and all(t in states for t in d["trans"][q]), "validity invariant failed")
    elif result.get("kind") == "counterexample":
        word = result.get("word")
        require(type(word) is list and len(word) <= 20000 and all(integer(a) and 0 <= a < 2 ** d["k"] for a in word), "invalid counterexample word")
        values = [sum(((letter // (2 ** i)) % 2) * (2 ** j) for j, letter in enumerate(word)) for i in range(d["k"])]
        require(same(values, result.get("values")), "counterexample decoding mismatch")
        q = d["start"]
        for letter in word:
            q = d["trans"][q][letter]
        require(not d["final"][q], "counterexample is accepted")
    else:
        raise Rejected("unknown verdict")
    return {"nodes": len(nodes), "transition_cells": total_cells,
            "root_states": len(d["trans"]), "verdict": result["kind"]}

def check_witness(d: dict, expected_inputs: list[int], record: dict) -> None:
    """Check a concrete witness against an ALREADY VERIFIED source automaton.
    This function alone does not establish a relation's source-level meaning.
    """
    require(type(expected_inputs) is list and all(integer(v) and v >= 0 for v in expected_inputs), "bad witness inputs")
    require(d["k"] == len(expected_inputs) + 1, "witness arity")
    require(same(record.get("inputs"), expected_inputs), "witness input mismatch")
    w, trace = record.get("word"), record.get("trace")
    require(type(w) is list and type(trace) is list and len(trace) == len(w) + 1, "bad witness trace")
    require(all(integer(a) and 0 <= a < 2 ** d["k"] for a in w), "bad witness letter")
    require(all(integer(q) and 0 <= q < len(d["trans"]) for q in trace), "bad witness state")
    require(trace[0] == d["start"], "witness initial state")
    for j, letter in enumerate(w):
        require(trace[j + 1] == d["trans"][trace[j]][letter], "witness trace equation")
    require(d["final"][trace[-1]], "witness is not accepted")
    values = [sum(((a // (2 ** i)) % 2) * (2 ** j) for j, a in enumerate(w)) for i in range(d["k"])]
    require(values[:-1] == expected_inputs and same(values[-1], record.get("witness")), "witness decoding equation")

def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("query", type=Path)
    p.add_argument("certificate", type=Path)
    args = p.parse_args()
    try:
        require(args.certificate.stat().st_size <= 100_000_000, "certificate byte limit")
        q, b = json.loads(args.query.read_text()), json.loads(args.certificate.read_text())
        print(json.dumps({"status": "accepted", **verify(b, q)}, sort_keys=True))
    except (Rejected, KeyError, IndexError, TypeError, ValueError, RecursionError) as e:
        print(json.dumps({"status": "rejected", "reason": str(e)}))
        raise SystemExit(1)

if __name__ == "__main__":
    main()
