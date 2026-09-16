"""Search-free, exact certificate checker. No imports from the producer/model.

This is ordinary Python validation, NOT a verified checker and NOT a Lean proof.
ResourceLimit is an inconclusive operational refusal, not a mathematical result.
Word summaries are recomputed as (minimum input, SIGNED net change), independently
of the producer's (consumption, production) composition implementation.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import product
from math import prod
from typing import Any
import json


class InvalidCertificate(ValueError):
    pass


class ResourceLimit(RuntimeError):
    pass


@dataclass(frozen=True)
class Limits:
    dimension: int = 128
    transitions: int = 10_000
    basis: int = 5_000
    nodes: int = 100_000
    input_bits: int = 4096
    summary_bits: int = 16384
    box_cells: int = 1_000_000
    file_bytes: int = 128 * 1024 * 1024


DEFAULT_LIMITS = Limits()


def fail(message: str) -> None:
    raise InvalidCertificate(message)


def same_json(a: Any, b: Any) -> bool:
    """Type-aware structural identity: True is NOT the integer 1."""
    if type(a) is not type(b):
        return False
    if type(a) is dict:
        return set(a) == set(b) and all(same_json(a[k], b[k]) for k in a)
    if type(a) is list:
        return len(a) == len(b) and all(same_json(x, y) for x, y in zip(a, b))
    return a == b


def fields(x: Any, keys: set[str], context: str) -> None:
    if type(x) is not dict or set(x) != keys:
        fail(f"{context}: wrong or unsupported fields")


def nat(x: Any, limits: Limits, context: str = "integer") -> int:
    if type(x) is not int or x < 0:
        fail(f"{context}: expected nonnegative integer, not Boolean")
    if x.bit_length() > limits.input_bits:
        raise ResourceLimit(f"{context}: input integer exceeds bit budget")
    return x


def arr(x: Any, context: str) -> list[Any]:
    if type(x) is not list:
        fail(f"{context}: expected a JSON list")
    return x


def vec(x: Any, d: int, limits: Limits, context: str = "vector") -> tuple[int, ...]:
    arr(x, context)
    if len(x) != d:
        fail(f"{context}: dimension mismatch")
    return tuple(nat(a, limits, context) for a in x)


def idx(x: Any, n: int, context: str) -> int:
    if type(x) is not int or not 0 <= x < n:
        fail(f"{context}: index out of range")
    return x


def below(a: tuple[int, ...], b: tuple[int, ...]) -> bool:
    # Only validated vectors enter here; do not let zip silently erase dimensions.
    if len(a) != len(b):
        fail("internal dimension mismatch")
    return all(a[i] <= b[i] for i in range(len(a)))


def validate_problem(p: Any, limits: Limits = DEFAULT_LIMITS) -> tuple[int, list[dict[str, Any]], list[tuple[int, ...]]]:
    fields(p, {"kind", "dimension", "transitions", "targets"}, "problem")
    if p["kind"] != "pt-net-coverability":
        fail("unsupported semantics: expected ordinary place/transition net")
    d = nat(p["dimension"], limits, "dimension")
    if d > limits.dimension:
        raise ResourceLimit("dimension budget")
    ts = arr(p["transitions"], "transitions")
    if len(ts) > limits.transitions:
        raise ResourceLimit("transition budget")
    names = set()
    for t in ts:
        fields(t, {"name", "consume", "produce"}, "transition")
        if type(t["name"]) is not str or len(t["name"]) > 65536:
            fail("invalid transition name")
        if t["name"] in names:
            fail("duplicate transition name")
        names.add(t["name"])
        vec(t["consume"], d, limits); vec(t["produce"], d, limits)
    targets = arr(p["targets"], "targets")
    if len(targets) > limits.basis:
        raise ResourceLimit("target budget")
    return d, ts, [vec(b, d, limits, "target") for b in targets]


def canonical_antichain(vs: list[tuple[int, ...]], context: str) -> None:
    if vs != sorted(vs):
        fail(f"{context}: not sorted")
    for i in range(len(vs)):
        for j in range(i):
            if below(vs[i], vs[j]) or below(vs[j], vs[i]):
                fail(f"{context}: duplicate or dominated element")


def check_runs(problem: dict[str, Any], nodes: Any, limits: Limits = DEFAULT_LIMITS
               ) -> list[tuple[tuple[int, ...], tuple[int, ...], int]]:
    d, transitions, _ = validate_problem(problem, limits)
    nodes = arr(nodes, "runs")
    if len(nodes) > limits.nodes:
        raise ResourceLimit("run DAG node budget")
    if not nodes:
        fail("empty run DAG")
    summaries = []
    for number, node in enumerate(nodes):
        if type(node) is not dict or type(node.get("op")) is not str:
            fail("missing run opcode")
        op = node["op"]
        if op == "empty":
            fields(node, {"op"}, "empty node")
            need = (0,) * d; delta = (0,) * d; length = 0
        elif op == "step":
            fields(node, {"op", "transition"}, "step node")
            t = transitions[idx(node["transition"], len(transitions), "transition reference")]
            need = tuple(t["consume"])
            delta = tuple(t["produce"][i] - t["consume"][i] for i in range(d))
            length = 1
        elif op == "seq":
            fields(node, {"op", "left", "right"}, "sequence node")
            r, e, n = summaries[idx(node["left"], number, "left DAG reference")]
            s, f, m = summaries[idx(node["right"], number, "right DAG reference")]
            need = tuple(max(r[i], s[i] - e[i]) for i in range(d))
            delta = tuple(e[i] + f[i] for i in range(d))
            length = n + m
        elif op == "repeat":
            fields(node, {"op", "body", "count"}, "repeat node")
            r, e, n = summaries[idx(node["body"], number, "body DAG reference")]
            count = nat(node["count"], limits, "repeat count")
            if count == 0:
                need = (0,) * d; delta = (0,) * d; length = 0
            else:
                need = tuple(r[i] + (count - 1) * max(0, -e[i]) for i in range(d))
                delta = tuple(count * e[i] for i in range(d))
                length = count * n
        else:
            fail("unknown run opcode")
        if any(x < 0 for x in need) or any(need[i] + delta[i] < 0 for i in range(d)):
            fail("invalid resource summary")
        if any(abs(x).bit_length() > limits.summary_bits for x in (*need, *delta, length)):
            raise ResourceLimit("intermediate run summary exceeds bit budget")
        summaries.append((need, delta, length))
    return summaries


def execute_summary(summary: tuple[tuple[int, ...], tuple[int, ...], int],
                    state: tuple[int, ...]) -> tuple[int, ...]:
    need, delta, _ = summary
    if not below(need, state):
        fail("claimed run is not enabled at its supplied starting marking")
    return tuple(state[i] + delta[i] for i in range(len(state)))


def check_frontier(expected_problem: dict[str, Any], cert: Any,
                   limits: Limits = DEFAULT_LIMITS) -> dict[str, Any]:
    d, transitions, targets = validate_problem(expected_problem, limits)
    fields(cert, {"schema", "problem", "basis", "runs", "target_cover", "predecessor_cover"},
           "frontier certificate")
    if cert["schema"] != "forge.resources.frontier.v1":
        fail("wrong frontier schema")
    validate_problem(cert["problem"], limits)
    if not same_json(cert["problem"], expected_problem):
        fail("certificate is not bound to the exact supplied problem")
    entries = arr(cert["basis"], "basis")
    if len(entries) > limits.basis:
        raise ResourceLimit("basis budget")
    markings = []
    for entry in entries:
        fields(entry, {"marking", "run", "target"}, "basis entry")
        markings.append(vec(entry["marking"], d, limits, "basis marking"))
    canonical_antichain(markings, "basis")
    runs = check_runs(expected_problem, cert["runs"], limits)
    for entry, marking in zip(entries, markings):
        summary = runs[idx(entry["run"], len(runs), "basis run")]
        target = targets[idx(entry["target"], len(targets), "basis target")]
        end = execute_summary(summary, marking)
        if not below(target, end):
            fail("basis witness does not cover its claimed original target")
    tc = arr(cert["target_cover"], "target cover")
    if len(tc) != len(targets):
        fail("target coverage is incomplete")
    for b, i in zip(targets, tc):
        if not below(markings[idx(i, len(markings), "target-cover reference")], b):
            fail("an original target is not covered by the basis")
    rows = arr(cert["predecessor_cover"], "predecessor cover")
    if len(rows) != len(markings):
        fail("missing predecessor rows")
    for b, row in zip(markings, rows):
        arr(row, "predecessor row")
        if len(row) != len(transitions):
            fail("missing predecessor obligations")
        for t, i in zip(transitions, row):
            # Exact lower threshold for enabling t and covering b in its successor.
            predecessor = tuple(t["consume"][j] + max(0, b[j] - t["produce"][j])
                                for j in range(d))
            a = markings[idx(i, len(markings), "predecessor-cover reference")]
            if not below(a, predecessor):
                fail("basis is not backward closed")
    return {"status": "PYTHON_CHECKED", "meaning": "exact minimal coverability frontier",
            "basis": [list(b) for b in markings], "run_nodes": len(runs),
            "maximum_witness_length": max([0] + [runs[e["run"]][2] for e in entries])}


def check_threshold(expected_query: dict[str, Any], cert: Any,
                    limits: Limits = DEFAULT_LIMITS) -> dict[str, Any]:
    fields(expected_query, {"problem", "slope", "offset"}, "threshold query")
    d, _, _ = validate_problem(expected_query["problem"], limits)
    a = vec(expected_query["slope"], d, limits, "slope")
    c = vec(expected_query["offset"], d, limits, "offset")
    fields(cert, {"schema", "query", "frontier", "basis_thresholds", "threshold"}, "threshold certificate")
    if cert["schema"] != "forge.resources.threshold.v1" or not same_json(cert["query"], expected_query):
        fail("threshold schema or query mismatch")
    checked = check_frontier(expected_query["problem"], cert["frontier"], limits)
    entries = checked["basis"]
    bs = arr(cert["basis_thresholds"], "basis thresholds")
    if len(bs) != len(entries):
        fail("missing basis threshold")
    recomputed = []
    for b, supplied in zip(entries, bs):
        impossible = any(a[i] == 0 and c[i] < b[i] for i in range(d))
        if impossible:
            if supplied is not None:
                fail("infeasible basis is assigned a finite threshold")
            recomputed.append(None)
            continue
        n = nat(supplied, limits, "basis threshold")
        # Check feasibility and predecessor failure, instead of trusting ceiling division.
        if not all(c[i] + n * a[i] >= b[i] for i in range(d)):
            fail("basis threshold is not feasible")
        if n > 0 and all(c[i] + (n - 1) * a[i] >= b[i] for i in range(d)):
            fail("basis threshold is not least")
        recomputed.append(n)
    finite = [n for n in recomputed if n is not None]
    expected = min(finite) if finite else None
    if cert["threshold"] is not None:
        nat(cert["threshold"], limits, "global threshold")
    if cert["threshold"] != expected:
        fail("global threshold mismatch")
    return {"status": "PYTHON_CHECKED", "meaning": "least unsafe natural parameter",
            "threshold": expected, "all_safe": expected is None}


def check_parameters(expected_query: dict[str, Any], cert: Any,
                     limits: Limits = DEFAULT_LIMITS) -> dict[str, Any]:
    fields(expected_query, {"problem", "matrix", "offset"}, "parameter query")
    d, _, _ = validate_problem(expected_query["problem"], limits)
    if d == 0:
        fail("parameter matrix encoding requires at least one place")
    matrix = arr(expected_query["matrix"], "affine matrix")
    if len(matrix) != d:
        fail("matrix row dimension")
    k = len(arr(matrix[0], "matrix row"))
    if k > limits.dimension:
        raise ResourceLimit("parameter dimension budget")
    A = [vec(row, k, limits, "matrix row") for row in matrix]
    c = vec(expected_query["offset"], d, limits, "offset")
    fields(cert, {"schema", "query", "frontier", "caps", "minima", "witness_basis", "covers"},
           "parameter certificate")
    if cert["schema"] != "forge.resources.parameters.v1" or not same_json(cert["query"], expected_query):
        fail("parameter schema or exact query mismatch")
    checked = check_frontier(expected_query["problem"], cert["frontier"], limits)
    B = [tuple(b) for b in checked["basis"]]
    eligible = [b for b in B if all(c[i] >= b[i] or any(A[i]) for i in range(d))]
    caps = vec(cert["caps"], k, limits, "caps")
    # Verify each cap directly as the least nonnegative integer satisfying all
    # relevant single-contribution requirements. This differs from the producer's ceil.
    for j in range(k):
        requirements = [(A[i][j], max(0, b[i] - c[i]))
                        for b in eligible for i in range(d) if A[i][j] > 0]
        if any(a * caps[j] < demand for a, demand in requirements):
            fail("cap is too small")
        if caps[j] > 0 and all(a * (caps[j] - 1) >= demand for a, demand in requirements):
            fail("cap is not canonical")
    cells = prod(x + 1 for x in caps)
    if cells > limits.box_cells:
        raise ResourceLimit("certified parameter box exceeds checker budget")
    minima_raw = arr(cert["minima"], "parameter minima")
    if len(minima_raw) > limits.basis:
        raise ResourceLimit("parameter frontier budget")
    minima = [vec(f, k, limits, "parameter minimum") for f in minima_raw]
    canonical_antichain(minima, "parameter minima")

    def marking(theta: tuple[int, ...]) -> tuple[int, ...]:
        return tuple(c[i] + sum(A[i][j] * theta[j] for j in range(k)) for i in range(d))

    witnesses = arr(cert["witness_basis"], "parameter witnesses")
    if len(witnesses) != len(minima):
        fail("missing parameter witness")
    for f, b_index in zip(minima, witnesses):
        if not below(f, caps):
            fail("parameter minimum outside proved cap")
        b = B[idx(b_index, len(B), "parameter witness basis")]
        if not below(b, marking(f)):
            fail("parameter minimum is not unsafe")
    covers = arr(cert["covers"], "parameter cover table")
    if len(covers) != cells:
        fail("parameter box table is incomplete")
    for theta, label in zip(product(*(range(x + 1) for x in caps)), covers):
        if type(label) is not int:
            fail("noninteger parameter cover label")
        unsafe = any(below(b, marking(theta)) for b in B)
        if label == -1:
            if unsafe:
                fail("unsafe parameter cell mislabeled safe")
        else:
            f = minima[idx(label, len(minima), "parameter cover label")]
            if not unsafe or not below(f, theta):
                fail("false parameter domination witness")
    return {"status": "PYTHON_CHECKED", "meaning": "exact minimal unsafe parameter frontier",
            "minima": [list(f) for f in minima], "box_cells": cells}


def check_lasso(expected_query: dict[str, Any], cert: Any,
                limits: Limits = DEFAULT_LIMITS) -> dict[str, Any]:
    fields(expected_query, {"problem", "initial", "claim", "place"}, "lasso query")
    d, _, _ = validate_problem(expected_query["problem"], limits)
    initial = vec(expected_query["initial"], d, limits, "initial marking")
    claim = expected_query["claim"]
    if claim not in ("unbounded", "nontermination"):
        fail("unknown lasso claim")
    place = expected_query["place"]
    if claim == "unbounded":
        idx(place, d, "growing place")
    elif place is not None:
        fail("nontermination claim must not pretend to identify an unbounded place")
    fields(cert, {"schema", "query", "runs", "prefix", "loop"}, "lasso certificate")
    if cert["schema"] != "forge.resources.lasso.v1" or not same_json(cert["query"], expected_query):
        fail("lasso schema or exact query mismatch")
    runs = check_runs(expected_query["problem"], cert["runs"], limits)
    stem = execute_summary(runs[idx(cert["prefix"], len(runs), "prefix")], initial)
    loop = runs[idx(cert["loop"], len(runs), "loop")]
    if loop[2] == 0:
        fail("empty loop is not an infinite execution")
    execute_summary(loop, stem)
    if any(e < 0 for e in loop[1]):
        fail("loop does not self-cover")
    if claim == "unbounded" and loop[1][place] <= 0:
        fail("claimed place does not grow")
    return {"status": "PYTHON_CHECKED", "meaning": claim, "stem": list(stem),
            "growth": list(loop[1]), "loop_length": loop[2],
            "prefix_length": runs[cert["prefix"]][2], "run_nodes": len(runs)}


def check_run(expected_query: dict[str, Any], cert: Any,
              limits: Limits = DEFAULT_LIMITS) -> dict[str, Any]:
    fields(expected_query, {"problem", "initial", "final", "length"}, "run query")
    d, _, _ = validate_problem(expected_query["problem"], limits)
    initial = vec(expected_query["initial"], d, limits, "initial marking")
    final = vec(expected_query["final"], d, limits, "final marking")
    length = nat(expected_query["length"], limits, "run length")
    fields(cert, {"schema", "query", "runs", "root"}, "run certificate")
    if cert["schema"] != "forge.resources.run.v1" or not same_json(cert["query"], expected_query):
        fail("run schema or exact query mismatch")
    runs = check_runs(expected_query["problem"], cert["runs"], limits)
    summary = runs[idx(cert["root"], len(runs), "run root")]
    if execute_summary(summary, initial) != final or summary[2] != length:
        fail("run endpoint or length mismatch")
    return {"status": "PYTHON_CHECKED", "meaning": "exact compressed finite run",
            "run_nodes": len(runs), "represented_length": length}


def check_equivalence(expected_query: dict[str, Any], cert: Any,
                      limits: Limits = DEFAULT_LIMITS) -> dict[str, Any]:
    fields(expected_query, {"problem", "left", "right"}, "equivalence query")
    d, _, _ = validate_problem(expected_query["problem"], limits)
    fields(cert, {"schema", "query", "verdict", "separating_initial"}, "equivalence certificate")
    if cert["schema"] != "forge.resources.equivalence.v1" or not same_json(cert["query"], expected_query):
        fail("equivalence schema or exact query mismatch")
    summaries = []
    for side in ("left", "right"):
        program = expected_query[side]
        fields(program, {"nodes", "root"}, "original compressed program")
        rs = check_runs(expected_query["problem"], program["nodes"], limits)
        summaries.append(rs[idx(program["root"], len(rs), "original program root")])
    left, right = summaries
    # Step count is deliberately NOT part of the observed partial function.
    if cert["verdict"] == "equivalent":
        if cert["separating_initial"] is not None or left[:2] != right[:2]:
            fail("false guarded endpoint equivalence")
        meaning = "equal guarded endpoint partial functions"
    elif cert["verdict"] == "different":
        initial = vec(cert["separating_initial"], d, limits, "separating initial marking")
        outputs = [execute_summary(s, initial) if below(s[0], initial) else None
                   for s in summaries]
        if outputs[0] == outputs[1]: fail("marking does not distinguish the programs")
        meaning = "different guarded endpoint partial functions"
    else:
        fail("unknown equivalence verdict")
    return {"status": "PYTHON_CHECKED", "meaning": meaning,
            "verdict": cert["verdict"], "left_length": left[2], "right_length": right[2]}


def check_record(record: Any, limits: Limits = DEFAULT_LIMITS) -> dict[str, Any]:
    fields(record, {"name", "expected", "certificate"}, "replay record")
    if type(record["name"]) is not str:
        fail("record name must be a string")
    cert = record["certificate"]
    if type(cert) is not dict:
        fail("missing certificate")
    functions = {"forge.resources.equivalence.v1": check_equivalence,
                 "forge.resources.run.v1": check_run,
                 "forge.resources.frontier.v1": check_frontier,
                 "forge.resources.threshold.v1": check_threshold,
                 "forge.resources.parameters.v1": check_parameters,
                 "forge.resources.lasso.v1": check_lasso}
    schema = cert.get("schema")
    if type(schema) is not str or schema not in functions:
        fail("unknown certificate schema")
    return functions[schema](record["expected"], cert, limits)


def load_json(text: str) -> Any:
    """Reject duplicate JSON keys; ordinary json.loads would silently retain the last."""
    def distinct(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for k, v in pairs:
            if k in result:
                fail("duplicate JSON object key")
            result[k] = v
        return result
    return json.loads(text, object_pairs_hook=distinct,
                      parse_constant=lambda _: fail("non-finite JSON number"))
