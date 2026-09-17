#!/usr/bin/env python3
"""Run the Forge oracle directly on bench/tactics/problems.json, without Lean.

The full head-to-head loads Mathlib and takes minutes. Changing the SEARCH does
not need Lean to be measured: the oracle is a Python process, and whether it
returns a certificate is decided there. This probe converts each problem to the
oracle's input with SymPy, runs `tools/forge_oracle.py`, and reports its status.

It is a development loop, not evidence. A certificate the oracle returns is
still only a claim until the Lean kernel checks it; `tools/compare_tactics.py`
is what records results.

Conversion, matching `forge_cone?`'s reification:
  goal `a <= b`  -> target  b - a      goal `0 <= e` -> target e
  hyp  `a <= b`  -> inequality b - a   hyp  `a = b`  -> equality a - b
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from pathlib import Path

import sympy as sp

ROOT = Path(__file__).resolve().parents[2]
if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")


def side(text: str, syms: dict) -> sp.Expr:
    return sp.sympify(text.replace("^", "**"), locals=syms)


def difference(rel: str, syms: dict) -> tuple[str, sp.Expr]:
    for op, kind in (("≤", "le"), ("≥", "ge"), ("=", "eq")):
        if op in rel:
            a, b = rel.split(op)
            a, b = side(a, syms), side(b, syms)
            if kind == "le":
                return "ineq", sp.expand(b - a)
            if kind == "ge":
                return "ineq", sp.expand(a - b)
            return "eq", sp.expand(a - b)
    raise ValueError("unsupported relation %r" % rel)


def poly_json(expr: sp.Expr, vs: list) -> dict:
    p = sp.Poly(expr, *vs)
    return {"n": len(vs), "terms": [[list(m), str(c)] for m, c in p.terms()]}


def problem_input(problem: dict) -> dict:
    syms = {v: sp.Symbol(v) for v in problem["vars"]}
    vs = [syms[v] for v in problem["vars"]]
    _, target = difference(problem["goal"], syms)
    ineqs, eqs = [], []
    for _, h in problem["hyps"]:
        kind, e = difference(h, syms)
        (ineqs if kind == "ineq" else eqs).append(poly_json(e, vs))
    return {"target": poly_json(target, vs), "inequalities": ineqs, "equalities": eqs}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--only", nargs="*")
    args = ap.parse_args()
    problems = json.loads((ROOT / "bench" / "tactics" / "problems.json")
                          .read_text(encoding="utf-8"))["problems"]
    if args.only:
        problems = [p for p in problems if p["id"] in args.only]
    found = 0
    for p in problems:
        t0 = time.monotonic()
        r = subprocess.run([sys.executable, str(ROOT / "tools" / "forge_oracle.py")],
                           input=json.dumps(problem_input(p)), capture_output=True,
                           text=True, encoding="utf-8")
        ms = int((time.monotonic() - t0) * 1000)
        try:
            out = json.loads(r.stdout)
        except json.JSONDecodeError:
            out = {"status": "crash", "reason": (r.stderr or r.stdout)[-200:]}
        ok = out.get("status") == "certificate"
        found += ok
        print("%-20s %-11s %5d ms  %s" % (p["id"], out.get("status"), ms,
                                          "" if ok else out.get("reason", "")[:110]))
    print("certificates found: %d of %d" % (found, len(problems)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
