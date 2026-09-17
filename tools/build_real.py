#!/usr/bin/env python3
"""Compile and audit lean/Forge/Real/, the soundness-over-the-reals layer.

These files import Mathlib. The only built Mathlib on this machine is for Lean
v4.32.0, while Forge pins v4.34.0, so -- exactly as for the tactic head-to-head
-- the core modules they need are compiled with v4.32 into an ignored build
directory and the Real files are compiled against them and Mathlib. The
toolchain is recorded in the result.

The process tree runs under the same memory ceiling and time limit as the
head-to-head. The verdict is Lean's EXIT CODE; axioms are read from
`#print axioms` lines in the Examples file and recorded as they are.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import compare_tactics as ct  # noqa: E402

LIB = ROOT / "lean" / "Forge" / "Real" / ".lake" / "build" / "lib"
CORE = ["Poly", "Cone", "Corpus"]
REAL = ["Cone", "Examples"]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--toolchain", default="v4.32.0")
    ap.add_argument("--mathlib-root", type=Path, default=Path("C:/ProveIt"))
    ap.add_argument("--mem-gb", type=float, default=12.0)
    ap.add_argument("--seconds", type=int, default=3600)
    ap.add_argument("--out", type=Path, default=ROOT / "results" / "lean-real.json")
    args = ap.parse_args()

    lean = ct.toolchain_lean(args.toolchain)
    sep = ";" if os.name == "nt" else ":"
    libs = [str(LIB)] + ct.mathlib_libs(args.mathlib_root)
    env = dict(os.environ, LEAN_PATH=sep.join(libs))
    logdir = LIB.parent
    logdir.mkdir(parents=True, exist_ok=True)
    steps = []

    def compile_one(src: Path, out: Path, name: str) -> bool:
        out.parent.mkdir(parents=True, exist_ok=True)
        log = logdir / ("%s.out" % name.replace("/", "_"))
        run = ct.run_guarded([str(lean), "-o", str(out), str(src)], env, str(ROOT / "lean"),
                             args.mem_gb, args.seconds, log)
        text = log.read_text(encoding="utf-8", errors="replace")
        errors = [ln for ln in text.splitlines() if ": error" in ln]
        steps.append({"module": name, **run, "errors": len(errors), "first_errors": errors[:5]})
        print("%-28s exit=%s errors=%d %.1fs peak=%.2fGB%s"
              % (name, run["exit_code"], len(errors), run["seconds"], run["peak_rss_gb"],
                 "  KILLED: %s" % run["killed"] if run["killed"] else ""))
        return run["exit_code"] == 0 and not errors and not run["killed"]

    ok = True
    for mod in CORE:
        ok = ok and compile_one(ROOT / "lean" / "Forge" / "Checker" / (mod + ".lean"),
                                LIB / "Forge" / "Checker" / (mod + ".olean"), "Checker/" + mod)
    for mod in REAL:
        if not ok:
            break
        ok = ok and compile_one(ROOT / "lean" / "Forge" / "Real" / (mod + ".lean"),
                                LIB / "Forge" / "Real" / (mod + ".olean"), "Real/" + mod)

    axioms = {}
    ex_log = logdir / "Real_Examples.out"
    if ex_log.exists():
        for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]",
                             ex_log.read_text(encoding="utf-8", errors="replace")):
            axioms[m.group(1)] = [a.strip() for a in m.group(2).split(",") if a.strip()]
    leaked = {n: a for n, a in axioms.items()
              if set(a) - {"propext", "Classical.choice", "Quot.sound"}}

    args.out.write_text(json.dumps({
        "what": "Soundness of cone certificates over the reals: lean/Forge/Real/.",
        "toolchain": args.toolchain,
        "mathlib_root": str(args.mathlib_root),
        "forge_pins": "leanprover/lean4:v4.34.0 (core modules compile unchanged on v4.32)",
        "compiled": ok,
        "steps": steps,
        "axioms": axioms,
        "axioms_beyond_propext_choice_quotsound": leaked,
        "note": ("Mathlib's reals are built with Classical.choice, so these theorems use "
                 "propext, Classical.choice and Quot.sound, unlike the core files."),
    }, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print("axioms:", axioms)
    return 0 if ok and axioms and not leaked else 1


if __name__ == "__main__":
    raise SystemExit(main())
