#!/usr/bin/env python3
"""Compile every Mathlib-dependent Lean file OUTSIDE lean/Forge.

These are the proposals' own copies (proposals/*/lean) and the prototype's
emitted outputs (prototype/results/lean). Nothing had compiled any of them.
`tools/build_mathlib_forge.py` covers the files merged into lean/Forge; this
script covers the rest, so that the repository's count of unchecked Lean
reaches zero one way or the other.

WHAT "COMPILES" MEANS HERE. Each file is compiled with the Lean toolchain Forge
pins (v4.34.0) against the Mathlib revision Forge pins. That is NOT necessarily
the Mathlib its author had in mind -- none of these authors had a toolchain at
all -- so a failure may be API drift rather than a false proof, and the record
keeps the first errors verbatim so the two can be told apart. A success is
unambiguous: the file's theorems check against a real Mathlib.

HOW. Files are grouped by root -- the nearest enclosing `lean` directory -- and
module names are paths relative to that root, which is how their sibling
imports are written. Each root compiles in import order into its own scratch
library under lean/.lake/sweep/, so two proposals' `ReplayExamples` modules
cannot collide. A file importing a sibling that failed is recorded as skipped,
not failed. Every run is under the same memory ceiling and time limit as the
other Lean runs here, one file at a time.

The verdict per file is the EXIT CODE, no `: error` lines, and no `sorry`
warning. The source is also scanned for `native_decide` and `axiom`
declarations, which compile cleanly but would widen what is trusted.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import compare_tactics as ct  # noqa: E402
from check_lean import strip_lean_comments  # noqa: E402

LEAN = ROOT / "lean"
SWEEP = LEAN / ".lake" / "sweep"
IMPORT = re.compile(r"^\s*import\s+([\w.]+)", re.M)

# Written by a person after reading each failure's log; recorded beside the
# verdict, never used to compute it. The proposals' files are historical
# deliverables and are NOT edited to make them pass.
DIAGNOSES = {
    "proposals/p5-certificate-first/lean/Forge/Invariants.lean":
        "Defines real-valued functions without `noncomputable`, which Lean rejects. The merged "
        "copy, lean/Forge/Generated/Invariants.lean, compiles once marked noncomputable.",
    "proposals/r4-analytic-certificates/lean/LadderBridge.lean":
        "`dsimp made no progress` in `convert ... <;> dsimp [w] <;> ring`: the tactic script "
        "does not survive the pinned Mathlib. The statement is not refuted. Its four importers "
        "are skipped.",
    "proposals/r6-flow-ladders/lean/FlowTargets.lean":
        "A module docstring above `import`, which Lean 4 rejects at parse time on any version.",
    "proposals/r7-quantitative/lean/ForgeQ/FiniteHorizon.lean":
        "`add_le_add_left` produces `b + c <= a + c` in the pinned Mathlib, not `c + b <= c + a`: "
        "API drift in one proof step. The statement is not refuted.",
}


def tracked_mathlib_files() -> list[Path]:
    out = subprocess.run(["git", "ls-files", "*.lean"], cwd=ROOT, capture_output=True,
                         text=True, check=True).stdout.split()
    files = []
    for rel in out:
        if rel.startswith("lean/") or rel.endswith("lakefile.lean"):
            continue
        files.append(ROOT / rel)
    return files


def root_of(path: Path) -> Path:
    for parent in path.parents:
        if parent.name == "lean":
            return parent
    return path.parent


def module_of(path: Path, root: Path) -> str:
    return ".".join(path.relative_to(root).with_suffix("").parts)


def imports_of(path: Path) -> list[str]:
    return IMPORT.findall(strip_lean_comments(path.read_text(encoding="utf-8", errors="replace")))


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--mem-gb", type=float, default=8.0)
    ap.add_argument("--seconds", type=int, default=3600)
    ap.add_argument("--only", nargs="*", help="repository-relative paths")
    ap.add_argument("--out", type=Path, default=ROOT / "results" / "lean-mathlib-sweep.json")
    args = ap.parse_args()

    toolchain = (LEAN / "lean-toolchain").read_text().strip()
    lean = ct.toolchain_lean(toolchain.split(":")[-1])
    sep = ";" if os.name == "nt" else ":"
    mathlib_libs = ct.mathlib_libs(LEAN)

    # Transitive Mathlib dependence within each root.
    files = tracked_mathlib_files()
    by_root: dict[Path, dict[str, Path]] = {}
    for f in files:
        r = root_of(f)
        by_root.setdefault(r, {})[module_of(f, r)] = f

    def needs_mathlib(f: Path, mods: dict[str, Path], seen=()) -> bool:
        for imp in imports_of(f):
            if imp.split(".")[0] == "Mathlib":
                return True
            if imp in mods and mods[imp] not in seen and needs_mathlib(mods[imp], mods, seen + (f,)):
                return True
        return False

    steps = []
    dependencies = []
    previous = []
    if args.only and args.out.exists():
        record = json.loads(args.out.read_text(encoding="utf-8"))
        previous = [s for s in record["files"] if s["file"] not in args.only]
        dependencies = record.get("dependencies_built", record.get("core_only_dependencies_built", []))
    for r in sorted(by_root):
        mods = by_root[r]
        order, done = [], set()

        def visit(m):
            if m in done:
                return
            done.add(m)
            for imp in imports_of(mods[m]):
                if imp in mods:
                    visit(imp)
            order.append(m)
        for m in sorted(mods):
            visit(m)
        lib = SWEEP / r.relative_to(ROOT).as_posix().replace("/", "__")
        # Forge's own build comes after the root's: r1 was written against the
        # merged tree and imports Forge.Closure.Covers.
        forge_lib = LEAN / ".lake" / "build" / "lib" / "lean"
        env = dict(os.environ, LEAN_PATH=sep.join([str(lib), str(forge_lib)] + mathlib_libs))
        failed: set[str] = set()
        targets = {m for m, f in mods.items() if needs_mathlib(f, mods)
                   and (not args.only or f.relative_to(ROOT).as_posix() in args.only)}
        # Siblings that a target imports must be built first -- core-only ones, and
        # on a rerun, Mathlib ones already recorded. They are not counted again;
        # their outcome is recorded separately.
        needed, stack = set(), list(targets)
        while stack:
            m = stack.pop()
            if m in needed:
                continue
            needed.add(m)
            stack += [i for i in imports_of(mods[m]) if i in mods]
        for m in order:
            src = mods[m]
            rel = src.relative_to(ROOT).as_posix()
            if m not in needed:
                continue
            if m not in targets:
                out = lib / (m.replace(".", "/") + ".olean")
                out.parent.mkdir(parents=True, exist_ok=True)
                log = lib / (m + ".out")
                run = ct.run_guarded([str(lean), "-o", str(out), str(src)], env, str(r),
                                     args.mem_gb, args.seconds, log)
                text = log.read_text(encoding="utf-8", errors="replace")
                ok = run["exit_code"] == 0 and ": error" not in text and not run["killed"]
                if not ok:
                    failed.add(m)
                dependencies[:] = [d for d in dependencies if d["file"] != rel]
                dependencies.append({"file": rel, "module": m, "compiled": ok,
                                     "needs_mathlib": needs_mathlib(src, mods), **run})
                print("%-70s dependency %s" % (rel, "built" if ok else "FAILED"))
                continue
            code = strip_lean_comments(src.read_text(encoding="utf-8", errors="replace"))
            trust = {"native_decide": len(re.findall(r"\bnative_decide\b", code)),
                     "axiom_declarations": re.findall(r"^\s*axiom\s+([\w.']+)", code, re.M)}
            blocked = [i for i in imports_of(src) if i in failed]
            if blocked:
                failed.add(m)
                steps.append({"file": rel, "module": m, "status": "skipped",
                              "reason": "imports a sibling that failed: %s" % blocked, **trust})
                print("%-70s SKIPPED" % rel)
                continue
            out = lib / (m.replace(".", "/") + ".olean")
            out.parent.mkdir(parents=True, exist_ok=True)
            log = lib / (m + ".out")
            run = ct.run_guarded([str(lean), "-o", str(out), str(src)], env, str(r),
                                 args.mem_gb, args.seconds, log)
            text = log.read_text(encoding="utf-8", errors="replace")
            errors = [ln for ln in text.splitlines() if ": error" in ln]
            sorries = [ln for ln in text.splitlines() if "declaration uses 'sorry'" in ln
                       or "declaration uses `sorry`" in ln]
            ok = run["exit_code"] == 0 and not errors and not sorries and not run["killed"]
            if not ok:
                failed.add(m)
            # A nonzero exit with no output at all is the process dying (on this
            # machine, memory pressure from other Lean jobs), not a verdict.
            status = ("compiled" if ok else
                      "crashed" if not text.strip() and not run["killed"] else "failed")
            if not ok and rel in DIAGNOSES:
                run = {**run, "diagnosis": DIAGNOSES[rel]}
            steps.append({"file": rel, "module": m, "status": status, **run,
                          "errors": len(errors), "sorry_warnings": len(sorries),
                          "first_errors": [re.sub(r"^.*?\.lean:", "", e)[:300] for e in errors[:6]],
                          **trust})
            print("%-70s %s errors=%d sorry=%d %.0fs peak=%.2fGB%s"
                  % (rel, status, len(errors), len(sorries), run["seconds"],
                     run["peak_rss_gb"], "  KILLED: %s" % run["killed"] if run["killed"] else ""))
            # Write as we go: a long sweep should leave a record if interrupted.
            write(args.out, toolchain, sorted(previous + steps, key=lambda e: e["file"]), dependencies)
    write(args.out, toolchain, sorted(previous + steps, key=lambda e: e["file"]), dependencies)
    print(" ".join("%s=%d" % (k, sum(1 for e in steps if e["status"] == k))
                   for k in ("compiled", "failed", "crashed", "skipped")))
    return 0


def write(path: Path, toolchain: str, steps: list, dependencies: list) -> None:
    path.write_text(json.dumps({
        "what": ("Compilation of every Mathlib-dependent Lean file outside lean/Forge -- the "
                 "proposals' own copies and prototype/results/lean -- on the toolchain and "
                 "Mathlib revision Forge pins, which are not necessarily the ones their "
                 "authors targeted."),
        "toolchain": toolchain,
        "mathlib": "lean/.lake/packages/mathlib (rev pinned in lean/lakefile.toml)",
        "verdict_rule": "exit code 0, no error lines, no sorry warning",
        "counts": {k: sum(1 for s in steps if s["status"] == k)
                   for k in ("compiled", "failed", "crashed", "skipped")},
        "files": steps,
        "dependencies_built": dependencies,
    }, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


if __name__ == "__main__":
    raise SystemExit(main())
