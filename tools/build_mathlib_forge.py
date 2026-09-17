#!/usr/bin/env python3
"""Compile the Mathlib-dependent files under lean/Forge on the PINNED toolchain.

Until this script, none of lean/Forge/Generated/*, lean/Forge/Examples/* (bar
Structural) had been compiled by anything: the only built Mathlib on the
machine was for Lean v4.32, and Forge pins v4.34. `lake build` has since
fetched the Mathlib revision the lakefile pins, with its prebuilt cache, into
lean/.lake/packages, so each file can now be checked against exactly the
Mathlib it names.

`lake env` is not used: with no lake-manifest.json (deliberately absent, see
the lakefile) it re-runs dependency resolution and the cache fetch on every
call. Instead the v4.34 `lean` is run with LEAN_PATH set to the package build
directories plus Forge's own, one file at a time, in import order, under the
same memory ceiling and time limit as every other Lean run in this repository.

The verdict per file is Lean's EXIT CODE plus the absence of `sorry` warnings.
When every file compiles, lean/MathlibAudit.lean walks the environment and fails
if any theorem declared in these modules uses an axiom beyond propext,
Classical.choice and Quot.sound; `#print axioms` lines are recorded as well. Nothing is
inferred from a file failing: the first errors are recorded verbatim.
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

LEAN = ROOT / "lean"
LIB = LEAN / ".lake" / "build" / "lib" / "lean"
GROUPS = ["Generated", "Examples", "Real"]


def forge_imports(path: Path) -> list[str]:
    mods = []
    for line in path.read_text(encoding="utf-8").splitlines():
        m = re.match(r"\s*import\s+(Forge\.[\w.]+)", line)
        if m:
            mods.append(m.group(1))
    return mods


def module_of(path: Path) -> str:
    return ".".join(path.relative_to(LEAN).with_suffix("").parts)


def ordered_files() -> list[Path]:
    files = []
    for g in GROUPS:
        for p in sorted((LEAN / "Forge" / g).glob("*.lean")):
            if "import Mathlib" in p.read_text(encoding="utf-8") or g == "Real":
                files.append(p)
    by_mod = {module_of(p): p for p in files}
    done, out = set(), []

    def visit(p):
        m = module_of(p)
        if m in done:
            return
        done.add(m)
        for dep in forge_imports(p):
            if dep in by_mod:
                visit(by_mod[dep])
        out.append(p)
    for p in files:
        visit(p)
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--mem-gb", type=float, default=12.0)
    ap.add_argument("--seconds", type=int, default=3600)
    ap.add_argument("--only", nargs="*", help="module names to compile")
    ap.add_argument("--out", type=Path, default=ROOT / "results" / "lean-mathlib-forge.json")
    args = ap.parse_args()

    toolchain = (LEAN / "lean-toolchain").read_text().strip()
    version = toolchain.split(":")[-1]
    mathlib_toolchain = (LEAN / ".lake" / "packages" / "mathlib" / "lean-toolchain").read_text().strip()
    if mathlib_toolchain != toolchain:
        raise SystemExit("Mathlib is for %s, Forge pins %s" % (mathlib_toolchain, toolchain))
    lean = ct.toolchain_lean(version)
    sep = ";" if os.name == "nt" else ":"
    env = dict(os.environ, LEAN_PATH=sep.join([str(LIB)] + ct.mathlib_libs(LEAN)))
    logdir = LEAN / ".lake" / "mathlib-forge"
    logdir.mkdir(parents=True, exist_ok=True)

    steps = []
    failed_modules: set[str] = set()
    for src in ordered_files():
        mod = module_of(src)
        if args.only and mod not in args.only:
            continue
        blocked = [d for d in forge_imports(src) if d in failed_modules]
        if blocked:
            steps.append({"module": mod, "skipped": "imports a module that failed: %s" % blocked})
            failed_modules.add(mod)
            print("%-34s SKIPPED (imports %s)" % (mod, blocked))
            continue
        out = LIB / src.relative_to(LEAN).with_suffix(".olean")
        out.parent.mkdir(parents=True, exist_ok=True)
        log = logdir / (mod + ".out")
        run = ct.run_guarded([str(lean), "-o", str(out), str(src)], env, str(LEAN),
                             args.mem_gb, args.seconds, log)
        text = log.read_text(encoding="utf-8", errors="replace")
        errors = [ln for ln in text.splitlines() if ": error" in ln]
        sorries = [ln for ln in text.splitlines() if "declaration uses 'sorry'" in ln]
        warnings = [ln for ln in text.splitlines() if ": warning" in ln]
        axioms = {m.group(1): [a.strip() for a in m.group(2).split(",") if a.strip()]
                  for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text)}
        no_axioms = re.findall(r"'([^']+)' does not depend on any axioms", text)
        ok = run["exit_code"] == 0 and not errors and not sorries and not run["killed"]
        if not ok:
            failed_modules.add(mod)
        steps.append({"module": mod, "compiled": ok, **run, "errors": len(errors),
                      "sorry_warnings": len(sorries), "warnings": len(warnings),
                      "first_errors": errors[:8], "axioms": axioms,
                      "no_axioms": no_axioms})
        print("%-34s exit=%s errors=%d sorry=%d warnings=%d %.1fs peak=%.2fGB%s"
              % (mod, run["exit_code"], len(errors), len(sorries), len(warnings),
                 run["seconds"], run["peak_rss_gb"],
                 "  KILLED: %s" % run["killed"] if run["killed"] else ""))

    audit = None
    if not args.only and steps and all(s.get("compiled") for s in steps):
        log = logdir / "MathlibAudit.out"
        run = ct.run_guarded([str(lean), str(LEAN / "MathlibAudit.lean")], env, str(LEAN),
                             args.mem_gb, args.seconds, log)
        text = log.read_text(encoding="utf-8", errors="replace")
        errors = [ln for ln in text.splitlines() if ": error" in ln]
        passed = re.search(r"mathlib axiom audit passed: (\d+) theorems in (\d+) modules", text)
        audit = {"file": "lean/MathlibAudit.lean", **run, "passed": bool(
                     passed and run["exit_code"] == 0 and not errors and not run["killed"]),
                 "theorems": int(passed.group(1)) if passed else None,
                 "modules": int(passed.group(2)) if passed else None,
                 "per_module": dict((m.group(2), int(m.group(1))) for m in
                                    re.finditer(r"^\s+(\d+) in (Forge\.[\w.]+)", text, re.M)),
                 "first_errors": errors[:8]}
        print("MathlibAudit passed=%s theorems=%s" % (audit["passed"], audit["theorems"]))

    # The `Forge` root, which also imports the core-only design and closure
    # files (built by `lake build ForgeCore`).
    root = None
    if audit and audit["passed"]:
        log = logdir / "Forge.out"
        run = ct.run_guarded([str(lean), "-o", str(LIB / "Forge.olean"), str(LEAN / "Forge.lean")],
                             env, str(LEAN), args.mem_gb, args.seconds, log)
        text = log.read_text(encoding="utf-8", errors="replace")
        errors = [ln for ln in text.splitlines() if ": error" in ln]
        root = {"file": "lean/Forge.lean", **run,
                "compiled": run["exit_code"] == 0 and not errors and not run["killed"],
                "first_errors": errors[:8]}
        print("Forge root compiled=%s" % root["compiled"])

    leaked = {m["module"]: {n: a for n, a in m.get("axioms", {}).items()
                            if set(a) - {"propext", "Classical.choice", "Quot.sound"}}
              for m in steps}
    leaked = {k: v for k, v in leaked.items() if v}
    args.out.write_text(json.dumps({
        "what": ("Compilation of the Mathlib-dependent files under lean/Forge against the "
                 "Mathlib revision the lakefile pins, on the toolchain Forge pins."),
        "toolchain": toolchain,
        "mathlib": "lean/.lake/packages/mathlib (rev pinned in lean/lakefile.toml; prebuilt cache)",
        "compiled": sum(1 for s in steps if s.get("compiled")),
        "attempted": len(steps),
        "steps": steps,
        "axioms_beyond_propext_choice_quotsound": leaked,
        "axiom_audit": audit,
        "forge_root": root,
    }, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print("compiled %d of %d" % (sum(1 for s in steps if s.get("compiled")), len(steps)))
    ok = all(s.get("compiled") for s in steps) and not leaked
    return 0 if ok and (args.only or (audit and audit["passed"] and root and root["compiled"])) else 1


if __name__ == "__main__":
    raise SystemExit(main())
