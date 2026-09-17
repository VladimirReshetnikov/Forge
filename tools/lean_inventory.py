#!/usr/bin/env python3
"""The authoritative inventory of this repository's Lean files.

WHY THIS EXISTS. Three figures in this repository were wrong at various points
-- the file count, the count of files with a `sorry` token, and the count of
files that can be checked -- and every one of them was wrong because it had been
derived by hand and then copied forward. This script derives them, so the next
person quoting a number can regenerate it instead.

Two of the three errors are worth recording, because both were the same mistake:

  The `sorry` scan tested for a SUBSTRING and reported a defect on a file whose
  only occurrence of the token was its header sentence saying there were none.

  A sweep counted files reporting `does not depend on any axioms` without
  checking the exit code, and so counted a file that fails with ten errors and
  still prints a reassuring axiom line.

Both were a substring taken as a verdict. This script checks exit codes and
strips comments.

THE DEPENDENCY QUESTION IS TRANSITIVE. A file importing a sibling that is itself
Mathlib-free is Mathlib-free: `Forge/Checker/Cone.lean` imports
`Forge/Checker/Poly.lean` and nothing else. An earlier count split "imports
Mathlib directly" from "imports a sibling" and filed the second group with the
unchecked, which understated what is checkable. That matters, because "nothing
has ever checked these" is the sentence the whole Lean argument rests on and it
should be said about the right set.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from check_lean import strip_lean_comments  # noqa: E402

CORE_ROOTS = {"Lean", "Init", "Std"}
SORRY = re.compile(r"\bsorry\b|\bsorryAx\b")
IMPORT = re.compile(r"^import\s+(\S+)", re.M)
AXIOM_FREE = "does not depend on any axioms"


def collect(root: Path) -> list[Path]:
    """Source files only: `.lake/` holds build output and GENERATED files (the
    tactic head-to-head writes one there), which are not repository Lean."""
    return sorted(p for p in root.rglob("*.lean")
                  if ".git" not in p.parts and ".lake" not in p.parts)


def module_table(root: Path, files: list[Path]) -> dict[str, set[Path]]:
    """Every suffix of a path is a candidate module name, so sibling imports
    resolve regardless of which directory is the library root."""
    table: dict[str, set[Path]] = {}
    for f in files:
        parts = list(f.relative_to(root).parts)
        for i in range(len(parts)):
            name = ".".join(parts[i:])[: -len(".lean")]
            table.setdefault(name, set()).add(f)
    return table


def classify(files: list[Path], imports: dict[Path, list[str]],
             table: dict[str, set[Path]]) -> dict[Path, str]:
    """'mathlib', 'core', 'lakefile', or 'unresolved', computed transitively."""
    state: dict[Path, str] = {}

    def walk(f: Path, stack: tuple[Path, ...]) -> str:
        if f in state:
            return state[f]
        if f in stack:
            return "core"                      # an import cycle; stay neutral
        if f.name == "lakefile.lean":
            state[f] = "lakefile"
            return state[f]
        verdict = "core"
        for imp in imports[f]:
            head = imp.split(".")[0]
            if head == "Mathlib":
                verdict = "mathlib"
                break
            if head in CORE_ROOTS:
                continue
            targets = table.get(imp)
            if not targets:
                verdict = "unresolved"
                continue
            for t in targets:
                if walk(t, stack + (f,)) in ("mathlib", "unresolved"):
                    verdict = "mathlib" if walk(t, stack + (f,)) == "mathlib" \
                        else "unresolved"
                    break
            if verdict != "core":
                break
        state[f] = verdict
        return verdict

    for f in files:
        walk(f, ())
    return state


def elaborate(f: Path, lean_path: Path, timeout: int) -> dict:
    """Run `lean` on one file. The EXIT CODE is the verdict, never the output."""
    started = time.monotonic()
    try:
        proc = subprocess.run(
            ["lean", str(f)], capture_output=True, text=True, timeout=timeout,
            env={**__import__("os").environ, "LEAN_PATH": str(lean_path)},
            cwd=str(ROOT / "lean"))
    except subprocess.TimeoutExpired:
        return {"status": "timeout", "elapsed_seconds": round(time.monotonic() - started, 1)}
    out = (proc.stdout or "") + (proc.stderr or "")
    return {
        "status": "elaborated" if proc.returncode == 0 else "failed",
        "exit_code": proc.returncode,
        "elapsed_seconds": round(time.monotonic() - started, 1),
        # Recorded, but NEVER used as the verdict -- a failing file can print it.
        "prints_axiom_free_line": AXIOM_FREE in out,
        "first_error": next((ln for ln in out.splitlines() if "error" in ln), None),
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--elaborate", action="store_true",
                    help="also run `lean` on every Mathlib-free file (slow)")
    ap.add_argument("--timeout", type=int, default=600)
    ap.add_argument("--out", type=Path, default=ROOT / "results" / "lean-inventory.json")
    args = ap.parse_args()

    files = collect(ROOT)
    imports = {f: IMPORT.findall(f.read_text(encoding="utf-8", errors="replace"))
               for f in files}
    kinds = classify(files, imports, module_table(ROOT, files))

    entries = []
    for f in files:
        text = f.read_text(encoding="utf-8", errors="replace")
        code = strip_lean_comments(text)
        entry = {
            "file": f.relative_to(ROOT).as_posix(),
            "depends_on": kinds[f],
            "real_sorry": bool(SORRY.search(code)),
            "sorry_token_in_comments_only":
                not SORRY.search(code) and bool(SORRY.search(text)),
            "lines": text.count("\n") + 1,
        }
        if args.elaborate and kinds[f] == "core":
            entry.update(elaborate(f, ROOT / "lean" / ".lake" / "build" / "lib",
                                   args.timeout))
        entries.append(entry)

    free = [e for e in entries if e["depends_on"] == "core"]
    counts = {
        "files_total": len(entries),
        "mathlib_free": len(free),
        "mathlib_dependent": sum(1 for e in entries if e["depends_on"] == "mathlib"),
        "lakefiles": sum(1 for e in entries if e["depends_on"] == "lakefile"),
        "unresolved": sum(1 for e in entries if e["depends_on"] == "unresolved"),
        "real_sorry_or_sorryAx": sum(1 for e in entries if e["real_sorry"]),
        "sorry_token_in_comments_only":
            sum(1 for e in entries if e["sorry_token_in_comments_only"]),
    }
    if args.elaborate:
        counts["elaborated"] = sum(1 for e in free if e.get("status") == "elaborated")
        counts["failed"] = sum(1 for e in free if e.get("status") == "failed")
        counts["timed_out"] = sum(1 for e in free if e.get("status") == "timeout")
        counts["printing_axiom_free_line_but_failing"] = sum(
            1 for e in free
            if e.get("prints_axiom_free_line") and e.get("status") != "elaborated")

    args.out.write_text(json.dumps({
        "what": "Authoritative inventory of every .lean file in this repository.",
        "dependency_counting": (
            "TRANSITIVE. A file importing a sibling that is itself Mathlib-free "
            "is Mathlib-free."),
        "verdict_rule": (
            "Elaboration success is the process EXIT CODE. A file's output is "
            "never the verdict: r8's file fails with ten errors and still prints "
            "'does not depend on any axioms' on its last line."),
        "sorry_rule": (
            "Lean comments are stripped, with a depth counter because block "
            "comments nest, before a word-boundary search. A token appearing "
            "only in prose is recorded separately and is not a defect."),
        "elaboration_run": bool(args.elaborate),
        "counts": counts,
        "files": entries,
    }, indent=2) + "\n", encoding="utf-8")

    print("wrote %s" % args.out)
    for k, v in counts.items():
        print("  %-38s %s" % (k, v))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
