#!/usr/bin/env python3
"""Compile Lean sources and record the actual outcome.

This is a compilation harness, not a tactic benchmark. It records what the
Lean toolchain reported, including failure, and never invents a success.

Two modes:

  --mode elaborate   run `lean FILE` on each file individually. Works for
                     files that import nothing beyond Lean core.
  --mode lake        run `lake env lean FILE` inside a supplied project that
                     already has its dependencies built. Required for any
                     file that imports Mathlib.

Usage
-----
    python tools/check_lean.py --mode elaborate lean/Forge/Design
    python tools/check_lean.py --mode lake --project /path/to/mathlib-project lean

Output is JSON on stdout, and to --output if given.
"""

from __future__ import annotations

import argparse
import json
import platform
import shutil
import subprocess
import sys
import time
from pathlib import Path


def lean_version(executable: str) -> str | None:
    try:
        out = subprocess.run(
            [executable, "--version"], capture_output=True, text=True, timeout=120
        )
    except (OSError, subprocess.SubprocessError):
        return None
    return out.stdout.strip() or None


def collect(targets: list[str]) -> list[Path]:
    files: list[Path] = []
    for target in targets:
        path = Path(target)
        if path.is_dir():
            files.extend(sorted(path.rglob("*.lean")))
        elif path.suffix == ".lean":
            files.append(path)
        else:
            raise SystemExit(f"not a .lean file or directory: {target}")
    return files


def run_one(
    path: Path, mode: str, project: Path | None, timeout: float, axioms: bool
) -> dict:
    if mode == "lake":
        command = ["lake", "env", "lean", str(path.resolve())]
        cwd: Path | None = project
    else:
        command = ["lean", str(path.resolve())]
        cwd = None

    started = time.perf_counter()
    try:
        completed = subprocess.run(
            command, capture_output=True, text=True, timeout=timeout, cwd=cwd
        )
    except subprocess.TimeoutExpired:
        return {
            "file": str(path).replace("\\", "/"),
            "status": "timeout",
            "timeout_seconds": timeout,
            "elapsed_seconds": round(time.perf_counter() - started, 3),
        }
    except OSError as exc:
        return {
            "file": str(path).replace("\\", "/"),
            "status": "tool_missing",
            "detail": str(exc),
        }

    elapsed = round(time.perf_counter() - started, 3)
    record = {
        "file": str(path).replace("\\", "/"),
        "status": "elaborated" if completed.returncode == 0 else "failed",
        "exit_code": completed.returncode,
        "elapsed_seconds": elapsed,
    }
    if completed.stdout.strip():
        record["stdout"] = completed.stdout.strip()[:8000]
    if completed.stderr.strip():
        record["stderr"] = completed.stderr.strip()[:8000]

    # `lean` exits 0 on a file whose declarations are admitted, so an
    # explicit sorry scan is part of the verdict rather than a nicety.
    text = path.read_text(encoding="utf-8", errors="replace")
    if "sorry" in text or "sorryAx" in text:
        record["contains_sorry_token"] = True
        record["status"] = "elaborated_with_sorry"

    if axioms and record["status"] == "elaborated":
        record["axiom_audit"] = "not_performed"
    return record


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("targets", nargs="+", help=".lean files or directories")
    parser.add_argument("--mode", choices=("elaborate", "lake"), default="elaborate")
    parser.add_argument("--project", type=Path, default=None)
    parser.add_argument("--timeout", type=float, default=900.0)
    parser.add_argument("--output", type=Path, default=None)
    parser.add_argument("--axioms", action="store_true")
    args = parser.parse_args()

    if args.mode == "lake" and args.project is None:
        parser.error("--mode lake requires --project")

    executable = "lake" if args.mode == "lake" else "lean"
    if shutil.which(executable) is None:
        report = {
            "status": "NOT_RUN",
            "reason": f"{executable} executable not found on PATH",
            "files": [],
        }
        print(json.dumps(report, indent=2))
        if args.output:
            args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        return 0

    files = collect(args.targets)
    records = [
        run_one(path, args.mode, args.project, args.timeout, args.axioms)
        for path in files
    ]

    counts: dict[str, int] = {}
    for record in records:
        counts[record["status"]] = counts.get(record["status"], 0) + 1

    report = {
        "status": "RUN",
        "mode": args.mode,
        "lean_version": lean_version("lean"),
        "lake_version": lean_version("lake") if args.mode == "lake" else None,
        "platform": platform.platform(),
        "project": str(args.project) if args.project else None,
        "counts": counts,
        "files": records,
        "note": (
            "Successful elaboration is not a full transitive-axiom audit and "
            "is not a comparison against any Lean tactic."
        ),
    }

    text = json.dumps(report, indent=2)
    print(text)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text + "\n", encoding="utf-8")

    return 0 if counts.get("failed", 0) == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
