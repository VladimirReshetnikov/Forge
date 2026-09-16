#!/usr/bin/env python3
"""Replay JSONL certificates with only Python's standard library.

Usage: python -S prototype/replay.py results/frontiers.jsonl [more files...]
No search code is imported. Exit 2 is a resource refusal, not invalid mathematics.
"""
from __future__ import annotations
import argparse
from collections import Counter
from pathlib import Path
import json
import sys
from forge_resources.checker import (check_record, load_json, InvalidCertificate,
                                     ResourceLimit, DEFAULT_LIMITS)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("files", type=Path, nargs="+")
    args = parser.parse_args()
    counts: Counter[str] = Counter()
    try:
        for path in args.files:
            if path.stat().st_size > DEFAULT_LIMITS.file_bytes:
                raise ResourceLimit(f"file byte limit: {path}")
            for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
                if not line.strip():
                    continue
                record = load_json(line)
                try:
                    result = check_record(record)
                except (InvalidCertificate, ResourceLimit) as error:
                    raise type(error)(f"{path}:{line_no}: {error}") from error
                counts[result["meaning"]] += 1
        print(json.dumps({"status": "PYTHON_CHECKED", "records": sum(counts.values()),
                          "by_kind": dict(counts), "search_imported": any(
                              x.endswith(("producer", "model")) and "forge_resources" in x
                              for x in sys.modules)}, indent=2))
        return 0
    except ResourceLimit as error:
        print(json.dumps({"status": "UNKNOWN_RESOURCE_LIMIT", "error": str(error)}))
        return 2
    except (InvalidCertificate, OSError, ValueError, TypeError) as error:
        print(json.dumps({"status": "INVALID_OR_UNREADABLE", "error": str(error)}))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
