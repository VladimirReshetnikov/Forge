"""Usage: python -S -m forge_closure.verify ../results/certificates"""
import argparse
import json
from pathlib import Path
from .checker import verify, Invalid


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("paths", nargs="+")
    args = ap.parse_args()
    failed = 0
    paths = []
    for name in args.paths:
        p = Path(name)
        paths.extend(sorted(p.glob("*.json")) if p.is_dir() else [p])
    if not paths:
        ap.error("no certificate files found")
    for path in paths:
        try:
            if path.stat().st_size > 8_000_000:
                raise Invalid("input file byte ceiling")
            bundle = json.loads(path.read_text())
            verify(bundle["problem"], bundle["certificate"])
            print(f"PASS {path.name}")
        except (OSError, ValueError, KeyError) as e:
            failed += 1
            print(f"FAIL {path.name}: {e}")
    raise SystemExit(bool(failed))

if __name__ == "__main__":
    main()
