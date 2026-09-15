#!/usr/bin/env python3
"""Replay stored certificates using the Python standard library ONLY.

Run it with site packages disabled, which is how it is meant to be used:

    python -S bin/verify.py

Nothing reachable from here imports NumPy, SciPy, SymPy or any search engine --
the search half lives in bin/generate.py. Every record is decoded through the
bounded decoders in forge/io/decode.py, then re-checked; in addition, each
record is MUTATED and the mutation must be rejected, and a bundle missing a
required certificate family is a hard failure rather than a vacuous success.

This is exact Python checking. It is NOT Lean kernel checking, and none of the
emitted Lean sources are compiled by this program.
"""
from __future__ import annotations
import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from forge.io import decode  # noqa: E402

FORBIDDEN = ('numpy', 'scipy', 'sympy')


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('path', nargs='?', type=Path,
                    default=ROOT / 'results' / 'certificates.json')
    args = ap.parse_args()
    if not args.path.exists():
        print('no certificate bundle at %s; run `python bin/generate.py` first'
              % args.path, file=sys.stderr)
        return 2
    if args.path.stat().st_size > 20_000_000:
        print('file size limit exceeded', file=sys.stderr)
        return 2
    try:
        records = decode.loads(args.path.read_text(encoding='utf-8'))
        summary = decode.verify_bundle(records)
    except decode.DecodeError as exc:
        print('REJECTED: %s' % exc, file=sys.stderr)
        return 1
    leaked = sorted(m for m in FORBIDDEN if m in sys.modules)
    if leaked:
        print('REJECTED: replay path imported %s' % ', '.join(leaked), file=sys.stderr)
        return 1
    print('%d/%d certificates rechecked successfully (exact Python, NOT Lean).'
          % (summary['records'], summary['records']))
    print('%d mutated certificates were rejected as required.'
          % summary['mutations_rejected'])
    for family in sorted(summary['families']):
        print('  %-34s %d' % (family, summary['families'][family]))
    print('verification dependencies: Python standard library only'
          ' (site packages %s).' % ('disabled' if sys.flags.no_site else 'enabled'))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
