"""Replay the stored corpus in a fresh process, without importing the producer."""
from __future__ import annotations
import argparse
import json
import sys
from pathlib import Path
from checker import verify, check_witness, require


def replay(directory: Path) -> dict:
    paths = sorted((directory / 'certificates').glob('*.json'))
    require(bool(paths), 'no certificates found')
    checked: dict[str, dict] = {}
    for path in paths:
        query = json.loads((directory / 'queries' / path.name).read_text())
        certificate = json.loads(path.read_text())
        verify(certificate, query)
        checked[path.stem] = certificate
    witnesses = json.loads((directory / 'witnesses.json').read_text())
    for item in witnesses:
        certificate = checked[item['source']]
        dfa = certificate['nodes'][certificate['root']]['dfa']
        check_witness(dfa, item['record']['inputs'], item['record'])
    require('producer' not in sys.modules and 'formula' not in sys.modules,
            'search modules were imported during replay')
    return {'status': 'accepted', 'certificates': len(checked),
            'concrete_witnesses': len(witnesses),
            'producer_imported': False, 'formula_module_imported': False,
            'site_disabled': bool(sys.flags.no_site),
            'scope': 'Python replay, not Lean verification'}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    parser.add_argument('--receipt', type=Path)
    args = parser.parse_args()
    result = replay(args.directory)
    text = json.dumps(result, indent=2) + '\n'
    if args.receipt:
        args.receipt.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
