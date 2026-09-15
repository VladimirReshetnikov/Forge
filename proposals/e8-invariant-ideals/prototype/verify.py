"""Search-free replay of stored certificates. Usage: python -S verify.py [FILE]."""
import json
from pathlib import Path
import sys
import invariant_space as inv
import ideal_space as ideal
import exact as ex
import finite_cover as fc
import presburger as pb


def reject_duplicates(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError('duplicate JSON key: '+key)
        result[key] = value
    return result


def main():
    path = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).resolve().parent.parent/'results/certificates.json'
    if path.stat().st_size > 64*1024*1024:
        raise ValueError('certificate archive exceeds 64 MiB replay limit')
    data = json.loads(path.read_text(), object_pairs_hook=reject_duplicates,
                      parse_constant=lambda x: (_ for _ in ()).throw(ValueError(x)))
    counts = {'invariant': 0, 'ideal': 0, 'finite': 0, 'integer': 0}
    checkers = {'invariant': inv.check, 'ideal': ideal.check, 'finite': fc.check, 'integer': pb.check}
    def forbidden(*args, **kwargs):
        raise RuntimeError('search routine called during replay')
    for module, names in [(inv, ['synthesize', 'nullspace', 'coordinates', 'poly_basis']),
                          (ideal, ['synthesize']), (fc, ['synthesize']),
                          (pb, ['synthesize', 'bezout']),
                          (ex, ['rref', 'nullspace', 'coordinates', 'poly_basis'])]:
        for name in names:
            setattr(module, name, forbidden)
    for entry in data:
        lane = entry['lane']
        if not checkers[lane](entry['problem'], entry['certificate']):
            raise ValueError('rejected '+entry['name'])
        counts[lane] += 1
    print(json.dumps({'status': 'accepted by Python checkers', 'counts': counts,
                      'lean_proofs': False}, indent=2))


if __name__ == '__main__':
    main()
