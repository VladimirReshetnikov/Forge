#!/usr/bin/env python3
"""Replay without importing the producer. Run using python -S verify_corpus.py."""
from __future__ import annotations
from pathlib import Path
from collections import Counter
import argparse
import json
import sys
if not __debug__:
    raise RuntimeError("Regression and replay scripts require assertions enabled; do not use -O")
from forge_symmetry.checker import (load_json, verify_chain, verify_canonical,
    verify_canonical_family, verify_burnside, verify_family)


def replay(directory: Path) -> dict:
    manifest=load_json(directory/'corpus_manifest.json')
    if type(manifest) is not list or not all(type(x) is str for x in manifest) or len(set(manifest)) != len(manifest):
        raise ValueError('malformed or duplicate corpus manifest')
    expected={name+'.json' for name in manifest}
    actual={p.name for p in (directory/'corpus').glob('*.json')}
    if actual!=expected or not expected:
        raise ValueError('corpus manifest mismatch or empty corpus')
    counts=Counter()
    for name in sorted(expected):
        b=load_json(directory/'corpus'/name)
        if b['name']+'.json' != name:
            raise ValueError('bundle identity differs from manifest')
        c=verify_chain(b['problem'],b['chain']);counts['chain_bundles']+=1
        for p,expected_member in b['membership']:
            assert c.contains(p)==expected_member
            counts['membership_queries']+=1
        for entry in b['canonical']:
            result=verify_canonical(c,entry['colors'],entry['certificate'])
            assert result['best']==entry['expected'];counts['canonical_images']+=1
        for entry in b['canonical_family']:
            result=verify_canonical_family(c,entry['colors'],entry['certificate'])
            assert result['best']==entry['expected'];counts['canonical_family_images']+=1
        family=verify_family(c,b['family']) if 'family' in b else None
        if family:counts['recognized_families']+=1
        if 'burnside' in b:
            inventory=verify_burnside(c,b['burnside']);counts['cycle_inventories']+=1
            for q,value in b['color_counts']:
                assert inventory.count_colors(q)==value
                if family:assert family.count_colors(q)==value
                counts['color_count_queries']+=1
            for weight,value in b['binary_counts']:
                assert inventory.count_binary_weight(weight)==value
                counts['fixed_weight_queries']+=1
        for q,value in b.get('family_counts',[]):
            assert family is not None and family.count_colors(q)==value
            counts['large_family_count_queries']+=1
    assert 'forge_symmetry.producer' not in sys.modules
    return {'status':'REPLAY_PASSED','site_packages_disabled':bool(sys.flags.no_site),
            'producer_imported':False,'counts':dict(sorted(counts.items()))}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('directory',type=Path);args=p.parse_args()
    print(json.dumps(replay(args.directory),indent=2))
