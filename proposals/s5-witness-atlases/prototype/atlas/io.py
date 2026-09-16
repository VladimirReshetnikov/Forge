"""Strict JSON loading: duplicate keys and nonfinite values are rejected."""
import json
from pathlib import Path


def _object(pairs):
    result={}
    for k,v in pairs:
        if k in result:
            raise ValueError('duplicate JSON key: '+k)
        result[k]=v
    return result


def load(path):
    data=Path(path).read_text(encoding='utf-8')
    if len(data)>50_000_000:
        raise ValueError('input file size limit')
    return json.loads(data,object_pairs_hook=_object,
        parse_constant=lambda value: (_ for _ in ()).throw(ValueError('nonfinite JSON number')))
