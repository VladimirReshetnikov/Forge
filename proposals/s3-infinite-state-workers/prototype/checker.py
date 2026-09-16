"""Search-independent certificate checking. No imports of producer modules.

This is an executable research checker, not a Lean theorem. Its nominal replay
uses equality matrices rather than the producer's canonicalizer. Vector
predecessors are expressed independently as max(a, a+b-z). Its concrete
interpreters are also separately implemented. Input models are supplied by the
caller, never selected by certificates. See docs/STATUS.md for the trust boundary.
"""
from __future__ import annotations
import json
from typing import Any

class Invalid(ValueError):
    pass

def require(condition: bool, message: str = 'invalid input') -> None:
    if not condition:
        raise Invalid(message)

def natural(x: Any) -> bool:
    return type(x) is int and x >= 0

def vector(v: Any, size: int) -> bool:
    return isinstance(v, (list, tuple)) and len(v) == size and all(natural(x) for x in v)

def validate_families(families: Any, controls: int, dimension: int) -> None:
    require(isinstance(families, list) and bool(families), 'missing initial family')
    for f in families:
        require(type(f) is dict and natural(f.get('control')) and f['control'] < controls)
        require(vector(f.get('base'), dimension))
        require(isinstance(f.get('rays'), list))
        require(all(vector(ray, dimension) for ray in f['rays']))

def validate_vass(p: dict) -> None:
    require(type(p) is dict)
    require(natural(p.get('dimension')) and p['dimension'] > 0)
    require(natural(p.get('controls')) and p['controls'] > 0)
    d, q = p['dimension'], p['controls']
    require(isinstance(p.get('transitions'), list) and isinstance(p.get('bad'), list))
    for e in p['transitions']:
        require(type(e) is dict and natural(e.get('src')) and e['src'] < q)
        require(natural(e.get('dst')) and e['dst'] < q)
        require(vector(e.get('consume'), d) and vector(e.get('produce'), d))
    for b in p['bad']:
        require(type(b) is dict and natural(b.get('control')) and b['control'] < q)
        require(vector(b.get('vector'), d))
    validate_families(p.get('initials'), q, d)

def validate_selector(e: Any, k: int, c: int, allow_input: bool = True) -> None:
    require(isinstance(e, list) and len(e) in (1, 2))
    op = e[0]
    if op in ('input', 'null'):
        require(len(e) == 1 and (op != 'input' or allow_input))
    elif op in ('reg', 'const'):
        require(len(e) == 2 and natural(e[1]) and e[1] < (k if op == 'reg' else c))
    else:
        raise Invalid('unsupported atom operation')

def validate_guard(e: Any, k: int, c: int, depth: int = 0, allow_input: bool = True) -> None:
    require(depth < 128, 'guard depth limit')
    if type(e) is bool:
        return
    require(isinstance(e, list) and bool(e))
    if e[0] == 'eq':
        require(len(e) == 3)
        validate_selector(e[1], k, c, allow_input)
        validate_selector(e[2], k, c, allow_input)
    elif e[0] == 'not':
        require(len(e) == 2)
        validate_guard(e[1], k, c, depth + 1, allow_input)
    elif e[0] in ('and', 'or'):
        require(len(e) >= 2)
        for child in e[1:]:
            validate_guard(child, k, c, depth + 1, allow_input)
    else:
        raise Invalid('unsupported guard')

def validate_register_header(m: dict) -> None:
    require(type(m) is dict)
    for key in ('registers', 'constants', 'controls', 'initial_control'):
        require(natural(m.get(key)))
    require(m['controls'] > 0 and m['initial_control'] < m['controls'])
    require(isinstance(m.get('tags'), list) and bool(m['tags']))
    require(all(type(t) is str and bool(t) for t in m['tags']))
    require(len(set(m['tags'])) == len(m['tags']))
    require(isinstance(m.get('initial_registers'), list) and
            len(m['initial_registers']) == m['registers'])
    require(all(v is None or (natural(v) and v < m['constants']) for v in m['initial_registers']))
    require(isinstance(m.get('rules'), list))

def validate_rule(r: dict, m: dict) -> None:
    require(type(r) is dict)
    require(natural(r.get('src')) and r['src'] < m['controls'])
    require(natural(r.get('dst')) and r['dst'] < m['controls'])
    require(r.get('tag') in m['tags'])
    validate_guard(r.get('guard'), m['registers'], m['constants'])
    require(isinstance(r.get('update'), list) and len(r['update']) == m['registers'])
    for e in r['update']:
        validate_selector(e, m['registers'], m['constants'])

def validate_machine(m: dict) -> None:
    validate_register_header(m)
    for r in m['rules']:
        validate_rule(r, m)
        o = r.get('output')
        require(isinstance(o, list) and len(o) == 2 and o[0] in ('bool', 'atom'))
        if o[0] == 'bool':
            validate_guard(o[1], m['registers'], m['constants'])
        else:
            validate_selector(o[1], m['registers'], m['constants'])
    for q in range(m['controls']):
        for tag in m['tags']:
            require(any(r['src'] == q and r['tag'] == tag and r['guard'] is True
                        for r in m['rules']), 'each ordered rule cell needs a default')

def validate_register_net(m: dict) -> None:
    validate_register_header(m)
    require(natural(m.get('dimension')) and m['dimension'] > 0)
    for r in m['rules']:
        validate_rule(r, m)
        require(vector(r.get('consume'), m['dimension']) and vector(r.get('produce'), m['dimension']))
    require(isinstance(m.get('bad'), list))
    for bad in m['bad']:
        require(type(bad) is dict)
        require(natural(bad.get('control')) and bad['control'] < m['controls'])
        require(vector(bad.get('vector'), m['dimension']))
        validate_guard(bad.get('guard'), m['registers'], m['constants'], allow_input=False)
    validate_families(m.get('initials'), m['controls'], m['dimension'])
    require(all(f['control'] == m['initial_control'] for f in m['initials']))

# The checker deliberately does not call antichain.predecessor or initial_witness.
def dominates_marking(marking: list | tuple, lower_bound: list | tuple) -> bool:
    return all(marking[i] >= lower_bound[i] for i in range(len(marking)))

def covered(basis: list, marking: list | tuple) -> bool:
    return any(dominates_marking(marking, entry) for entry in basis)

def separated(family: dict, basis: list) -> bool:
    for entry in basis:
        obstructed = False
        for i in range(len(entry)):
            fixed = all(ray[i] == 0 for ray in family['rays'])
            if fixed and family['base'][i] < entry[i]:
                obstructed = True
                break
        if not obstructed:
            return False
    return True

def valid_bases(bases: Any, n: int, d: int) -> bool:
    return (isinstance(bases, list) and len(bases) == n and
            all(isinstance(b, list) and all(vector(v, d) for v in b) for b in bases))

def closed_edge(source_basis: list, target_basis: list, consume: list, produce: list) -> bool:
    for target in target_basis:
        minimal = [max(consume[i], consume[i] + target[i] - produce[i])
                   for i in range(len(consume))]
        if not covered(source_basis, minimal):
            return False
    return True

def instantiate_family(f: dict, params: Any) -> list:
    require(vector(params, len(f['rays'])), 'bad parameter assignment')
    result = list(f['base'])
    for j in range(len(params)):
        for i in range(len(result)):
            result[i] += params[j] * f['rays'][j][i]
    return result

def apply_counter_rule(r: dict, counters: list) -> list:
    require(dominates_marking(counters, r['consume']), 'disabled transition in witness')
    return [counters[i] - r['consume'][i] + r['produce'][i] for i in range(len(counters))]

def check_vass(p: dict, cert: dict) -> bool:
    try:
        validate_vass(p)
        require(type(cert) is dict and cert.get('schema') == 1 and type(cert['schema']) is int)
        if cert.get('kind') == 'safe':
            bases = cert.get('basis')
            require(valid_bases(bases, p['controls'], p['dimension']))
            require(all(covered(bases[b['control']], b['vector']) for b in p['bad']))
            require(all(closed_edge(bases[e['src']], bases[e['dst']], e['consume'], e['produce'])
                        for e in p['transitions']))
            require(all(separated(f, bases[f['control']]) for f in p['initials']))
            return True
        if cert.get('kind') == 'unsafe':
            fi = cert.get('initial')
            require(natural(fi) and fi < len(p['initials']))
            family = p['initials'][fi]
            q, counters = family['control'], instantiate_family(family, cert.get('parameters'))
            require(isinstance(cert.get('transitions'), list))
            for eid in cert['transitions']:
                require(natural(eid) and eid < len(p['transitions']))
                edge = p['transitions'][eid]
                require(edge['src'] == q, 'wrong source control')
                counters = apply_counter_rule(edge, counters)
                q = edge['dst']
            return any(b['control'] == q and dominates_marking(counters, b['vector']) for b in p['bad'])
        return False
    except (Invalid, KeyError, TypeError, IndexError, AttributeError, RecursionError):
        return False

# Independent interpreter: environments are explicit selector-name dictionaries.
def eval_selector(e: list, values: tuple, inp: int) -> Any:
    if len(e) == 1:
        return inp if e[0] == 'input' else None
    return values[e[1]] if e[0] == 'reg' else e[1]

def eval_condition(e: Any, values: tuple, inp: int) -> bool:
    if isinstance(e, bool):
        return e
    tag, *args = e
    if tag == 'eq':
        return eval_selector(args[0], values, inp) == eval_selector(args[1], values, inp)
    if tag == 'not':
        return not eval_condition(args[0], values, inp)
    evaluated = [eval_condition(v, values, inp) for v in args]
    return all(evaluated) if tag == 'and' else any(evaluated)

def execute(m: dict, state: tuple, input_tag: str, inp: int) -> tuple:
    control, values = state
    choices = [r for r in m['rules'] if r['src'] == control and r['tag'] == input_tag]
    chosen = next(r for r in choices if eval_condition(r['guard'], values, inp))
    typ, out = chosen['output']
    result = eval_condition(out, values, inp) if typ == 'bool' else eval_selector(out, values, inp)
    return (typ, result), (chosen['dst'], tuple(eval_selector(e, values, inp) for e in chosen['update']))

def equality_signature(values: tuple, constants: int) -> tuple:
    # Null and every fixed constant are anchored; all other atom identities vanish.
    anchored = (None,) + tuple(range(constants)) + values
    return tuple(anchored[i] == anchored[j] for i in range(len(anchored)) for j in range(i))

def checker_inputs(values: tuple, constants: int) -> list[int]:
    names = list(range(constants))
    for value in values:
        if value is not None and value not in names:
            names.append(value)
    # A different choice from the producer's least-unused construction.
    names.append(max(names, default=constants - 1) + 1)
    return names

def valid_register_values(values: Any, k: int) -> bool:
    return isinstance(values, (tuple, list)) and len(values) == k and all(v is None or natural(v) for v in values)

def check_nominal(left: dict, right: dict, cert: dict) -> bool:
    try:
        validate_machine(left); validate_machine(right)
        require(left['constants'] == right['constants'] and left['tags'] == right['tags'])
        require(type(cert) is dict and type(cert.get('schema')) is int and cert['schema'] == 1)
        c, ka, kb = left['constants'], left['registers'], right['registers']
        sa = (left['initial_control'], tuple(left['initial_registers']))
        sb = (right['initial_control'], tuple(right['initial_registers']))
        if cert.get('kind') == 'different':
            require(isinstance(cert.get('word'), list))
            differed = False
            for item in cert['word']:
                require(isinstance(item, list) and len(item) == 2 and item[0] in left['tags'] and natural(item[1]))
                oa, sa = execute(left, sa, *item)
                ob, sb = execute(right, sb, *item)
                differed = differed or oa != ob
            return differed
        if cert.get('kind') != 'equivalent':
            return False
        require(isinstance(cert.get('states'), list) and bool(cert['states']))
        index = set()
        for item in cert['states']:
            require(isinstance(item, list) and len(item) == 3)
            qa, qb, values = item
            require(natural(qa) and qa < left['controls'] and natural(qb) and qb < right['controls'])
            require(valid_register_values(values, ka + kb))
            sig = (qa, qb, equality_signature(tuple(values), c))
            require(sig not in index, 'duplicate orbit')
            index.add(sig)
        require((sa[0], sb[0], equality_signature(sa[1] + sb[1], c)) in index)
        for qa, qb, values in cert['states']:
            va, vb = tuple(values[:ka]), tuple(values[ka:])
            for tag in left['tags']:
                for atom in checker_inputs(tuple(values), c):
                    oa, na = execute(left, (qa, va), tag, atom)
                    ob, nb = execute(right, (qb, vb), tag, atom)
                    require(oa == ob, 'output disagreement')
                    sig = (na[0], nb[0], equality_signature(na[1] + nb[1], c))
                    require(sig in index, 'orbit not closed')
        return True
    except (Invalid, KeyError, TypeError, IndexError, AttributeError, StopIteration, RecursionError):
        return False

def check_mixed(m: dict, cert: dict) -> bool:
    """Replay directly from the supplied register-net semantics, not compiled edges."""
    try:
        validate_register_net(m)
        require(type(cert) is dict and type(cert.get('schema')) is int and cert['schema'] == 1)
        c, k, d = m['constants'], m['registers'], m['dimension']
        if cert.get('kind') == 'unsafe':
            fi = cert.get('initial')
            require(natural(fi) and fi < len(m['initials']))
            counters = instantiate_family(m['initials'][fi], cert.get('parameters'))
            q, values = m['initial_control'], tuple(m['initial_registers'])
            require(isinstance(cert.get('steps'), list))
            for item in cert['steps']:
                require(isinstance(item, list) and len(item) == 3)
                rid, tag, atom = item
                require(natural(rid) and rid < len(m['rules']) and natural(atom))
                rule = m['rules'][rid]
                require(rule['src'] == q and tag == rule['tag'])
                require(eval_condition(rule['guard'], values, atom))
                counters = apply_counter_rule(rule, counters)
                values = tuple(eval_selector(e, values, atom) for e in rule['update'])
                q = rule['dst']
            return any(b['control'] == q and eval_condition(b['guard'], values, 0)
                       and dominates_marking(counters, b['vector']) for b in m['bad'])
        if cert.get('kind') != 'safe':
            return False
        states, bases = cert.get('states'), cert.get('basis')
        require(isinstance(states, list) and bool(states))
        require(valid_bases(bases, len(states), d))
        indices = {}
        for i, state in enumerate(states):
            require(isinstance(state, list) and len(state) == 2)
            q, values = state
            require(natural(q) and q < m['controls'] and valid_register_values(values, k))
            key = (q, equality_signature(tuple(values), c))
            require(key not in indices)
            indices[key] = i
        initial_key = (m['initial_control'], equality_signature(tuple(m['initial_registers']), c))
        require(initial_key in indices)
        require(all(separated(f, bases[indices[initial_key]]) for f in m['initials']))
        for i, (q, values0) in enumerate(states):
            values = tuple(values0)
            for bad in m['bad']:
                if bad['control'] == q and eval_condition(bad['guard'], values, 0):
                    require(covered(bases[i], bad['vector']))
            for rule in m['rules']:
                if rule['src'] != q:
                    continue
                for atom in checker_inputs(values, c):
                    if not eval_condition(rule['guard'], values, atom):
                        continue
                    successor = tuple(eval_selector(e, values, atom) for e in rule['update'])
                    key = (rule['dst'], equality_signature(successor, c))
                    require(key in indices, 'register quotient is incomplete')
                    require(closed_edge(bases[i], bases[indices[key]], rule['consume'], rule['produce']))
        return True
    except (Invalid, KeyError, TypeError, IndexError, AttributeError, RecursionError):
        return False


def load_json(text: str, max_bytes: int = 16_000_000) -> Any:
    require(len(text.encode('utf-8')) <= max_bytes, 'byte limit')
    def unique(pairs: list[tuple]) -> dict:
        result = {}
        for key, value in pairs:
            require(key not in result, 'duplicate JSON key')
            result[key] = value
        return result
    return json.loads(text, object_pairs_hook=unique,
                      parse_constant=lambda v: (_ for _ in ()).throw(Invalid('nonfinite number')))
