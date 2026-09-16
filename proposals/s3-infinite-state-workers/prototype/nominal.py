"""Exact equivalence of deterministic equality-register Mealy machines.

The input alphabet is Tags x Atoms. Atoms are observed only by equality; registers
can copy input, fixed constants, old registers or None. Outputs are Boolean or
optional atoms. Register updates are simultaneous. 'None' is not an input atom.
Search uses a joint canonical form; checker.py uses pairwise equality signatures.
"""
from __future__ import annotations
from collections import deque
from typing import Any


def select(expr: list, registers: tuple, atom: int) -> Any:
    op = expr[0]
    if op == 'input': return atom
    if op == 'reg': return registers[expr[1]]
    if op == 'const': return expr[1]
    if op == 'null': return None
    raise ValueError(f'bad selector: {op}')


def guard(expr: Any, registers: tuple, atom: int) -> bool:
    if type(expr) is bool: return expr
    op = expr[0]
    if op == 'eq': return select(expr[1], registers, atom) == select(expr[2], registers, atom)
    if op == 'not': return not guard(expr[1], registers, atom)
    if op == 'and': return all(guard(x, registers, atom) for x in expr[1:])
    if op == 'or': return any(guard(x, registers, atom) for x in expr[1:])
    raise ValueError(f'bad guard: {op}')


def transition(machine: dict, state: tuple, tag: str, atom: int) -> tuple:
    q, registers = state
    for rule in machine['rules']:
        if rule['src'] == q and rule['tag'] == tag and guard(rule['guard'], registers, atom):
            typ, expression = rule['output']
            value = guard(expression, registers, atom) if typ == 'bool' else select(expression, registers, atom)
            out = (typ, value)
            nxt = (rule['dst'], tuple(select(e, registers, atom) for e in rule['update']))
            return out, nxt
    raise ValueError('machine is not total')


def canonical(values: tuple, constants: int) -> tuple:
    names: dict[int, int] = {i: i for i in range(constants)}
    nxt = constants
    result = []
    for value in values:
        if value is None:
            result.append(None)
        else:
            if value not in names:
                names[value] = nxt
                nxt += 1
            result.append(names[value])
    return tuple(result)


def representatives(values: tuple, constants: int) -> list[int]:
    live = sorted(set(range(constants)) | {v for v in values if v is not None})
    fresh = constants
    while fresh in live:
        fresh += 1
    return live + [fresh]


def pair_state(sa: tuple, sb: tuple, constants: int) -> tuple:
    return (sa[0], sb[0], canonical(sa[1] + sb[1], constants))


def split_state(state: tuple, left_regs: int) -> tuple:
    qa, qb, registers = state
    return (qa, registers[:left_regs]), (qb, registers[left_regs:])


def realize_atom(representative: int, canon_regs: tuple, real_regs: tuple, constants: int) -> int:
    if representative < constants:
        return representative
    for i, v in enumerate(canon_regs):
        if v == representative:
            assert real_regs[i] is not None
            return real_regs[i]
    used = set(range(constants)) | {v for v in real_regs if v is not None}
    candidate = constants
    while candidate in used:
        candidate += 1
    return candidate


def equivalence(left: dict, right: dict, *, max_states: int = 10000) -> dict:
    if left['constants'] != right['constants'] or left['tags'] != right['tags']:
        raise ValueError('incompatible alphabets')
    c, k = left['constants'], left['registers']
    sa0 = (left['initial_control'], tuple(left['initial_registers']))
    sb0 = (right['initial_control'], tuple(right['initial_registers']))
    root = pair_state(sa0, sb0, c)
    todo = deque([root])
    parents: dict[tuple, tuple | None] = {root: None}
    transitions_checked = 0

    def witness(state: tuple, tag: str, atom: int) -> list:
        abstract = [(state, tag, atom)]
        while parents[state] is not None:
            prev, prev_tag, prev_atom = parents[state]
            abstract.append((prev, prev_tag, prev_atom))
            state = prev
        abstract.reverse()
        actual_left, actual_right = sa0, sb0
        result = []
        for src, t, representative in abstract:
            real = actual_left[1] + actual_right[1]
            a = realize_atom(representative, src[2], real, c)
            result.append([t, a])
            _, actual_left = transition(left, actual_left, t, a)
            _, actual_right = transition(right, actual_right, t, a)
        return result

    while todo:
        if len(parents) > max_states:
            return {'schema': 1, 'kind': 'unknown', 'reason': 'budget', 'states': len(parents)}
        state = todo.popleft()
        sa, sb = split_state(state, k)
        for tag in left['tags']:
            for atom in representatives(state[2], c):
                transitions_checked += 1
                oa, na = transition(left, sa, tag, atom)
                ob, nb = transition(right, sb, tag, atom)
                if oa != ob:
                    return {'schema': 1, 'kind': 'different', 'word': witness(state, tag, atom),
                            'stats': {'orbits': len(parents), 'edges': transitions_checked}}
                nxt = pair_state(na, nb, c)
                if nxt not in parents:
                    parents[nxt] = (state, tag, atom)
                    todo.append(nxt)
    return {'schema': 1, 'kind': 'equivalent',
            'states': [[qa, qb, list(rs)] for qa, qb, rs in parents],
            'stats': {'orbits': len(parents), 'edges': transitions_checked}}
