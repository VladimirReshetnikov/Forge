"""Composition: equality-register control plus unbounded monotone counters."""
from __future__ import annotations
from collections import deque
import antichain
import nominal


def compile_quotient(model: dict, max_states: int = 10000) -> tuple:
    """Build structural orbits, deliberately ignoring counter enabling for discovery.

    Edges retain the original rule and input orbit for witness lifting. Every
    discovered edge still has its exact consume/produce vectors in the VASS.
    """
    c = model['constants']
    root = (model['initial_control'], tuple(model['initial_registers']))
    states = [root]
    index = {root: 0}
    todo = deque([root])
    transitions, labels = [], []
    while todo:
        if len(states) > max_states:
            raise OverflowError('orbit budget')
        state = todo.popleft()
        q, registers = state
        for rid, rule in enumerate(model['rules']):
            if rule['src'] != q:
                continue
            for atom in nominal.representatives(registers, c):
                if not nominal.guard(rule['guard'], registers, atom):
                    continue
                updated = tuple(nominal.select(e, registers, atom) for e in rule['update'])
                nxt = (rule['dst'], nominal.canonical(updated, c))
                if nxt not in index:
                    index[nxt] = len(states)
                    states.append(nxt)
                    todo.append(nxt)
                transitions.append({'src': index[state], 'dst': index[nxt],
                                    'consume': rule['consume'], 'produce': rule['produce']})
                labels.append((rid, rule['tag'], atom))
    bad = []
    for i, (q, regs) in enumerate(states):
        for b in model['bad']:
            if b['control'] == q and nominal.guard(b['guard'], regs, 0):
                bad.append({'control': i, 'vector': b['vector']})
    initials = [{'control': 0, 'base': f['base'], 'rays': f['rays']} for f in model['initials']]
    net = {'dimension': model['dimension'], 'controls': len(states),
           'initials': initials, 'transitions': transitions, 'bad': bad}
    return net, states, labels


def solve(model: dict, *, max_states: int = 10000,
          max_admissions: int = 20000, max_predecessors: int = 200000) -> dict:
    try:
        net, states, labels = compile_quotient(model, max_states)
    except OverflowError:
        return {'schema': 1, 'kind': 'unknown', 'reason': 'orbit budget'}
    result = antichain.solve(net, max_admissions=max_admissions, max_predecessors=max_predecessors)
    result['stats']['orbits'] = len(states)
    result['stats']['quotient_edges'] = len(labels)
    if result['kind'] == 'safe':
        result['states'] = [[q, list(regs)] for q, regs in states]
        return result
    if result['kind'] == 'unsafe':
        registers = tuple(model['initial_registers'])
        steps = []
        for eid in result.pop('transitions'):
            edge, (rid, tag, representative) = net['transitions'][eid], labels[eid]
            abstract_regs = states[edge['src']][1]
            atom = nominal.realize_atom(representative, abstract_regs, registers, model['constants'])
            rule = model['rules'][rid]
            steps.append([rid, tag, atom])
            registers = tuple(nominal.select(e, registers, atom) for e in rule['update'])
        result['steps'] = steps
    return result
