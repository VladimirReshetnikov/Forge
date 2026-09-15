"""Exact finite-algebra reachability for recursively generated trees.

Search returns either an inductive cover or a concrete constructor-tree DAG.
The checker checks closure or evaluates that DAG; it does not run reachability.
"""
from itertools import product
from math import prod


def validate_problem(problem):
    n = problem['states']
    if type(n) is not int or n <= 0:
        raise ValueError('positive state count required')
    ctors = problem['constructors']
    if type(ctors) is not list:
        raise ValueError('constructor list required')
    names = set()
    for c in ctors:
        a = c['arity']
        if type(c['name']) is not str or c['name'] in names:
            raise ValueError('distinct constructor names required')
        names.add(c['name'])
        if type(a) is not int or not 0 <= a <= 2:
            raise ValueError('prototype supports arities zero through two')
        if (type(c['table']) is not list or len(c['table']) != n**a or
            any(type(x) is not int or not 0 <= x < n for x in c['table'])):
            raise ValueError('invalid transition table')
    good = problem['good']
    if (type(good) is not list or len(good) != len(set(good)) or
        any(type(x) is not int or not 0 <= x < n for x in good)):
        raise ValueError('invalid good-state set')


def transition(problem, constructor, args):
    c = problem['constructors'][constructor]
    if len(args) != c['arity']:
        raise ValueError('constructor arity mismatch')
    i = 0
    for a in args:
        if type(a) is not int or not 0 <= a < problem['states']:
            raise ValueError('state out of range')
        i = i * problem['states'] + a
    return c['table'][i]


def synthesize(problem, budget=1000000):
    validate_problem(problem)
    reached = {}  # state -> earlier-indexed term-DAG node
    nodes = []
    visited = set()
    evaluations = tuple_visits = rounds = 0
    good = set(problem['good'])
    while True:
        rounds += 1
        frontier_size = len(reached)
        states = sorted(reached)
        for ci, c in enumerate(problem['constructors']):
            for args in product(states, repeat=c['arity']):
                tuple_visits += 1
                key = (ci,) + args
                if key in visited:
                    continue
                if evaluations >= budget:
                    return {'schema': 'forge.finite-cover/1', 'kind': 'unknown',
                            'reason': 'transition budget'}, {'evaluations': evaluations}
                visited.add(key)
                evaluations += 1
                result = transition(problem, ci, args)
                if result not in reached:
                    node = {'constructor': ci, 'children': [reached[a] for a in args]}
                    reached[result] = len(nodes)
                    nodes.append(node)
                    if result not in good:
                        cert = {'schema': 'forge.finite-cover/1', 'kind': 'counterexample',
                                'problem': problem, 'nodes': nodes, 'root': len(nodes)-1}
                        return cert, {'states_reached': len(reached), 'rounds': rounds,
                                      'evaluations': evaluations, 'tuple_visits': tuple_visits}
        if len(reached) == frontier_size:
            cert = {'schema': 'forge.finite-cover/1', 'kind': 'cover', 'problem': problem,
                    'cover': sorted(reached)}
            return cert, {'states_reached': len(reached), 'rounds': rounds,
                          'evaluations': evaluations, 'tuple_visits': tuple_visits}


def check(problem, certificate):
    try:
        validate_problem(problem)
        if (certificate.get('schema') != 'forge.finite-cover/1' or
            certificate.get('problem') != problem):
            return False
        n = problem['states']
        good = set(problem['good'])
        if certificate['kind'] == 'cover':
            raw = certificate['cover']
            if (type(raw) is not list or len(raw) != len(set(raw)) or
                any(type(x) is not int or not 0 <= x < n for x in raw)):
                return False
            cover = set(raw)
            if not cover <= good:
                return False
            for ci, c in enumerate(problem['constructors']):
                for args in product(raw, repeat=c['arity']):
                    if transition(problem, ci, args) not in cover:
                        return False
            return True
        if certificate['kind'] == 'counterexample':
            values = []
            for node in certificate['nodes']:
                ci = node['constructor']
                if type(ci) is not int or not 0 <= ci < len(problem['constructors']):
                    return False
                children = node['children']
                if (type(children) is not list or
                    any(type(i) is not int or not 0 <= i < len(values) for i in children)):
                    return False
                values.append(transition(problem, ci, [values[i] for i in children]))
            root = certificate['root']
            return (type(root) is int and 0 <= root < len(values) and values[root] not in good)
        return False
    except (KeyError, TypeError, ValueError, IndexError, AttributeError):
        return False


def binary_tree_counts(modulus):
    """State = (leaf count, internal-node count), each modulo modulus."""
    m = modulus
    n = m*m
    return {'states': n, 'constructors': [
        {'name': 'leaf', 'arity': 0, 'table': [(1 % m)*m]},
        {'name': 'node', 'arity': 2,
         'table': [((a//m + b//m) % m)*m + ((a % m + b % m + 1) % m)
                   for a in range(n) for b in range(n)]}],
        'good': [a*m+b for a in range(m) for b in range(m) if (a-b-1) % m == 0]}


def mirror_problem(operation):
    """Pair the original and mirrored evaluations in an arbitrary finite magma."""
    k = len(operation)
    if not k or any(len(row) != k for row in operation):
        raise ValueError('square operation table required')
    n = k*k
    ctors = [{'name': 'leaf_%d' % a, 'arity': 0, 'table': [a*k+a]} for a in range(k)]
    ctors.append({'name': 'node', 'arity': 2,
                  'table': [operation[a//k][b//k]*k + operation[b % k][a % k]
                            for a in range(n) for b in range(n)]})
    return {'states': n, 'constructors': ctors, 'good': [a*k+a for a in range(k)]}
