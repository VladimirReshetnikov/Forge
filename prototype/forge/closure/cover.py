# PROVENANCE: e8-invariant-ideals/prototype/finite_cover.py, ported with the
# house naming and validation conventions. The algorithm, the certificate
# shapes, and both worked families are that proposal's.
"""Finite-algebra covers for recursively generated trees.

A datatype with constructors c of arity a(c) is abstracted by a finite state
set Q with transitions delta_c : Q^a(c) -> Q, and a good set G. The goal is
that every finite constructor tree summarises into G.

A set R is an INDUCTIVE COVER when delta_c(q1..qa) lies in R for every
constructor and every tuple drawn from R -- for a nullary constructor, when its
designated state is in R. If R is an inductive cover and R is inside G, the
goal holds, by induction on a finite tree.

The positive certificate is therefore a bare list of state identifiers. The
checker verifies membership, distinctness, all constructor closures, and
inclusion in G. It does not recompute the least reachable set and does not care
how R was found: a larger closed cover is exactly as sound as the least one.
That is the cheapest checker in this package.

The negative certificate is a constructor-tree DAG in which every child index
is strictly smaller than its parent's, plus a designated root. The checker
re-evaluates each node in the INPUT algebra and checks that the root state is
outside G. No search tag substitutes for the tree.

Scope: this decides the supplied finite algebra. It is not a claim that an
arbitrary recursive function admits a sufficiently precise finite abstraction,
and for an abstracted infinite payload a bad abstract state gives no concrete
source counterexample -- its labels or transitions may be unrealisable.
"""
from __future__ import annotations
from itertools import product

SCHEMA = 'forge.finite-cover/1'


def validate_problem(problem) -> None:
    states = problem['states']
    if type(states) is not int or states <= 0:
        raise ValueError('positive state count required')
    constructors = problem['constructors']
    if type(constructors) is not list or not constructors:
        raise ValueError('constructor list required')
    names = set()
    for c in constructors:
        arity = c['arity']
        if type(c['name']) is not str or c['name'] in names:
            raise ValueError('distinct constructor names required')
        names.add(c['name'])
        if type(arity) is not int or not 0 <= arity <= 2:
            raise ValueError('this prototype supports arities zero through two')
        table = c['table']
        if (type(table) is not list or len(table) != states**arity or
                any(type(x) is not int or not 0 <= x < states for x in table)):
            raise ValueError('invalid transition table')
    good = problem['good']
    if (type(good) is not list or len(good) != len(set(good)) or
            any(type(x) is not int or not 0 <= x < states for x in good)):
        raise ValueError('invalid good-state set')


def transition(problem, constructor: int, args) -> int:
    c = problem['constructors'][constructor]
    if len(args) != c['arity']:
        raise ValueError('constructor arity mismatch')
    index = 0
    for a in args:
        if type(a) is not int or not 0 <= a < problem['states']:
            raise ValueError('state out of range')
        index = index*problem['states'] + a
    return c['table'][index]


def synthesize(problem, budget: int = 1_000_000):
    """Saturate, keeping a witness node for every newly reached state.

    Returns (certificate, statistics). The certificate is a cover, a
    counterexample tree, or `unknown` -- and `unknown` is a resource verdict,
    never a statement that no cover exists.
    """
    validate_problem(problem)
    reached: dict[int, int] = {}
    nodes: list[dict] = []
    visited: set[tuple] = set()
    evaluations = tuple_visits = rounds = 0
    good = set(problem['good'])
    while True:
        rounds += 1
        frontier = len(reached)
        states = sorted(reached)
        for index, c in enumerate(problem['constructors']):
            for args in product(states, repeat=c['arity']):
                tuple_visits += 1
                key = (index,) + args
                if key in visited:
                    continue
                if evaluations >= budget:
                    return ({'schema': SCHEMA, 'kind': 'unknown',
                             'reason': 'transition budget'},
                            {'evaluations': evaluations, 'rounds': rounds,
                             'tuple_visits': tuple_visits,
                             'states_reached': len(reached)})
                visited.add(key)
                evaluations += 1
                result = transition(problem, index, args)
                if result in reached:
                    continue
                nodes.append({'constructor': index,
                              'children': [reached[a] for a in args]})
                reached[result] = len(nodes)-1
                if result not in good:
                    return ({'schema': SCHEMA, 'kind': 'counterexample',
                             'problem': problem, 'nodes': nodes,
                             'root': len(nodes)-1},
                            {'states_reached': len(reached), 'rounds': rounds,
                             'evaluations': evaluations,
                             'tuple_visits': tuple_visits})
        if len(reached) == frontier:
            return ({'schema': SCHEMA, 'kind': 'cover', 'problem': problem,
                     'cover': sorted(reached)},
                    {'states_reached': len(reached), 'rounds': rounds,
                     'evaluations': evaluations, 'tuple_visits': tuple_visits})


def binary_tree_counts(modulus: int) -> dict:
    """Leaves against internal nodes, both modulo `modulus`.

    Closure is one line: (l1+l2) - (n1+n2+1) = (l1-n1) + (l2-n2) - 1.

    The certificate establishes the CONGRUENCE. It does not license upgrading
    that to the integer equality L = N + 1, even though the integer equality is
    what motivated the choice of states.
    """
    if type(modulus) is not int or modulus <= 0:
        raise ValueError('positive modulus required')
    m = modulus
    n = m*m
    return {
        'states': n,
        'constructors': [
            {'name': 'leaf', 'arity': 0, 'table': [(1 % m)*m]},
            {'name': 'node', 'arity': 2,
             'table': [((a//m + b//m) % m)*m + ((a % m + b % m + 1) % m)
                       for a in range(n) for b in range(n)]}],
        'good': [a*m+b for a in range(m) for b in range(m) if (a-b-1) % m == 0]}


def mirror_problem(operation) -> dict:
    """A fold against a mirror fold in an arbitrary finite magma.

    No associativity is assumed. If the operation commutes the diagonal is
    closed and associativity is irrelevant; if some a*b differs from b*a, the
    two-leaf tree is already the counterexample.
    """
    k = len(operation)
    if not k or any(len(row) != k for row in operation):
        raise ValueError('square operation table required')
    n = k*k
    constructors = [{'name': 'leaf_%d' % a, 'arity': 0, 'table': [a*k+a]}
                    for a in range(k)]
    constructors.append(
        {'name': 'node', 'arity': 2,
         'table': [operation[a//k][b//k]*k + operation[b % k][a % k]
                   for a in range(n) for b in range(n)]})
    return {'states': n, 'constructors': constructors,
            'good': [a*k+a for a in range(k)]}
