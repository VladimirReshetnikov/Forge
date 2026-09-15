# PROVENANCE: e4-delta-countermodels/forge_delta/kripke.py, ported with the
# house naming conventions and without that package's shared validation
# helpers. The semantics, the proposer, the branching fixtures, and the scope
# discipline are that proposal's.
"""Finite Kripke countermodels for intuitionistic propositional logic.

What an accepted certificate establishes, exactly:

    there is no derivation of G from Gamma in the named IPC calculus.

It does NOT mean Lean can prove not-G, that no Lean term of G exists, or that
classical reasoning cannot prove G. It says nothing about domain hypotheses
omitted from the object sequent. This is the collection's only checkable
refutation object, and keeping its scope narrow is what makes it sound.

A model is worlds 0..n-1 with a least root, a partial order, and one persistent
Boolean valuation per atom. Forcing is the usual recursive definition, with

    w |- A -> B   iff   for every v >= w, v |- A implies v |- B.

Checking implication at the current world only would collapse the semantics to
something essentially classical and would be wrong for this purpose.

The checker RECOMPUTES forcing. Any solver-supplied table of formula truth
values is unnecessary and untrusted. The proposer evaluates with bit masks over
rooted trees; the checker uses a plain recursive function over the explicit
relation matrix, so the two do not share an evaluator.

When the world bound or model budget is exhausted the result is `unknown`. IPC
having the finite model property does not turn a three-world cap into a
decision procedure, and valid schemas in a corpus are positive controls against
an invalid refuter, not theorems proved by the absence of a small countermodel.
"""
from __future__ import annotations
from functools import lru_cache
from itertools import product

MAX_WORLDS = 32
MAX_ATOMS = 16
MAX_CONTEXT = 64
MAX_DEPTH = 64
MAX_NODES = 1024


class Invalid(ValueError):
    """A structural rejection. Never a statement about the sequent."""


def _require(condition, message):
    if not condition:
        raise Invalid(message)


def atom(name): return ['var', name]
def bot(): return ['bot']
def conj(a, b): return ['and', a, b]
def disj(a, b): return ['or', a, b]
def imp(a, b): return ['imp', a, b]
def neg(a): return imp(a, bot())


def formula(raw, depth: int = 0, fuel: list | None = None) -> tuple:
    if fuel is None:
        fuel = [0]
    fuel[0] += 1
    _require(depth <= MAX_DEPTH and fuel[0] <= MAX_NODES, 'formula budget')
    _require(type(raw) is list and raw and type(raw[0]) is str, 'formula node')
    tag = raw[0]
    if tag == 'var':
        _require(len(raw) == 2 and type(raw[1]) is str and 0 < len(raw[1]) <= 128, 'atom')
        return (tag, raw[1])
    if tag == 'bot':
        _require(len(raw) == 1, 'bottom arity')
        return (tag,)
    _require(tag in ('and', 'or', 'imp') and len(raw) == 3, 'connective arity')
    return (tag, formula(raw[1], depth+1, fuel), formula(raw[2], depth+1, fuel))


def atoms(f: tuple) -> set[str]:
    if f[0] == 'var':
        return {f[1]}
    if f[0] == 'bot':
        return set()
    return atoms(f[1]) | atoms(f[2])


def sequent(goal, context=None) -> dict:
    return {'version': 1, 'kind': 'propositional_sequent', 'logic': 'IPC',
            'context': [] if context is None else context, 'goal': goal}


def parse_problem(problem):
    _require(type(problem) is dict, 'problem object')
    _require(set(problem) == {'version', 'kind', 'logic', 'context', 'goal'},
             'unexpected problem fields')
    _require(problem['version'] == 1 and
             problem['kind'] == 'propositional_sequent' and
             problem['logic'] == 'IPC', 'unsupported logic')
    _require(type(problem['context']) is list and
             len(problem['context']) <= MAX_CONTEXT, 'context budget')
    context = [formula(f) for f in problem['context']]
    goal = formula(problem['goal'])
    names = set().union(*(atoms(f) for f in context + [goal]))
    _require(len(names) <= MAX_ATOMS, 'atom budget')
    return context, goal, sorted(names)


def _check(problem, certificate) -> None:
    context, goal, names = parse_problem(problem)
    _require(type(certificate) is dict, 'certificate object')
    _require(set(certificate) == {'kind', 'worlds', 'root', 'relation', 'valuation'},
             'unexpected certificate fields')
    _require(certificate['kind'] == 'finite_kripke_countermodel', 'certificate kind')
    n = certificate['worlds']
    _require(type(n) is int and 1 <= n <= MAX_WORLDS, 'world count')
    root = certificate['root']
    _require(type(root) is int and 0 <= root < n, 'root index')
    relation = certificate['relation']
    valuation = certificate['valuation']
    _require(type(relation) is list and len(relation) == n, 'relation rows')
    for row in relation:
        _require(type(row) is list and len(row) == n and
                 all(type(v) is bool for v in row), 'relation values')
    _require(all(relation[i][i] for i in range(n)), 'relation not reflexive')
    _require(all(relation[root][i] for i in range(n)), 'root not least')
    for i in range(n):
        for j in range(n):
            _require(i == j or not (relation[i][j] and relation[j][i]),
                     'relation not antisymmetric')
            for k in range(n):
                _require(not (relation[i][j] and relation[j][k]) or relation[i][k],
                         'relation not transitive')
    _require(type(valuation) is dict and set(valuation) == set(names),
             'valuation atom coverage')
    for values in valuation.values():
        _require(type(values) is list and len(values) == n and
                 all(type(v) is bool for v in values), 'valuation values')
        for i in range(n):
            for j in range(n):
                _require(not (values[i] and relation[i][j]) or values[j],
                         'valuation not persistent')

    # The recursive definition, as written in the mathematics. Do NOT trust a
    # truth table, witness annotations, or the proposer's bitset evaluation.
    @lru_cache(None)
    def force(w: int, f: tuple) -> bool:
        if f[0] == 'var':
            return valuation[f[1]][w]
        if f[0] == 'bot':
            return False
        if f[0] == 'and':
            return force(w, f[1]) and force(w, f[2])
        if f[0] == 'or':
            return force(w, f[1]) or force(w, f[2])
        return all(not relation[w][v] or not force(v, f[1]) or force(v, f[2])
                   for v in range(n))

    _require(all(force(root, f) for f in context), 'context not forced at root')
    _require(not force(root, goal), 'goal forced at root')


def verify(problem, certificate) -> bool:
    try:
        _check(problem, certificate)
        return True
    except (Invalid, TypeError, ValueError, KeyError, IndexError, RecursionError):
        return False


def tree_frames(n: int):
    """Rooted trees with parents before children, isomorphic duplicates included.

    This does not enumerate all finite partial orders. Rooted-tree unravelings
    suffice semantically for IPC, but a world cap remains incomplete, and no
    minimality or symmetry optimisation is claimed.
    """
    for parents in product(*(range(i) for i in range(1, n))):
        successors = [1 << i for i in range(n)]
        for i in range(n-1, 0, -1):
            successors[parents[i-1]] |= successors[i]
        yield successors


def _truth_bits(f, valuation, successors, allbits, cache):
    if f in cache:
        return cache[f]
    if f[0] == 'var':
        bits = valuation[f[1]]
    elif f[0] == 'bot':
        bits = 0
    else:
        a = _truth_bits(f[1], valuation, successors, allbits, cache)
        c = _truth_bits(f[2], valuation, successors, allbits, cache)
        if f[0] == 'and':
            bits = a & c
        elif f[0] == 'or':
            bits = a | c
        else:
            bad = a & (allbits ^ c)
            bits = sum(1 << w for w, s in enumerate(successors) if not (s & bad))
    cache[f] = bits
    return bits


def find_countermodel(problem, max_worlds: int = 3, max_models: int = 200_000) -> dict:
    """Increase the world count to the bound; propose the first model that fits.

    Every proposal is re-verified by `verify` before it is returned, so the
    proposer's bitset evaluation is never the acceptance path.
    """
    context, goal, names = parse_problem(problem)
    if not 1 <= max_worlds <= 6:
        raise ValueError('max_worlds must be between 1 and 6')
    models = frames = 0
    for n in range(1, max_worlds+1):
        full = (1 << n) - 1
        for successors in tree_frames(n):
            frames += 1
            upward = [b for b in range(1 << n)
                      if all(not (b >> w & 1) or b & s == s
                             for w, s in enumerate(successors))]
            for values in product(upward, repeat=len(names)):
                if models >= max_models:
                    return {'status': 'unknown', 'reason': 'model budget',
                            'stats': {'models': models, 'frames': frames}}
                models += 1
                valuation = dict(zip(names, values))
                cache: dict = {}
                if (all(_truth_bits(f, valuation, successors, full, cache) & 1
                        for f in context) and
                        not _truth_bits(goal, valuation, successors, full, cache) & 1):
                    certificate = {
                        'kind': 'finite_kripke_countermodel', 'worlds': n, 'root': 0,
                        'relation': [[bool(s >> j & 1) for j in range(n)]
                                     for s in successors],
                        'valuation': {name: [bool(b >> j & 1) for j in range(n)]
                                      for name, b in valuation.items()}}
                    if not verify(problem, certificate):
                        raise AssertionError('Kripke replay rejected its own proposal')
                    return {'status': 'countermodel', 'certificate': certificate,
                            'stats': {'models': models, 'frames': frames}}
    return {'status': 'unknown',
            'reason': 'world bound exhausted; no validity claim is made',
            'stats': {'models': models, 'frames': frames}}


# The enforcement tests. Each is classically valid, so an interface that turned
# any of these countermodels into a proof of the NEGATED Lean formula would be
# visibly unsound. They are not ornamental.
EXCLUDED_MIDDLE = sequent(disj(atom('P'), neg(atom('P'))))
DOUBLE_NEGATION = sequent(imp(neg(neg(atom('P'))), atom('P')))
PEIRCE = sequent(imp(imp(imp(atom('P'), atom('Q')), atom('P')), atom('P')))
# Needs a branching model: no chain of any length refutes it.
LINEARITY = sequent(disj(imp(atom('P'), atom('Q')), imp(atom('Q'), atom('P'))))
WEAK_EM = sequent(disj(neg(atom('P')), neg(neg(atom('P')))))
