"""Hardened, standard-library-only decoding and replay of stored certificates.

PROVENANCE
  BASE  p1-structural-search/prototype/verify_certificates.py -- bounded decoders
        (regex-restricted rationals with a bit-length cap, polynomial shape/size
        limits, bounded exponents, bounded tree depth) and the family dispatch.
  FOLD  p3-planner-certificate-layer/prototype/replay.py -- the json
        object_pairs_hook that rejects duplicate keys outright.
  FOLD  p9-proof-planner/scripts/verify_certificates.py -- the well_typed gate
        applied to every decoded first-order term.
  FOLD  p6-proof-logging-cdcl/prototype/replay_certificates.py -- anti-vacuity:
        every decoded induction certificate is MUTATED and the mutation must be
        rejected, and a bundle missing a required family is a hard failure.

This module imports nothing outside the standard library and forge's exact
checkers: no NumPy, SciPy, SymPy or search engine is reachable from here.
This is research tooling, not a hardened service for hostile uploads, and it is
not a Lean kernel.
"""
from __future__ import annotations
import json
import re
from fractions import Fraction as Q

from ..poly import Poly
from ..certificates import (ConeTerm, ConeCertificate, check_cone,
                            BernsteinLeaf, BernsteinSplit, check_bernstein,
                            CoefficientLeaf, CoefficientSplit,
                            check_bernstein_expansion,
                            InvariantCertificate, check_invariant)
from ..recurrence import check_recurrence
from ..univariate import UnivariateCertificate, check_univariate
from ..witness.affine import AffineWitness, check_affine_witness
from ..witness import lattice as lattice_witness
from ..witness import modular as modular_witness
from .. import terms as terms_module
from .. import induction as induction_module
from .. import horn as horn_module
from .. import sat as sat_module
from ..closure import certificates as closure_checkers
from ..closure import kripke as kripke_module
from ..closure import words as words_module
from ..wsts import certificates as wsts_checkers

RATIONAL = re.compile(r'-?[0-9]+(?:/[1-9][0-9]*)?')

REQUIRED_FAMILIES = ('Quadratic SOS', 'Bernstein box', 'List induction',
                     'CDCL(T) refutation', 'Observable closure',
                     'Finite cover', 'Integer projection',
                     'Kripke countermodel', 'Ore common multiple',
                     'Coverability frontier', 'Backward-closed basis')


class DecodeError(ValueError):
    pass


def no_duplicate_keys(pairs):
    """p3: a duplicate JSON key is malformed input, never a last-one-wins merge."""
    d = {}
    for k, v in pairs:
        if k in d:
            raise DecodeError('duplicate JSON key: ' + str(k))
        d[k] = v
    return d


def loads(text: str):
    return json.loads(text, object_pairs_hook=no_duplicate_keys)


# ---------------------------------------------------------------------------
# Bounded scalar / polynomial decoders (p1).
# ---------------------------------------------------------------------------
def rational(x) -> Q:
    if not isinstance(x, str) or len(x) > 2500 or not RATIONAL.fullmatch(x):
        raise DecodeError('invalid bounded rational')
    q = Q(x)
    if max(q.numerator.bit_length(), q.denominator.bit_length()) > 4096:
        raise DecodeError('rational bit limit')
    return q


def integer(x, low: int, high: int) -> int:
    if type(x) is not int or not low <= x <= high:
        raise DecodeError('integer outside permitted range')
    return x


def polynomial(x) -> Poly:
    if not isinstance(x, dict) or set(x) != {'n', 'terms'}:
        raise DecodeError('invalid polynomial object')
    n, ts = x['n'], x['terms']
    if type(n) is not int or not 1 <= n <= 8 or not isinstance(ts, list) or len(ts) > 5000:
        raise DecodeError('polynomial shape/size limit')
    terms = []
    seen = set()
    for item in ts:
        if not isinstance(item, list) or len(item) != 2:
            raise DecodeError('invalid term')
        e, c = item
        if (not isinstance(e, list) or len(e) != n
                or any(type(k) is not int or k < 0 for k in e) or sum(e) > 256):
            raise DecodeError('invalid monomial')
        if tuple(e) in seen:
            raise DecodeError('duplicate monomial')
        seen.add(tuple(e))
        terms.append((tuple(e), rational(c)))
    return Poly.make(n, terms)


def box(x) -> tuple[tuple[Q, Q], ...]:
    if not isinstance(x, list) or not 1 <= len(x) <= 8:
        raise DecodeError('invalid box')
    out = []
    for pair in x:
        if not isinstance(pair, list) or len(pair) != 2:
            raise DecodeError('invalid interval')
        l, u = rational(pair[0]), rational(pair[1])
        if not l < u:
            raise DecodeError('degenerate interval')
        out.append((l, u))
    return tuple(out)


def cone(x) -> ConeCertificate:
    if not isinstance(x, dict) or set(x) != {'terms', 'equality_multipliers'}:
        raise DecodeError('invalid cone object')
    if len(x['terms']) > 5000 or len(x['equality_multipliers']) > 64:
        raise DecodeError('cone size limit')
    ts = []
    for t in x['terms']:
        if not isinstance(t, dict) or set(t) != {'weight', 'square', 'powers'}:
            raise DecodeError('invalid cone term')
        powers = t['powers']
        if (not isinstance(powers, list) or len(powers) > 32
                or any(type(k) is not int or not 0 <= k <= 32 for k in powers)):
            raise DecodeError('invalid powers')
        ts.append(ConeTerm(rational(t['weight']), polynomial(t['square']), tuple(powers)))
    return ConeCertificate(tuple(ts),
                           tuple(polynomial(p) for p in x['equality_multipliers']))


def bernstein_tree(x, depth: int = 0):
    if depth > 64 or not isinstance(x, dict):
        raise DecodeError('invalid tree/depth')
    if set(x) == {'leaf'}:
        return BernsteinLeaf(rational(x['leaf']))
    if set(x) != {'axis', 'point', 'left', 'right'}:
        raise DecodeError('invalid split fields')
    return BernsteinSplit(integer(x['axis'], 0, 7), rational(x['point']),
                          bernstein_tree(x['left'], depth + 1),
                          bernstein_tree(x['right'], depth + 1))


def coefficient_tree(x, depth: int = 0):
    if depth > 64 or not isinstance(x, dict):
        raise DecodeError('invalid tree/depth')
    if set(x) == {'leaf'}:
        v = x['leaf']
        if set(v) != {'box', 'degrees', 'coefficients'}:
            raise DecodeError('invalid coefficient leaf')
        degrees = tuple(integer(d, 0, 64) for d in v['degrees'])
        if len(v['coefficients']) > 100_000:
            raise DecodeError('coefficient count limit')
        coefficients = tuple((tuple(integer(k, 0, 64) for k in key), rational(c))
                             for key, c in v['coefficients'])
        return CoefficientLeaf(box(v['box']), degrees, coefficients)
    if set(x) != {'split'}:
        raise DecodeError('invalid coefficient node')
    v = x['split']
    if set(v) != {'box', 'axis', 'cut', 'left', 'right'}:
        raise DecodeError('invalid coefficient split')
    return CoefficientSplit(box(v['box']), integer(v['axis'], 0, 7), rational(v['cut']),
                            coefficient_tree(v['left'], depth + 1),
                            coefficient_tree(v['right'], depth + 1))


# ---------------------------------------------------------------------------
# First-order terms (p9's well_typed gate).
# ---------------------------------------------------------------------------
def term(x):
    t = terms_module.parse_term(x)
    if not terms_module.well_typed(t):  # belt and braces: the gate is explicit
        raise DecodeError('ill-sorted term')
    return t


def horn_term(x, depth: int = 0) -> horn_module.Term:
    if depth > 32 or not isinstance(x, dict) or set(x) != {'symbol', 'args'}:
        raise DecodeError('invalid horn term')
    if not isinstance(x['symbol'], str) or not 1 <= len(x['symbol']) <= 64:
        raise DecodeError('invalid horn symbol')
    if not isinstance(x['args'], list) or len(x['args']) > 8:
        raise DecodeError('invalid horn arguments')
    return horn_module.Term(x['symbol'],
                            tuple(horn_term(a, depth + 1) for a in x['args']))


def horn_atom(x) -> horn_module.Atom:
    if not isinstance(x, dict) or set(x) != {'predicate', 'args'}:
        raise DecodeError('invalid horn atom')
    if not isinstance(x['predicate'], str) or not 1 <= len(x['predicate']) <= 64:
        raise DecodeError('invalid horn predicate')
    return horn_module.Atom(x['predicate'], tuple(horn_term(a) for a in x['args']))


def horn_rule(x) -> horn_module.Rule:
    if not isinstance(x, dict) or set(x) != {'name', 'head', 'body'}:
        raise DecodeError('invalid horn rule')
    return horn_module.Rule(str(x['name']), horn_atom(x['head']),
                            tuple(horn_atom(a) for a in x['body']))


def horn_certificate(x) -> horn_module.HornCertificate:
    if not isinstance(x, dict) or set(x) != {'nodes', 'root'}:
        raise DecodeError('invalid horn certificate')
    if len(x['nodes']) > 100_000:
        raise DecodeError('proof size limit')
    nodes = []
    for node in x['nodes']:
        if set(node) != {'conclusion', 'rule', 'substitution', 'premises'}:
            raise DecodeError('invalid proof node')
        rule = node['rule']
        if rule is not None:
            rule = integer(rule, 0, 10 ** 6)
        nodes.append(horn_module.ProofNode(
            horn_atom(node['conclusion']), rule,
            tuple((str(k), horn_term(v)) for k, v in node['substitution']),
            tuple(integer(j, 0, 10 ** 6) for j in node['premises'])))
    return horn_module.HornCertificate(tuple(nodes), integer(x['root'], 0, 10 ** 6))


# ---------------------------------------------------------------------------
# Family dispatch.
# ---------------------------------------------------------------------------
def verify(record) -> bool:
    if not isinstance(record, dict) or not {'family', 'input', 'certificate'} <= set(record):
        raise DecodeError('invalid record')
    inp, c, family = record['input'], record['certificate'], record['family']

    if family in ('Quadratic SOS', 'Finite cone LP'):
        return check_cone(polynomial(inp['p']),
                          [polynomial(p) for p in inp.get('inequalities', [])],
                          [polynomial(p) for p in inp.get('equalities', [])],
                          cone(c))
    if family == 'Bernstein box':
        return check_bernstein(polynomial(inp['p']), box(inp['box']), bernstein_tree(c))
    if family == 'Bernstein expansion':
        return check_bernstein_expansion(polynomial(inp['p']), box(inp['box']),
                                         coefficient_tree(c))
    if family == 'Polynomial recurrence':
        return check_recurrence(polynomial(inp['step']), polynomial(inp['initial']),
                                polynomial(c))
    if family == 'Conserved invariant':
        return check_invariant(InvariantCertificate(
            polynomial(c['invariant']), tuple(rational(v) for v in c['initial']),
            tuple(polynomial(p) for p in c['transition'])))
    if family == 'Integral affine witness':
        cert = AffineWitness(tuple(tuple(rational(v) for v in r) for r in c['linear']),
                             tuple(rational(v) for v in c['offset']))
        return check_affine_witness(inp['A'], inp['B'], inp['c'], cert, True)
    if family == 'Univariate with zeros':
        cert = UnivariateCertificate(polynomial(c['square']), polynomial(c['residual']),
                                     tuple(polynomial(p) for p in c['chain']))
        a, b = rational(inp['interval'][0]), rational(inp['interval'][1])
        return check_univariate(polynomial(inp['p']), a, b, cert)
    if family == 'Horn proof':
        return horn_module.check_horn(tuple(horn_atom(a) for a in inp['facts']),
                                      tuple(horn_rule(r) for r in inp['rules']),
                                      horn_atom(inp['goal']), horn_certificate(c))
    if family == 'List induction':
        return induction_module.verify(term(inp['lhs']), term(inp['rhs']), c)
    if family == 'Induction bank':
        bank = induction_module.TheoremBank()
        if not isinstance(c, dict) or set(c) != {'lemmas', 'specialization'}:
            raise DecodeError('invalid induction bank')
        if not c['lemmas'] or len(c['lemmas']) > 256:
            raise DecodeError('induction bank size limit')
        for entry in c['lemmas']:
            if not bank.add(str(entry['name']), term(entry['lhs']), term(entry['rhs']),
                            entry['certificate']):
                return False
        spec = c['specialization']
        if spec is None:
            return True
        rules = {r.name: r for r in terms_module.DEFINITIONS + bank.rules}
        if len(rules) != len(terms_module.DEFINITIONS) + len(bank.rules):
            return False
        lhs, rhs = term(spec['goal']['lhs']), term(spec['goal']['rhs'])
        left = tuple(terms_module.Step(tuple(st['path']), str(st['rule']))
                     for st in spec['left'])
        right = tuple(terms_module.Step(tuple(st['path']), str(st['rule']))
                      for st in spec['right'])
        a = terms_module.replay(lhs, left, rules)
        b = terms_module.replay(rhs, right, rules)
        return a is not None and a == b
    if family == 'Lemma bundle':
        return induction_module.verify_bundle(c, inp.get('required', ()))
    if family == 'Integer lattice':
        steps = tuple(lattice_witness.Step(
            integer(s['row'], 0, 4096), tuple(map(tuple, s['transform'])),
            s['gcd'], s['residual'], s['quotient'], s['obstruction'])
            for s in c['steps'])
        cert = lattice_witness.Certificate(c['feasible'], steps,
                                           tuple(c['witness']), tuple(map(tuple, c['basis'])))
        return lattice_witness.check(inp['A'], inp['b'], cert)
    if family == 'Modular witness':
        return modular_witness.verify(inp['a'], inp['b'], inp['m'], c)
    if family == 'CDCL(T) refutation':
        atoms = {int(k): sat_module.DiffAtom(**v) for k, v in inp['atoms'].items()}
        return sat_module.replay(inp['n'], inp['clauses'], atoms, c)
    # --- extension round: closure families ---------------------------------
    if family in ('Observable closure', 'Separating word'):
        model = words_module.Model.build(
            integer(inp['dimension'], 1, 256), inp['initial'], inp['output'],
            inp['actions'])
        if family == 'Observable closure':
            return closure_checkers.check_observable(model, c)
        return closure_checkers.check_separating_word(model, c['word'], c['value'])
    if family in ('Finite cover', 'Constructor counterexample'):
        return closure_checkers.check_cover(inp, c)
    if family == 'Integer projection':
        return closure_checkers.check_projection(inp, c)
    if family == 'Kripke countermodel':
        return kripke_module.verify(inp, c)
    if family == 'Ore common multiple':
        return closure_checkers.check_ore(inp, c)
    if family == 'Singularity plan':
        return closure_checkers.check_singularity_plan(inp, c)
    if family == 'CDCL(T) resolution refutation':
        atoms = {int(k): sat_module.DiffAtom(**v) for k, v in inp['atoms'].items()}
        return sat_module.verify_resolution(inp['clauses'], atoms, inp.get('nodes'), c)
    # --- fourth round: finite bases for infinite state spaces ---------------
    # These raise on rejection rather than returning False, because a rejected
    # certificate here is a specific mathematical complaint worth reporting.
    if family in ('Coverability frontier', 'Backward-closed basis',
                  'Unsafe run', 'Parameter threshold'):
        try:
            if family == 'Coverability frontier':
                wsts_checkers.check_frontier(inp, c)
            elif family == 'Backward-closed basis':
                wsts_checkers.check_backward_closed(inp, c)
            elif family == 'Unsafe run':
                wsts_checkers.check_counterexample(inp, c)
            else:
                wsts_checkers.check_threshold(inp, c)
        except (wsts_checkers.InvalidCertificate, KeyError, TypeError,
                IndexError, ValueError):
            return False
        return True
    raise DecodeError('unknown family: ' + str(family))


# ---------------------------------------------------------------------------
# Anti-vacuity (p6).
# ---------------------------------------------------------------------------
def _inflate_leaves(node):
    if set(node) == {'leaf'}:
        node['leaf'] = '1000000'
        return
    for side in ('left', 'right'):
        _inflate_leaves(node[side])


def mutations(record) -> list:
    """Produce records that MUST be rejected, given one that must be accepted."""
    import copy
    out = []
    family, c = record['family'], record['certificate']
    if family == 'List induction':
        for branch in range(len(c.get('branches', []))):
            for side in ('left', 'right'):
                trace = c['branches'][branch][side]
                if trace:
                    bad = copy.deepcopy(record)
                    bad['certificate']['branches'][branch][side] = trace[:-1]
                    out.append(bad)
        bad = copy.deepcopy(record)
        bad['certificate']['generalized'] = list(bad['certificate']['generalized']) + ['?zzz']
        out.append(bad)
    elif family == 'Induction bank':
        if len(c['lemmas']) > 1:
            bad = copy.deepcopy(record)
            del bad['certificate']['lemmas'][0]
            out.append(bad)
        if c['specialization'] and c['specialization']['left']:
            bad = copy.deepcopy(record)
            bad['certificate']['specialization']['left'] =                 bad['certificate']['specialization']['left'][:-1]
            out.append(bad)
    elif family == 'Lemma bundle':
        for i in range(len(c)):
            if c[i].get('status') == 'proved':
                bad = copy.deepcopy(record)
                bad['certificate'][i]['certificate']['branches'][1]['left'] = []
                out.append(bad)
    elif family in ('Quadratic SOS', 'Finite cone LP') and c['terms']:
        bad = copy.deepcopy(record)
        bad['certificate']['terms'][0]['weight'] = '-1'
        out.append(bad)
        bad = copy.deepcopy(record)
        w = Q(bad['certificate']['terms'][0]['weight'])
        # p5's float-tolerance exploit, in serialised form.
        bad['certificate']['terms'][0]['weight'] = str(w * Q(10 ** 20 + 1, 10 ** 20))
        out.append(bad)
    elif family == 'Bernstein box':
        bad = copy.deepcopy(record)
        _inflate_leaves(bad['certificate'])
        out.append(bad)
    elif family == 'Bernstein expansion':
        bad = copy.deepcopy(record)
        node = bad['certificate']
        while set(node) == {'split'}:
            node = node['split']['left']
        first = node['leaf']['coefficients'][0]
        first[1] = str(Q(first[1]) + Q(1, 10 ** 18))
        out.append(bad)
    elif family == 'Horn proof':
        bad = copy.deepcopy(record)
        bad['input']['facts'] = []
        out.append(bad)
    elif family in ('CDCL(T) refutation',) and c:
        bad = copy.deepcopy(record)
        bad['certificate'] = bad['certificate'][:-1]
        out.append(bad)
    elif family == 'CDCL(T) resolution refutation':
        bad = copy.deepcopy(record)
        bad['certificate']['root'] = 0
        out.append(bad)
    elif family == 'Polynomial recurrence':
        bad = copy.deepcopy(record)
        bad['certificate']['terms'].append([[0] * bad['certificate']['n'], '1'])
        out.append(bad)
    elif family == 'Conserved invariant':
        bad = copy.deepcopy(record)
        bad['certificate']['invariant']['terms'].append(
            [[0] * bad['certificate']['invariant']['n'], '1'])
        out.append(bad)
    elif family == 'Univariate with zeros':
        bad = copy.deepcopy(record)
        bad['certificate']['chain'] = bad['certificate']['chain'][:-1]
        out.append(bad)
    elif family == 'Integral affine witness':
        bad = copy.deepcopy(record)
        bad['certificate']['offset'][0] = str(Q(bad['certificate']['offset'][0]) + 1)
        out.append(bad)
    elif family == 'Integer lattice':
        bad = copy.deepcopy(record)
        if bad['certificate']['witness']:
            bad['certificate']['witness'][0] += 1
            out.append(bad)
    elif family == 'Modular witness':
        bad = copy.deepcopy(record)
        bad['certificate']['offsets'][0] += 1
        out.append(bad)
    # --- extension round -----------------------------------------------------
    # Each mutation changes one specific checked quantity, following e9's
    # design rather than flipping random bytes. Note that the converse is NOT
    # claimed: scaling a whole valid certificate can produce another valid one.
    elif family == 'Observable closure':
        bad = copy.deepcopy(record)
        bad['certificate']['target_coordinates'] = [
            [0, 1] for _ in bad['certificate']['target_coordinates']]
        out.append(bad)                      # target no longer spanned
        bad = copy.deepcopy(record)
        first = bad['certificate']['basis'][0][0]
        bad['certificate']['basis'][0][0] = [first[0] + first[1], first[1]]
        out.append(bad)                      # invariant row no longer invariant
    elif family == 'Separating word':
        bad = copy.deepcopy(record)
        bad['certificate']['value'] = [0, 1]
        out.append(bad)                      # a zero observation refutes nothing
        bad = copy.deepcopy(record)
        bad['certificate']['word'] = bad['certificate']['word'][:-1]
        out.append(bad)                      # a shorter word observes zero
    elif family == 'Finite cover':
        bad = copy.deepcopy(record)
        bad['certificate']['cover'] = sorted(
            set(bad['certificate']['cover']) | {bad['input']['states'] - 1})
        out.append(bad)
        bad = copy.deepcopy(record)
        if len(bad['certificate']['cover']) > 1:
            del bad['certificate']['cover'][0]
            out.append(bad)                  # no longer constructor-closed
    elif family == 'Constructor counterexample':
        bad = copy.deepcopy(record)
        bad['certificate']['nodes'][-1]['children'] = [len(bad['certificate']['nodes']) - 1]
        out.append(bad)                      # self-reference, not a finite tree
    elif family == 'Integer projection':
        bad = copy.deepcopy(record)
        bad['certificate']['bezout'][0][1] += 1
        out.append(bad)                      # the Bezout combination no longer holds
        bad = copy.deepcopy(record)
        bad['certificate']['program']['guards'] = []
        out.append(bad)                      # a deleted guard is not a stronger result
    elif family == 'Kripke countermodel':
        bad = copy.deepcopy(record)
        n = bad['certificate']['worlds']
        bad['certificate']['relation'] = [[i == j for j in range(n)] for i in range(n)]
        out.append(bad)                      # discrete order: the root is not least
        for name in bad['certificate']['valuation']:
            bad = copy.deepcopy(record)
            values = bad['certificate']['valuation'][name]
            bad['certificate']['valuation'][name] = [not v for v in values]
            out.append(bad)                  # persistence or the goal now fails
            break
    elif family == 'Ore common multiple':
        bad = copy.deepcopy(record)
        bad['certificate']['common'][-1] = [[1, 1], [1, 1]]
        out.append(bad)                      # U A no longer equals the claimed L
    elif family == 'Singularity plan':
        bad = copy.deepcopy(record)
        if bad['certificate']['seed_indices']:
            del bad['certificate']['seed_indices'][0]
            out.append(bad)                  # a removed seed is an unproved pivot
        bad = copy.deepcopy(record)
        bad['certificate']['bound'] = 0
        out.append(bad)                      # an understated root bound
    elif family == 'Coverability frontier':
        bad = copy.deepcopy(record)
        bad['certificate']['basis'][0]['marking'][0] += 1
        out.append(bad)                      # the basis is no longer minimal
        bad = copy.deepcopy(record)
        if len(bad['certificate']['basis']) > 1:
            del bad['certificate']['basis'][-1]
            out.append(bad)                  # a dropped element breaks closure
    elif family == 'Backward-closed basis':
        bad = copy.deepcopy(record)
        if bad['certificate']['basis'][0]:
            bad['certificate']['basis'][0][0][0] += 1
            out.append(bad)                  # raising it opens a predecessor gap
    return out


def verify_bundle(records, required=REQUIRED_FAMILIES) -> dict:
    """Replay a bundle; fail loudly rather than succeed vacuously."""
    if not isinstance(records, list) or not records or len(records) > 10_000:
        raise DecodeError('record count limit')
    counts: dict[str, int] = {}
    rejected = 0
    for i, record in enumerate(records):
        if not verify(record):
            raise DecodeError('REJECTED certificate %d (%s)' % (i, record.get('id')))
        counts[record['family']] = counts.get(record['family'], 0) + 1
        for bad in mutations(record):
            try:
                accepted = verify(bad)
            except (DecodeError, ValueError, TypeError, KeyError, IndexError):
                accepted = False
            if accepted:
                raise DecodeError('accepted a mutated certificate at record %d' % i)
            rejected += 1
    missing = [f for f in required if not counts.get(f)]
    if missing:
        raise DecodeError('missing required certificate families: ' + ', '.join(missing))
    if not rejected:
        raise DecodeError('no mutation was exercised; the run would be vacuous')
    return {'records': len(records), 'families': counts, 'mutations_rejected': rejected}
