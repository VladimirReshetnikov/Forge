"""Exact, deterministic multilinear reachable-span and context-quotient search.

Search is untrusted. checker.py has separate decoding, source semantics and
certificate arithmetic, and imports neither this module nor compilers.py.
Python 3.11+, standard library only. No floating point is used for decisions.
"""
from __future__ import annotations
from collections import deque
from fractions import Fraction as Q
from itertools import product
from dataclasses import dataclass
from typing import Any
import time

Vector = tuple[Q, ...]

def encode(v):
    return [str(x) for x in v]

def dot(a, b):
    return sum((x*y for x, y in zip(a, b)), Q(0))

def lincomb(basis, coeff, dimension):
    return tuple(sum((c*v[i] for c, v in zip(coeff, basis)), Q(0))
                 for i in range(dimension))

class Echelon:
    """Incremental span with coordinates in the ORIGINAL, reachable vectors."""
    def __init__(self, dimension: int):
        self.dimension = dimension
        self.basis: list[Vector] = []
        self.rows: list[tuple[int, Vector, Vector]] = []

    def reduce(self, v: Vector):
        if len(v) != self.dimension:
            raise ValueError('dimension mismatch')
        rem = list(v)
        coeff = [Q(0)] * len(self.basis)
        for pivot, row, origin in self.rows:
            factor = rem[pivot]
            if factor:
                rem = [x-factor*y for x, y in zip(rem, row)]
                coeff = [x+factor*y for x, y in zip(coeff, origin)]
        return tuple(rem), tuple(coeff)

    def coordinates(self, v):
        rem, coeff = self.reduce(v)
        return None if any(rem) else coeff

    def add(self, v):
        rem, coeff = self.reduce(tuple(v))
        if not any(rem):
            return False
        pivot = next(i for i, x in enumerate(rem) if x)
        scale = rem[pivot]
        row = tuple(x/scale for x in rem)
        origin = tuple(-x/scale for x in coeff) + (Q(1)/scale,)
        self.rows = [(p, r, c+(Q(0),)) for p, r, c in self.rows]
        self.rows.append((pivot, row, origin))
        self.rows.sort(key=lambda x: x[0])
        self.basis.append(tuple(v))
        return True

@dataclass(frozen=True)
class Budget:
    max_candidates: int = 100000
    max_bits: int = 8192
    max_basis: int = 4096

class Cutoff(Exception):
    pass

def bitcheck(values, cap):
    if any(max(x.numerator.bit_length(), x.denominator.bit_length()) > cap
           for x in values):
        raise Cutoff('coefficient_bit_limit')

def decode(problem):
    dims = problem['sorts']
    ops = []
    for op in problem['operations']:
        ops.append((op['out'], tuple(op['inputs']),
                    [(e['out'], tuple(e['in']), Q(e['q'])) for e in op['terms']]))
    targets = [(t['sort'], tuple(Q(x) for x in t['q'])) for t in problem['targets']]
    return dims, ops, targets

def apply(op, children, dims):
    out, _, terms = op
    ans = [Q(0)] * dims[out]
    for output, indices, coefficient in terms:
        v = coefficient
        for child, i in zip(children, indices):
            v *= child[i]
        ans[output] += v
    return tuple(ans)

def saturate(problem: dict[str, Any], budget=Budget(), stop_on_counterexample=True):
    """Return a certificate, not a trusted verdict. Incomplete work is UNKNOWN.

    Each (operation, original-basis-index tuple) is queued at most once.
    Basis witness nodes always point to earlier nodes; dependent vectors are
    never expanded. No shortest-counterexample claim is made.
    """
    start = time.perf_counter()
    dims, ops, targets = decode(problem)
    spaces = {s:Echelon(d) for s, d in dims.items()}
    refs = {s:[] for s in dims}
    nodes = []
    queue, scheduled = deque(), set()
    evaluations = 0

    def enqueue(oi, children):
        key = (oi, tuple(children))
        if key not in scheduled:
            scheduled.add(key)
            queue.append(key)

    for oi, (_, inputs, _) in enumerate(ops):
        if not inputs:
            enqueue(oi, ())

    def stats():
        return dict(candidate_evaluations=evaluations, scheduled=len(scheduled),
                    ranks={s:len(x.basis) for s,x in spaces.items()},
                    witness_nodes=len(nodes), seconds=time.perf_counter()-start)

    try:
        while queue:
            if evaluations >= budget.max_candidates:
                raise Cutoff('candidate_limit')
            oi, indices = queue.popleft()
            out, inputs, _ = ops[oi]
            children = [spaces[s].basis[i] for s, i in zip(inputs, indices)]
            value = apply(ops[oi], children, dims)
            evaluations += 1
            bitcheck(value, budget.max_bits)
            child_refs = [refs[s][i] for s,i in zip(inputs, indices)]
            if stop_on_counterexample:
                for ti, (s, q) in enumerate(targets):
                    observed = dot(q, value) if s == out else Q(0)
                    if observed:
                        nodes.append({'op':oi, 'children':child_refs})
                        cert = {'schema':'forge.mlc.certificate.v1',
                                'kind':'counterexample', 'nodes':nodes,
                                'root':len(nodes)-1, 'target':ti,
                                'claimed_value':str(observed)}
                        return {'status':'REFUTED', 'certificate':cert, 'stats':stats()}
            space = spaces[out]
            if space.coordinates(value) is not None:
                continue
            if sum(len(s.basis) for s in spaces.values()) >= budget.max_basis:
                raise Cutoff('basis_limit')
            space.add(value)
            for _, row, combo in space.rows:
                bitcheck(row+combo, budget.max_bits)
            new_index = len(space.basis)-1
            refs[out].append(len(nodes))
            nodes.append({'op':oi, 'children':child_refs})
            for pj, (_, args, _) in enumerate(ops):
                for hole, arg in enumerate(args):
                    if arg != out:
                        continue
                    ranges = [range(len(spaces[s].basis)) for s in args]
                    ranges[hole] = (new_index,)
                    for tup in product(*ranges):
                        enqueue(pj, tup)

        closures = []
        for oi, (out, inputs, _) in enumerate(ops):
            for indices in product(*(range(len(spaces[s].basis)) for s in inputs)):
                value = apply(ops[oi], [spaces[s].basis[i]
                                      for s,i in zip(inputs,indices)], dims)
                c = spaces[out].coordinates(value)
                if c is None:
                    raise AssertionError('internal closure failure')
                bitcheck(c, budget.max_bits)
                closures.append({'op':oi,'children':list(indices),'coeff':encode(c)})
        enclosure = {'basis':{s:[encode(v) for v in sp.basis] for s,sp in spaces.items()},
                     'closures':closures}
        cert = {'schema':'forge.mlc.certificate.v1',
                'kind':'invariant' if stop_on_counterexample else 'enclosure',
                **enclosure}
        return {'status':'PROVED' if stop_on_counterexample else 'CLOSED',
                'certificate':cert, 'stats':stats(),
                'basis_witnesses':{'nodes':nodes,'refs':refs}}
    except Cutoff as e:
        return {'status':'UNKNOWN','reason':str(e),'stats':stats()}

def left_inverse(basis, dimension):
    """Rows L with L B = I, where B has the reachable vectors as columns."""
    rank=len(basis)
    cols=Echelon(rank);pivots=[]
    for j in range(dimension):
        if cols.add(tuple(v[j] for v in basis)):
            pivots.append(j)
    result=[]
    for i in range(rank):
        target=tuple(Q(int(i==j)) for j in range(rank))
        coeff=cols.coordinates(target)
        if coeff is None:raise AssertionError('dependent reachability basis')
        row=[Q(0)]*dimension
        for j,c in zip(pivots,coeff):row[j]=c
        result.append(tuple(row))
    return result

def minimize(problem, budget=Budget()):
    """Reachable linear quotient preserving all listed scalar observations.

    Context search runs in reachable-basis coordinates. Returned quotient
    certificates prove preservation, not minimality; the minimality theorem
    additionally uses the completed context search and independent reach basis.
    """
    full = saturate(problem, budget, stop_on_counterexample=False)
    if full['status'] != 'CLOSED':
        return full
    dims, ops, targets = decode(problem)
    enc = full['certificate']
    basis = {s:[tuple(Q(x) for x in v) for v in bs] for s,bs in enc['basis'].items()}
    ranks = {s:len(bs) for s,bs in basis.items()}
    h = {(c['op'],tuple(c['children'])):tuple(Q(x) for x in c['coeff'])
         for c in enc['closures']}
    cspaces = {s:Echelon(r) for s,r in ranks.items()}
    queue = deque()
    steps = 0

    def admit(s, row):
        bitcheck(row, budget.max_bits)
        if cspaces[s].add(row):
            queue.append((s, tuple(row)))

    try:
        for s,q in targets:
            admit(s, tuple(dot(q,v) for v in basis[s]))
        while queue:
            out,row = queue.popleft()
            for oi,(result,args,_) in enumerate(ops):
                if result != out:
                    continue
                for hole,s in enumerate(args):
                    positions = [j for j in range(len(args)) if j != hole]
                    for others in product(*(range(ranks[args[j]]) for j in positions)):
                        steps += 1
                        if steps > budget.max_candidates:
                            raise Cutoff('context_candidate_limit')
                        idx = [0]*len(args)
                        for j,k in zip(positions,others):
                            idx[j] = k
                        pull = []
                        for k in range(ranks[s]):
                            idx[hole] = k
                            pull.append(dot(row,h[oi,tuple(idx)]))
                        admit(s,tuple(pull))
        C = {s:sp.basis for s,sp in cspaces.items()}
        qdims = {s:len(rows) for s,rows in C.items()}
        R = {}
        for s in dims:
            r, k = ranks[s], qdims[s]
            colspace = Echelon(k)
            pivots = []
            for j in range(r):
                col = tuple(C[s][i][j] for i in range(k))
                if colspace.add(col):
                    pivots.append(j)
            inverse = [[Q(0)]*k for _ in range(r)]
            for i in range(k):
                e = tuple(Q(int(i==j)) for j in range(k))
                co = colspace.coordinates(e)
                if co is None:
                    raise AssertionError('context rows lost independence')
                for j,v in zip(pivots,co):
                    inverse[j][i] = v
            R[s] = inverse

        qops = []
        for oi,(out,args,_) in enumerate(ops):
            terms=[]
            for inds in product(*(range(qdims[s]) for s in args)):
                value=[Q(0)]*ranks[out]
                for old in product(*(range(ranks[s]) for s in args)):
                    scale=Q(1)
                    for s,j,k in zip(args,old,inds):
                        scale*=R[s][j][k]
                    if scale:
                        value=[x+scale*y for x,y in zip(value,h[oi,old])]
                for i,row in enumerate(C[out]):
                    x=dot(row,value)
                    if x:
                        terms.append({'out':i,'in':list(inds),'q':str(x)})
            qops.append({'name':problem['operations'][oi]['name'],
                         'out':out,'inputs':list(args),'terms':terms})
        qtargets=[]
        for s,q in targets:
            a=tuple(dot(q,v) for v in basis[s])
            beta=tuple(sum((a[j]*R[s][j][i] for j in range(ranks[s])),Q(0))
                       for i in range(qdims[s]))
            qtargets.append({'sort':s,'q':encode(beta)})
        qmodel={'schema':'forge.mlc.problem.v1', 'name':problem['name']+'_quotient',
                'sorts':qdims,'operations':qops,'targets':qtargets}
        cert={'schema':'forge.mlc.certificate.v1','kind':'quotient',
              'enclosure':{'basis':enc['basis'],'closures':enc['closures']},
              'maps':{s:[encode(row) for row in C[s]] for s in dims},
              'left_inverses':{s:[encode(row) for row in left_inverse(basis[s],dims[s])] for s in dims},
              'sections':{s:[encode(row) for row in R[s]] for s in dims},
              'model':qmodel}
        return {'status':'QUOTIENT','certificate':cert,
                'stats':{'ambient_dimensions':dims,'reachable_dimensions':ranks,
                         'quotient_dimensions':qdims,'context_candidates':steps}}
    except Cutoff as e:
        return {'status':'UNKNOWN','reason':str(e)}
