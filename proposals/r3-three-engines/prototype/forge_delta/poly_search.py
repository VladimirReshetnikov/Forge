"""Exact constructive Fourier--Motzkin search with local projection receipts.

Rows encode a[0]*x[0]+...+a[-2]*x[-1]+a[-1] >= 0 (or > 0).
The target is forall parameters, domain -> exists outputs, target.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from typing import Sequence
from .wire import q, qs

class BudgetExceeded(Exception):
    pass

@dataclass(frozen=True)
class Row:
    a: tuple[F, ...]
    strict: bool = False
    def wire(self):
        return {'a': list(map(str, self.a)), 'strict': self.strict}

def row(a: Sequence, strict: bool = False) -> dict:
    return Row(tuple(map(q, a)), strict).wire()

def read(r):
    return Row(tuple(map(q, r['a'])), r['strict'])

def norm(r):
    scale = 1 / next((abs(t) for t in r.a if t), F(1))
    return Row(tuple(scale*t for t in r.a), r.strict), scale

def dot(a, x):
    return a[-1] + sum((c*t for c,t in zip(a[:-1], x)), F(0))

def holds(r, x):
    v = dot(r.a, x)
    return v > 0 if r.strict else v >= 0

def project_step(rows: list[Row], var: int, limit: int = 5000):
    pos = [i for i,r in enumerate(rows) if r.a[var] > 0]
    neg = [i for i,r in enumerate(rows) if r.a[var] < 0]
    zero = [i for i,r in enumerate(rows) if not r.a[var]]
    if len(pos)*len(neg) + len(zero) > limit:
        raise BudgetExceeded('Projection pair budget')
    out, weights, obligations, index = [], [], [], {}
    def emit(w, label):
        a = tuple(sum((w[i]*rows[i].a[k] for i in range(len(rows))), F(0))
                  for k in range(len(rows[0].a)))
        s = any(w[i] > 0 and rows[i].strict for i in range(len(rows)))
        rr, scale = norm(Row(a,s))
        if rr not in index:
            index[rr] = len(out)
            out.append(rr)
            weights.append([str(scale*t) for t in w])
        obligations.append({**label, 'out': index[rr]})
    for i in zero:
        w = [F(0)]*len(rows); w[i] = F(1)
        emit(w, {'kind':'zero','i':i})
    for i in pos:
        for j in neg:
            w = [F(0)]*len(rows)
            w[i],w[j] = 1/rows[i].a[var], -1/rows[j].a[var]
            emit(w, {'kind':'pair','i':i,'j':j})
    return out, {'var':var,
                 'outputs':[{'row':r.wire(),'weights':w} for r,w in zip(out,weights)],
                 'required':obligations}

def choose(rows: list[Row], var: int, assignment: list[F]):
    lo,hi = [],[]
    strict = any(r.strict and r.a[var] for r in rows)
    for r in rows:
        a = r.a[var]
        if a:
            b = r.a[-1] + sum((r.a[k]*assignment[k]
                       for k in range(len(assignment)) if k != var), F(0))
            (lo if a > 0 else hi).append(-b/a)
    if not strict:
        return max(lo) if lo else min(hi) if hi else F(0)
    if lo and hi:
        return (max(lo)+min(hi))/2
    return max(lo)+1 if lo else min(hi)-1 if hi else F(0)

def solve(rows: list[Row], n: int, limit: int = 5000):
    """Return exact model or a nonnegative contradiction combination."""
    original = rows
    origins = [[F(int(i==j)) for j in range(len(rows))] for i in range(len(rows))]
    history = []
    for v in reversed(range(n)):
        for r,w in zip(rows,origins):
            if not any(r.a[:-1]) and (r.a[-1] < 0 or r.strict and r.a[-1] == 0):
                return {'unsat':list(map(str,w))}
        history.append((v,rows))
        new,step = project_step(rows,v,limit)
        next_origins = []
        for o in step['outputs']:
            w = list(map(q,o['weights']))
            next_origins.append([sum((w[i]*origins[i][k]
                              for i in range(len(rows))), F(0))
                              for k in range(len(original))])
        rows,origins = new,next_origins
    for r,w in zip(rows,origins):
        if r.a[-1] < 0 or r.strict and r.a[-1] == 0:
            return {'unsat':list(map(str,w))}
    x = [F(0)]*n
    for v,rs in reversed(history):
        x[v] = choose(rs,v,x)
    assert all(holds(r,x) for r in original)
    return {'model':list(map(str,x))}

def prove(problem: dict, limit: int = 5000):
    p,n = problem['parameters'],problem['variables']
    rows = list(map(read,problem['target']))
    domain = list(map(read,problem['domain']))
    steps = []
    try:
        for v in reversed(range(p,n)):
            rows,step = project_step(rows,v,limit)
            steps.append(step)
        receipts = []
        for i,r in enumerate(rows):
            neg = Row(tuple(-a for a in r.a),not r.strict)
            outcome = solve(domain+[neg],n,limit)
            if 'model' in outcome:
                return {'kind':'refuted','steps':steps,'bad_row':i,
                        'parameters':outcome['model'][:p]}
            receipts.append(outcome['unsat'])
        return {'kind':'proved','steps':steps,'domain_proofs':receipts,
                'witness_rule':'extrema-v1'}
    except BudgetExceeded as e:
        return {'kind':'unknown','reason':str(e)}

def witness(problem: dict, cert: dict, parameters: Sequence):
    if cert['kind'] != 'proved':
        raise ValueError('A positive certificate is required')
    p,n = problem['parameters'],problem['variables']
    if len(parameters) != p:
        raise ValueError('Parameter arity')
    rs = list(map(read,problem['target'])); history=[]
    for step in cert['steps']:
        history.append((step['var'],rs))
        rs = [read(o['row']) for o in step['outputs']]
    x = list(map(q,parameters))+[F(0)]*(n-p)
    for v,rs in reversed(history):
        x[v] = choose(rs,v,x)
    return x[p:]
