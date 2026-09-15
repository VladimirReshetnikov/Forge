"""Degree-bounded descending invariant spaces with exact ideal preimages.

Search uses SymPy; a tracked Buchberger implementation extracts multipliers.
No search result is a Lean proof. Resource cutoffs raise BudgetExceeded.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import combinations
import sympy as s
from .encode import polynomial

class BudgetExceeded(RuntimeError):
    pass

@dataclass
class Limits:
    max_pairs: int = 20000
    max_terms: int = 30000
    max_basis: int = 512
    max_rounds: int = 512

class TrackedGB:
    def __init__(self, generators, variables, limits=None):
        self.x = tuple(variables)
        self.orig = [s.expand(f) for f in generators]
        self.limits = limits or Limits()
        self.g = []
        self.reps = []
        self.pairs_processed = 0
        for i, f in enumerate(self.orig):
            q, rem = self.divide(f)
            rep = [s.Integer(int(i == j)) for j in range(len(self.orig))]
            for a, basisrep in zip(q, self.reps):
                rep = [s.expand(v-a*w) for v,w in zip(rep,basisrep)]
            self._append(rem, rep)
        todo = list(combinations(range(len(self.g)),2))
        pos = 0
        while pos < len(todo):
            if pos >= self.limits.max_pairs:
                raise BudgetExceeded('Groebner pair budget')
            i,j = todo[pos]; pos += 1
            self.pairs_processed += 1
            ei, _ = self._lead(self.g[i]); ej, _ = self._lead(self.g[j])
            e = tuple(max(a,b) for a,b in zip(ei,ej))
            a = self._mon(tuple(t-u for t,u in zip(e,ei)))
            b = self._mon(tuple(t-u for t,u in zip(e,ej)))
            f = s.expand(a*self.g[i]-b*self.g[j])
            rep = [s.expand(a*v-b*w) for v,w in zip(self.reps[i],self.reps[j])]
            q, rem = self.divide(f)
            for c, basisrep in zip(q,self.reps):
                rep = [s.expand(v-c*w) for v,w in zip(rep,basisrep)]
            old = len(self.g)
            if self._append(rem,rep):
                todo.extend((i,old) for i in range(old))

    def _mon(self, e):
        return s.prod(x**a for x,a in zip(self.x,e))

    def _lead(self, f):
        p = s.Poly(f,*self.x,domain=s.QQ)
        if len(p.terms()) > self.limits.max_terms:
            raise BudgetExceeded('polynomial term budget')
        return p.terms()[0]

    def _append(self, f, rep):
        f = s.expand(f)
        if f == 0:
            return False
        if len(self.g) >= self.limits.max_basis:
            raise BudgetExceeded('Groebner basis budget')
        _,lc = self._lead(f)
        self.g.append(s.expand(f/lc))
        self.reps.append([s.expand(v/lc) for v in rep])
        return True

    def divide(self,f):
        f = s.expand(f); rem = s.Integer(0)
        q = [s.Integer(0)]*len(self.g)
        steps = 0
        while f != 0:
            steps += 1
            if steps > self.limits.max_terms:
                raise BudgetExceeded('division step budget')
            e,c = self._lead(f)
            for i,g in enumerate(self.g):
                eg,cg = self._lead(g)
                if all(a >= b for a,b in zip(e,eg)):
                    term = c/cg*self._mon(tuple(a-b for a,b in zip(e,eg)))
                    q[i] = s.expand(q[i]+term)
                    f = s.expand(f-term*g)
                    break
            else:
                term = c*self._mon(e)
                rem += term; f = s.expand(f-term)
        return q,s.expand(rem)

    def normal(self,f):
        return self.divide(f)[1]

    def lift(self,f):
        q,rem = self.divide(f)
        if rem != 0:
            return None
        return [s.expand(sum((a*rep[j] for a,rep in zip(q,self.reps)),s.Integer(0)))
                for j in range(len(self.orig))]

def null_combinations(columns, images, codomains):
    """Kernel of several polynomial linear maps, columns indexed by basis."""
    count = len(columns)
    rows = []
    for block, variables in zip(images,codomains):
        dicts=[]
        for p in block:
            if variables:
                d = dict(s.Poly(s.expand(p),*variables,domain=s.QQ).terms())
            else:
                d = {():s.Rational(p)}
            dicts.append(d)
        monoms = sorted(set().union(*(set(d) for d in dicts)))
        rows.extend([[d.get(m,0) for d in dicts] for m in monoms])
    a = s.Matrix(rows) if rows else s.zeros(0,count)
    return [s.expand(sum((c*p for c,p in zip(v,columns)),s.Integer(0))) for v in a.nullspace()]

def substitute(p,variables,images):
    return s.expand(p.subs(dict(zip(variables,images)), simultaneous=True))

def discover(variables, initial, transitions, goal, degree=2, limits=None):
    """initial: [(parameter_symbols, polynomial_coordinate_list)].
    transitions: [(update_coordinate_list, equality_guard_list)].
    """
    limits = limits or Limits()
    x = tuple(variables)
    v = sorted(s.itermonomials(x,degree), key=lambda p:(s.total_degree(p), str(p)))
    if len(v) > limits.max_basis:
        raise BudgetExceeded('candidate dimension budget')
    images = [[substitute(p,x,ims) for p in v] for _,ims in initial]
    v = null_combinations(v,images,[params for params,_ in initial])
    dimensions=[len(v)]
    pairs=0
    for _ in range(limits.max_rounds):
        if not v:
            break
        blocks=[]
        for ims,guards in transitions:
            gb=TrackedGB(v+list(guards),x,limits); pairs += gb.pairs_processed
            blocks.append([gb.normal(substitute(p,x,ims)) for p in v])
        nv = null_combinations(v,blocks,[x]*len(blocks))
        dimensions.append(len(nv))
        stable = len(nv) == len(v)
        v = nv
        if stable:
            break
    else:
        raise BudgetExceeded('fixed-point round budget')
    gb = TrackedGB(v,x,limits); pairs += gb.pairs_processed
    target = gb.lift(goal)
    if target is None:
        return None, {'dimensions':dimensions,'invariants':[str(p) for p in v], 'reason':'target_not_in_fixed_point_ideal'}
    steps=[]
    for ims,guards in transitions:
        gb=TrackedGB(v+list(guards),x,limits); pairs += gb.pairs_processed
        step=[]
        for p in v:
            coeff=gb.lift(substitute(p,x,ims))
            if coeff is None:
                raise AssertionError('fixed-point extraction disagreement')
            step.append([polynomial(c,x) for c in coeff])
        steps.append(step)
    problem={
      'kind':'inductive_ideal_problem_v1','dimension':len(x),
      'initial':[{'parameters':len(params),'values':[polynomial(p,params) for p in ims]} for params,ims in initial],
      'transitions':[{'update':[polynomial(p,x) for p in ims],'guards':[polynomial(g,x) for g in guards]} for ims,guards in transitions],
      'goal':polynomial(goal,x)}
    cert={'kind':'inductive_ideal_v1','invariants':[polynomial(p,x) for p in v],
          'steps':steps,'goal_multipliers':[polynomial(p,x) for p in target]}
    return (problem,cert), {'dimensions':dimensions,'invariants':[str(p) for p in v], 'groebner_pairs':pairs}

def conserved_dimension(variables, initial, transitions, degree):
    x=tuple(variables)
    v=sorted(s.itermonomials(x,degree),key=str)
    images=[[substitute(p,x,ims) for p in v] for _,ims in initial]
    domains=[params for params,_ in initial]
    # Deliberately restricted comparator: exact global conservation on each edge.
    for ims,_ in transitions:
        images.append([substitute(p,x,ims)-p for p in v]); domains.append(x)
    return len(null_combinations(v,images,domains))
