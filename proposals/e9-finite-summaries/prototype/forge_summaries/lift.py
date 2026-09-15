"""Polynomial observation lifting for affine state updates (search-side only).

SymPy checks substitution identities over QQ. This is NOT a Lean reifier.
The returned matrices describe the supplied symbolic expressions, not arbitrary
Lean source. A production adapter needs kernel-checked correspondence proofs.
"""
from fractions import Fraction as Q
from itertools import product
import sympy as s

def _q(x):
    x=s.Rational(x); return Q(int(x.p),int(x.q))

def compile_lift(state,initial,transitions,observer,degree,input_symbol=None):
    if len(state)!=len(initial) or degree<0: raise ValueError('lift shape')
    exps=sorted((e for e in product(range(degree+1),repeat=len(state)) if sum(e)<=degree),
                key=lambda e:(sum(e),e))
    mons=[s.prod(z**i for z,i in zip(state,e)) for e in exps]
    index={e:i for i,e in enumerate(exps)}; d=len(mons); tables=[]; D=0
    for update in transitions:
        if len(update)!=len(state): raise ValueError('update arity')
        # State degree must be affine, although coefficients may depend on input.
        if any(s.Poly(t,*state).total_degree()>1 for t in update): raise ValueError('non-affine update')
        table=[[s.Integer(0) for _ in range(d)] for _ in range(d)]
        for j,m in enumerate(mons):
            expr=s.expand(m.subs(dict(zip(state,update)),simultaneous=True))
            for e,c in s.Poly(expr,*state).terms():
                if not c: continue
                if e not in index: raise ValueError('degree growth')
                table[index[e]][j]=c
                if input_symbol is None:
                    _q(c)
                else:
                    pc=s.Poly(c,input_symbol)
                    if not pc.is_zero: D=max(D,pc.degree())
            assert s.expand(expr-sum(mons[i]*table[i][j] for i in range(d)))==0
        tables.append(table)
    obs=[Q(0)]*d
    for e,c in s.Poly(s.expand(observer),*state).terms():
        if not c: continue
        if e not in index: raise ValueError('observer degree')
        obs[index[e]]=_q(c)
    u=[_q(m.subs(dict(zip(state,initial)),simultaneous=True)) for m in mons]
    if input_symbol is None:
        matrices=[[[ _q(c) for c in row] for row in t] for t in tables]
    else:
        if len(tables)!=1: raise ValueError('parametric adapter supports one update schema')
        matrices=[[[ _q(s.Poly(c,input_symbol).nth(h)) for c in row] for row in tables[0]] for h in range(D+1)]
    return u,matrices,obs,{'state_dimension':len(state),'observation_degree':degree,
                          'lift_dimension':d,'input_degree':D,'monomials':[str(m) for m in mons]}
