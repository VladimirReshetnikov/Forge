"""Compile an accepted extrema schedule to a hash-consed real-expression DAG.

The checker fixes the reconstruction rule. No untrusted proposed program is
substituted for that rule. This is not a Lean source-expression reifier.
"""
from fractions import Fraction as F
from .wire import q
from .poly_check import check,parse

def compile_witness(problem,cert):
    if cert.get('kind')!='proved' or not check(problem,cert):
        raise ValueError('A checked positive projection certificate is required')
    n,p=problem['variables'],problem['parameters']; nodes=[]; keys={}
    def node(k,*a):
        key=(k,*a)
        if key not in keys: keys[key]=len(nodes); nodes.append(list(key))
        return keys[key]
    def const(c): return node('const',str(c))
    def scale(c,x):
        return const(F(0)) if c==0 else x if c==1 else node('scale',str(c),x)
    def add(a,b): return node('add',a,b)
    def fold(k,xs):
        if not xs: raise ValueError('Empty extremum')
        x=xs[0]
        for y in xs[1:]: x=node(k,x,y)
        return x
    rs=[parse(r,n) for r in problem['target']]; history=[]
    for st in cert['steps']:
        history.append((st['var'],rs))
        rs=[parse(o['row'],n) for o in st['outputs']]
    env={i:node('param',i) for i in range(p)}
    for v,rs in reversed(history):
        lo=[];hi=[]; strict=any(s and a[v] for a,s in rs)
        for a,_ in rs:
            if not a[v]: continue
            z=const(-a[-1]/a[v])
            for k,c in enumerate(a[:-1]):
                if k!=v and c:
                    if k not in env: raise ValueError('Escaped dependency')
                    z=add(z,scale(-c/a[v],env[k]))
            (lo if a[v]>0 else hi).append(z)
        l=fold('max',lo) if lo else None
        u=fold('min',hi) if hi else None
        if strict:
            z=scale(F(1,2),add(l,u)) if lo and hi else add(l,const(F(1))) if lo else add(u,const(F(-1))) if hi else const(F(0))
        else: z=l if lo else u if hi else const(F(0))
        env[v]=z
    return {'nodes':nodes,'outputs':[env[v] for v in range(p,n)]}

def evaluate(dag,parameters):
    vals=[]
    for t in dag['nodes']:
        k=t[0]
        if k=='const': z=q(t[1])
        elif k=='param': z=q(parameters[t[1]])
        elif k=='scale': z=q(t[1])*vals[t[2]]
        elif k=='add': z=vals[t[1]]+vals[t[2]]
        elif k=='max': z=max(vals[t[1]],vals[t[2]])
        elif k=='min': z=min(vals[t[1]],vals[t[2]])
        else: raise ValueError('DAG node')
        vals.append(z)
    return [vals[i] for i in dag['outputs']]

def lean_expression(dag):
    """Diagnostic Lean-style term; uncompiled, and not an acceptance receipt."""
    def rat(s):
        r=q(s)
        return f'({r.numerator} : Real)' if r.denominator==1 else f'(({r.numerator} : Real) / {r.denominator})'
    lines=[]
    for i,t in enumerate(dag['nodes']):
        k=t[0]
        if k=='const': s=rat(t[1])
        elif k=='param': s=f'x{t[1]}'
        elif k=='scale': s=f'{rat(t[1])} * t{t[2]}'
        elif k=='add': s=f't{t[1]} + t{t[2]}'
        else: s=f'{k} t{t[1]} t{t[2]}'
        lines.append(f'let t{i} : Real := {s};')
    outputs=', '.join(f't{i}' for i in dag['outputs'])
    lines.append(outputs if len(dag['outputs'])==1 else f'({outputs})')
    return '\n'.join(lines)
