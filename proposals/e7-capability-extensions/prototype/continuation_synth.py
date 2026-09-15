"""A typed, finite-fragment prototype of continuation-local fold synthesis.

The Church eliminator is primitive in this small calculus; there is no claim
of general System F, dependent, or Lean universe inference. Elimination-spine
carrier discovery, local hole enumeration, reconstruction, and type checking
are executable. Local constraints come from the supplied indexing equations,
not from the type alone. End-to-end tests use actual Church encodings of lists.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import product
from typing import Any

@dataclass(frozen=True)
class Ty:
    tag: str
    args: tuple['Ty',...]=()

INT=Ty('Int'); ELEM=Ty('A')
def arrow(a,b): return Ty('arrow',(a,b))
def church_type(a): return Ty('Church',(a,))

@dataclass(frozen=True)
class E:
    op: str
    args: tuple=()

def V(name): return E('var',(name,))
def lam(name,ty,body): return E('lam',(name,ty,body))
def app(f,x): return E('app',(f,x))
def shift(i,c): return E('shift',(i,c))
def case(i,a,b,c): return E('case',(i,a,b,c))


def infer(e:E,ctx:dict[str,Ty])->Ty:
    if e.op=='var':
        if e.args[0] not in ctx:
            raise TypeError('escaped or unknown lexical binder')
        return ctx[e.args[0]]
    if e.op=='lam':
        name,t,body=e.args
        if name in ctx:
            raise TypeError('binder IDs must be globally fresh, not display names')
        return arrow(t,infer(body,ctx|{name:t}))
    if e.op=='app':
        f,x=e.args; ft=infer(f,ctx); xt=infer(x,ctx)
        if ft.tag!='arrow' or ft.args[0]!=xt:
            raise TypeError('application type mismatch')
        return ft.args[1]
    if e.op=='shift':
        i,c=e.args
        if infer(i,ctx)!=INT or type(c)is not int:
            raise TypeError('shift requires an integer')
        return INT
    if e.op=='case':
        i,neg,zero,pos=e.args
        if infer(i,ctx)!=INT:
            raise TypeError('guard is not Int')
        a,b,c=(infer(x,ctx) for x in (neg,zero,pos))
        if not a==b==c:
            raise TypeError('branch types differ')
        return a
    if e.op=='fold':
        xs,r,step,base=e.args; xt=infer(xs,ctx)
        if xt.tag!='Church':
            raise TypeError('not a Church eliminator')
        a=xt.args[0]
        if infer(step,ctx)!=arrow(a,arrow(r,r)) or infer(base,ctx)!=r:
            raise TypeError('ill-typed fold algebra')
        return r
    raise TypeError('unknown constructor')


def evaluate(e:E,env:dict[str,Any]):
    if e.op=='var': return env[e.args[0]]
    if e.op=='lam':
        name,_,body=e.args
        return lambda x:evaluate(body,env|{name:x})
    if e.op=='app': return evaluate(e.args[0],env)(evaluate(e.args[1],env))
    if e.op=='shift': return evaluate(e.args[0],env)+e.args[1]
    if e.op=='case':
        i,neg,zero,pos=e.args; z=evaluate(i,env)
        return evaluate(neg if z<0 else zero if z==0 else pos,env)
    if e.op=='fold':
        xs,_,step,base=e.args
        return evaluate(xs,env)(evaluate(step,env))(evaluate(base,env))
    raise ValueError('unknown expression')


def encode_list(xs):
    """An actual Church value, curried like the typed eliminator."""
    def with_step(step):
        def with_base(base):
            z=base
            for a in reversed(xs): z=step(a)(z)
            return z
        return with_base
    return with_step


def carrier_from_elimination_spine(result:Ty, arguments:list[Ty])->Ty:
    r=result
    for a in reversed(arguments): r=arrow(a,r)
    return r


def pretty(e):
    if e.op=='var': return e.args[0]
    if e.op=='lam': return f'(fun {e.args[0]} => {pretty(e.args[2])})'
    if e.op=='app': return f'({pretty(e.args[0])} {pretty(e.args[1])})'
    if e.op=='shift':
        c=e.args[1]
        return f'({pretty(e.args[0])} {"+" if c>=0 else "-"} {abs(c)})'
    if e.op=='case':
        i,a,b,c=map(pretty,e.args)
        return f'(if {i} < 0 then {a} else if {i} = 0 then {b} else {c})'
    if e.op=='fold':
        xs,r,step,base=e.args
        return f'({pretty(xs)} [Int -> A] {pretty(step)} {pretty(base)})'
    raise ValueError(e.op)


def grammar(noise:int):
    if not 0<=noise<=64: raise ValueError('noise limit')
    ctx={'default':ELEM,'outerIndex':INT,'input':church_type(ELEM)}
    ctx|={f'noise{j}':ELEM for j in range(noise)}
    # Unhelpful terms are deliberately early for *both* comparison policies.
    ns=[V(f'noise{j}') for j in range(noise)]
    base=ns+[V('default')]
    atom=ns+[V('head'),V('default')]
    pos=atom+[app(V('tailFn'),shift(V('localIndex'),c)) for c in (2,1,0,-2,-3,-1)]
    return ctx,[base,atom,atom,pos]


def build(parts):
    b,n,z,p=parts
    r=carrier_from_elimination_spine(ELEM,[INT])
    step=lam('head',ELEM,lam('tailFn',r,lam('localIndex',INT,
               case(V('localIndex'),n,z,p))))
    base=lam('baseIndex',INT,b)
    return app(E('fold',(V('input'),r,step,base)),V('outerIndex'))


def local_world(noise,index):
    return {'default':('default',),'head':('head',),'localIndex':index,
            'outerIndex':99,'input':encode_list([('irrelevant',)]),
            'tailFn':lambda j:('tail-at',j),
            **{f'noise{j}':('noise',j) for j in range(noise)}}


def local_passes(hole,e,noise):
    # These local conditions are the base/constructor contract for the chosen
    # sketch. TailFn is tested as an opaque function, not replaced by a guess.
    ids=range(-3,0) if hole==1 else (0,) if hole==2 else (1,2,5) if hole==3 else (0,)
    for i in ids:
        got=evaluate(e,local_world(noise,i))
        want=('default',) if hole in (0,1) else ('head',) if hole==2 else ('tail-at',i-1)
        if got!=want: return False
    return True


def training_passes(term,noise):
    d=('default',); a,b,c=('head0',),('head1',),('head2',)
    examples=[([],0,d),([a],-1,d),([a],0,a),([a,b,c],1,b),([a,b,c],2,c),([a],3,d)]
    for xs,i,want in examples:
        env={'default':d,'outerIndex':i,'input':encode_list(xs),
             **{f'noise{j}':('noise',j) for j in range(noise)}}
        if evaluate(term,env)!=want: return False
    return True


def synthesize(noise:int,local:bool,cap:int|None=None):
    ctx,holes=grammar(noise); built=0; local_checks=0
    candidates=holes
    if local:
        candidates=[]
        for i,hs in enumerate(holes):
            kept=[]
            for e in hs:
                local_checks+=1
                if local_passes(i,e,noise): kept.append(e)
            candidates.append(kept)
    for parts in product(*candidates):
        if cap is not None and built>=cap:
            return None,dict(status='truncated',complete_candidates=built,
                             local_component_checks=local_checks)
        term=build(parts)
        if infer(term,ctx)!=ELEM: raise AssertionError('generated invalid term')
        built+=1
        if training_passes(term,noise):
            return term,dict(status='found',complete_candidates=built,
                             local_component_checks=local_checks,
                             grammar_sizes=[len(h) for h in holes])
    return None,dict(status='unknown',complete_candidates=built,
                     local_component_checks=local_checks)


def reference_index(default,xs,index):
    # Independent non-fold reference. The function is total on mathematical Int.
    return xs[index] if 0<=index<len(xs) else default


def execute(term,default,xs,index,noise):
    return evaluate(term,{'default':default,'input':encode_list(xs),'outerIndex':index,
                **{f'noise{j}':('noise',j) for j in range(noise)}})


def encode_type(t):
    return {'tag':t.tag,'args':[encode_type(a) for a in t.args]}


def encode_term(e):
    """Transport only; acceptance is in replay.check_church_index."""
    if e.op=='var': return {'op':'var','id':e.args[0]}
    if e.op=='lam':
        x,t,b=e.args
        return {'op':'lam','id':x,'type':encode_type(t),'body':encode_term(b)}
    if e.op=='app': return {'op':'app','fn':encode_term(e.args[0]),'arg':encode_term(e.args[1])}
    if e.op=='shift': return {'op':'shift','arg':encode_term(e.args[0]),'offset':e.args[1]}
    if e.op=='case':
        return dict(op='intcase',**dict(zip(('index','negative','zero','positive'),map(encode_term,e.args))))
    if e.op=='fold':
        xs,r,s,b=e.args
        return {'op':'fold','input':encode_term(xs),'carrier':encode_type(r),
                'step':encode_term(s),'base':encode_term(b)}
    raise ValueError('unserializable term')


def certificate(term,noise):
    problem={'name':f'church_index_noise_{noise}',
             'semantics':'encoded-finite-list-index-v1',
             'default':'default','input':'input','index':'outerIndex',
             'irrelevant_element_binders':[f'noise{j}' for j in range(noise)]}
    return {'problem':problem,'certificate':{'kind':'church-index-v1','term':encode_term(term)}}
