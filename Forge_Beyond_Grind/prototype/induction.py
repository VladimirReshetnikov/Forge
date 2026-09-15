"""A tiny typed equational prover with checked structural-induction certificates.

This is NOT Lean. It models a transparent fragment: Nat, polymorphic lists,
defining equations, congruence/rewrite chains, and structural induction.
The checker reconstructs the exact base/step goals and only exposes an IH
at the immediate predecessor/tail. Generalized parameters alone may vary.
"""
from __future__ import annotations
from dataclasses import dataclass

SIGNATURE = {
    'nil':((), 'L'), 'cons':(('E','L'),'L'), 'app':(('L','L'),'L'),
    'rev':(('L',),'L'), 'ra':(('L','L'),'L'),
    'z':((),'N'), 's':(('N',),'N'), 'add':(('N','N'),'N'),
    'length':(('L',),'N'), 'la':(('L','N'),'N'),
}

@dataclass(frozen=True)
class Term:
    name: str
    sort: str
    args: tuple['Term',...] = ()
    variable: bool = False

    def __str__(self) -> str:
        return self.name if self.variable or not self.args else self.name+'('+', '.join(map(str,self.args))+')'


def V(name: str, sort: str) -> Term:
    if sort not in ('L','N','E'): raise ValueError('Unknown sort')
    return Term(name,sort,(),True)


def F(name: str,*args: Term) -> Term:
    domain,codomain=SIGNATURE[name]
    if tuple(a.sort for a in args)!=domain: raise ValueError('Ill-sorted application')
    return Term(name,codomain,tuple(args))


def valid(t: Term) -> bool:
    if t.variable:
        return t.sort in ('L','N','E') and not t.args
    if t.name not in SIGNATURE: return False
    ds,s=SIGNATURE[t.name]
    return t.sort==s and tuple(a.sort for a in t.args)==ds and all(valid(a) for a in t.args)


def variables(t: Term) -> dict[str,str]:
    if t.variable: return {t.name:t.sort}
    d={}
    for a in t.args:
        for v,s in variables(a).items():
            if v in d and d[v]!=s: raise ValueError('Variable sort conflict')
            d[v]=s
    return d


def subst(t: Term, env: dict[str,Term]) -> Term:
    if t.variable:
        r=env.get(t.name,t)
        if r.sort!=t.sort: raise ValueError('Ill-sorted substitution')
        return r
    return F(t.name,*(subst(a,env) for a in t.args))


def match(p: Term, t: Term, env: dict[str,Term]) -> bool:
    if p.sort!=t.sort: return False
    if p.variable and p.name.startswith('?'):
        if p.name in env: return env[p.name]==t
        env[p.name]=t
        return True
    if p.name!=t.name or p.variable!=t.variable or len(p.args)!=len(t.args): return False
    return all(match(a,b,env) for a,b in zip(p.args,t.args))

@dataclass(frozen=True)
class Equation:
    name: str
    lhs: Term
    rhs: Term


def defining_equations() -> tuple[Equation,...]:
    x,xs,ys,a,n,m=V('?x','E'),V('?xs','L'),V('?ys','L'),V('?a','L'),V('?n','N'),V('?m','N')
    nil,z=F('nil'),F('z')
    rows=[
        ('app_nil',F('app',nil,ys),ys),
        ('app_cons',F('app',F('cons',x,xs),ys),F('cons',x,F('app',xs,ys))),
        ('rev_nil',F('rev',nil),nil),
        ('rev_cons',F('rev',F('cons',x,xs)),F('app',F('rev',xs),F('cons',x,nil))),
        ('ra_nil',F('ra',nil,a),a),
        ('ra_cons',F('ra',F('cons',x,xs),a),F('ra',xs,F('cons',x,a))),
        ('add_zero',F('add',z,m),m),
        ('add_succ',F('add',F('s',n),m),F('s',F('add',n,m))),
        ('length_nil',F('length',nil),z),
        ('length_cons',F('length',F('cons',x,xs)),F('s',F('length',xs))),
        ('la_nil',F('la',nil,n),n),
        ('la_cons',F('la',F('cons',x,xs),n),F('la',xs,F('s',n))),
    ]
    return tuple(Equation(*r) for r in rows)

@dataclass(frozen=True)
class Step:
    path: tuple[int,...]
    rule: str
    after: Term

@dataclass(frozen=True)
class EqualityProof:
    left: tuple[Step,...]
    right: tuple[Step,...]

@dataclass(frozen=True)
class InductionProof:
    subject: str
    generalize: tuple[str,...]
    base: EqualityProof
    step: EqualityProof


def at(t: Term, path: tuple[int,...]) -> Term:
    for i in path:
        if type(i) is not int or i<0 or i>=len(t.args): raise ValueError('Bad path')
        t=t.args[i]
    return t


def replace(t: Term,path: tuple[int,...],r: Term) -> Term:
    if not path:
        if t.sort!=r.sort: raise ValueError('Sort changed by rewrite')
        return r
    i,*tail=path
    if type(i) is not int or not 0<=i<len(t.args): raise ValueError('Bad path')
    args=list(t.args)
    args[i]=replace(args[i],tuple(tail),r)
    return F(t.name,*args)


def positions(t: Term):
    # Innermost normalization; exact paths are stored for replay.
    for i,a in enumerate(t.args):
        for p in positions(a): yield (i,)+p
    yield ()


def normalize(t: Term,rules: tuple[Equation,...],limit: int=300) -> tuple[Term,tuple[Step,...]]:
    out=[]
    seen={t}
    for _ in range(limit):
        chosen=None
        for path in positions(t):
            s=at(t,path)
            for rule in rules:
                env={}
                if match(rule.lhs,s,env):
                    r=replace(t,path,subst(rule.rhs,env))
                    if r!=t:
                        chosen=(r,Step(path,rule.name,r))
                        break
            if chosen: break
        if not chosen: return t,tuple(out)
        t,step=chosen
        if t in seen: return t,tuple(out+[step])
        seen.add(t)
        out.append(step)
    return t,tuple(out)


def prove_equality(lhs: Term,rhs: Term,rules: tuple[Equation,...]) -> EqualityProof|None:
    l,lp=normalize(lhs,rules)
    r,rp=normalize(rhs,rules)
    return EqualityProof(lp,rp) if l==r else None


def check_equality(lhs: Term,rhs: Term,proof: EqualityProof,rules: tuple[Equation,...]) -> bool:
    try:
        table={r.name:r for r in rules}
        if len(table)!=len(rules) or not valid(lhs) or not valid(rhs) or lhs.sort!=rhs.sort: return False
        ends=[]
        for start,steps in ((lhs,proof.left),(rhs,proof.right)):
            t=start
            for step in steps:
                rule=table.get(step.rule)
                if rule is None or not valid(step.after): return False
                env={}
                if not match(rule.lhs,at(t,step.path),env): return False
                expected=replace(t,step.path,subst(rule.rhs,env))
                if expected!=step.after: return False
                t=step.after
            ends.append(t)
        return ends[0]==ends[1]
    except (ValueError,TypeError,KeyError,IndexError,AttributeError): return False


def induction_goals(eq: Equation,subject: str,gen: tuple[str,...]):
    vs=variables(eq.lhs)
    for v,s in variables(eq.rhs).items():
        if v in vs and vs[v]!=s: raise ValueError('Sort conflict')
        vs[v]=s
    if any(v.startswith(('?','$')) for v in vs): raise ValueError('Reserved variable namespace')
    if subject not in vs or vs[subject] not in ('L','N'): raise ValueError('Bad induction subject')
    if len(set(gen))!=len(gen) or any(v not in vs or v==subject for v in gen): raise ValueError('Bad generalization')
    tail=V('$tail',vs[subject])
    if vs[subject]=='L': zero,successor=F('nil'),F('cons',V('$head','E'),tail)
    else: zero,successor=F('z'),F('s',tail)
    base=(subst(eq.lhs,{subject:zero}),subst(eq.rhs,{subject:zero}))
    step=(subst(eq.lhs,{subject:successor}),subst(eq.rhs,{subject:successor}))
    env={subject:tail,**{v:V('?'+v,vs[v]) for v in gen}}
    ih=Equation('$ih',subst(eq.lhs,env),subst(eq.rhs,env))
    return base,step,ih


def changing_parameters(eq: Equation,subject: str) -> tuple[str,...]:
    """Read recursive defining equations, detect changed nonrecursive arguments.
    Prototype scopes: first argument structurally recursive; no dependent types.
    """
    found=set()
    for path in positions(eq.lhs):
        t=at(eq.lhs,path)
        if not t.args or t.args[0]!=V(subject,'L'): continue
        for d in defining_equations():
            if d.lhs.name!=t.name or len(d.lhs.args)!=len(t.args): continue
            if not d.lhs.args[0].args: continue
            for rp in positions(d.rhs):
                call=at(d.rhs,rp)
                if call.name!=t.name or len(call.args)!=len(t.args): continue
                for i in range(1,len(t.args)):
                    if call.args[i]!=d.lhs.args[i]:
                        found.update(variables(t.args[i]))
    found.discard(subject)
    return tuple(sorted(found))

class Kernel:
    """Accepted lemmas can only be installed through checked induction proofs."""
    def __init__(self):
        self._lemmas: list[Equation]=[]

    @property
    def rules(self) -> tuple[Equation,...]:
        return defining_equations()+tuple(self._lemmas)

    def check(self,eq: Equation,proof: InductionProof) -> bool:
        try:
            b,s,ih=induction_goals(eq,proof.subject,proof.generalize)
            return check_equality(*b,proof.base,self.rules) and check_equality(*s,proof.step,self.rules+(ih,))
        except (ValueError,TypeError,AttributeError): return False

    def install(self,eq: Equation,proof: InductionProof) -> None:
        if eq.name in {r.name for r in self.rules} or eq.name.startswith('$'):
            raise ValueError('Duplicate/reserved theorem name')
        if not self.check(eq,proof): raise ValueError('Rejected induction proof')
        vs=variables(eq.lhs)|variables(eq.rhs)
        env={v:V('?'+v,s) for v,s in vs.items()}
        self._lemmas.append(Equation(eq.name,subst(eq.lhs,env),subst(eq.rhs,env)))


def prove_induction(kernel: Kernel,eq: Equation,subject: str,*,generalization: bool=True) -> InductionProof|None:
    gen=changing_parameters(eq,subject) if generalization else ()
    b,s,ih=induction_goals(eq,subject,gen)
    bp=prove_equality(*b,kernel.rules)
    sp=prove_equality(*s,kernel.rules+(ih,))
    if bp is None or sp is None: return None
    p=InductionProof(subject,gen,bp,sp)
    return p if kernel.check(eq,p) else None


def examples() -> list[tuple[Equation,str]]:
    xs,ys,zs,a=map(lambda s:V(s,'L'),('xs','ys','zs','a'))
    n,m=V('n','N'),V('m','N')
    nil,z=F('nil'),F('z')
    return [
        (Equation('append_right_identity',F('app',xs,nil),xs),'xs'),
        (Equation('append_associativity',F('app',F('app',xs,ys),zs),F('app',xs,F('app',ys,zs))),'xs'),
        (Equation('add_right_zero',F('add',n,z),n),'n'),
        (Equation('add_right_successor',F('add',n,F('s',m)),F('s',F('add',n,m))),'n'),
        (Equation('reverse_append',F('rev',F('app',xs,ys)),F('app',F('rev',ys),F('rev',xs))),'xs'),
        (Equation('reverse_involution',F('rev',F('rev',xs)),xs),'xs'),
        (Equation('reverse_accumulator',F('ra',xs,a),F('app',F('rev',xs),a)),'xs'),
        (Equation('length_accumulator',F('la',xs,n),F('add',F('length',xs),n)),'xs'),
    ]


def proof_json(p: InductionProof) -> dict:
    def st(s): return {'path':list(s.path),'rule':s.rule,'after':str(s.after)}
    def ep(e): return {'left':[st(s) for s in e.left],'right':[st(s) for s in e.right]}
    return {'subject':p.subject,'generalize':list(p.generalize),'base':ep(p.base),'step':ep(p.step)}
