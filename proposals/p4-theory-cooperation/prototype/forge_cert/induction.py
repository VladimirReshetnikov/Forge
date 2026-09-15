"""Typed list-equation induction planner and explicit proof-trace checker.

This is a small object logic, not Lean. All successful proofs consist of
constructor-complete induction plus checked instances of defining equations,
previously checked lemmas, and a correctly restricted induction hypothesis.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import product
from typing import Iterable

SIG = {'nil': ((), 'L'), 'cons': (('E','L'), 'L'),
       'app': (('L','L'), 'L'), 'rev': (('L',), 'L'), 'qrev': (('L','L'), 'L')}

@dataclass(frozen=True)
class Term:
    op: str
    args: tuple['Term', ...] = ()
    sort: str = 'L'
    def __str__(self):
        return self.op if not self.args else self.op+'('+','.join(map(str,self.args))+')'

def V(name, sort='L'):
    return Term('$'+name, (), sort)

def F(op, *args):
    ins, out = SIG[op]
    if tuple(a.sort for a in args) != ins:
        raise ValueError('ill-typed application')
    return Term(op, tuple(args), out)

def vars_of(t):
    if t.op.startswith('$'):
        return {t.op: t.sort}
    out = {}
    for a in t.args:
        for k, v in vars_of(a).items():
            if k in out and out[k] != v:
                raise ValueError('inconsistent variable sort')
            out[k] = v
    return out

def subst(t, env):
    if t.op.startswith('$'):
        return env.get(t.op, t)
    return F(t.op, *(subst(a,env) for a in t.args))

def serial(t):
    return [t.op, t.sort, [serial(a) for a in t.args]]

def parse(t):
    op, sort, args = t
    if op.startswith('$'):
        if args or sort not in ('L','E'):
            raise ValueError('bad variable')
        return Term(op, (), sort)
    v = F(op, *(parse(a) for a in args))
    if v.sort != sort:
        raise ValueError('bad result sort')
    return v

@dataclass(frozen=True)
class Rule:
    name: str
    lhs: Term
    rhs: Term
    flexible: frozenset[str]

def rule(name, lhs, rhs, flexible=None):
    if lhs.sort != rhs.sort or not vars_of(rhs).keys() <= vars_of(lhs).keys():
        raise ValueError('invalid oriented equation')
    return Rule(name,lhs,rhs,frozenset(vars_of(lhs) if flexible is None else flexible))

x,y,z = V('x'),V('y'),V('z')
h,t,a = V('h','E'),V('t'),V('a')
N = F('nil')
DEFS = [rule('app_nil',F('app',N,y),y),
        rule('app_cons',F('app',F('cons',h,t),y),F('cons',h,F('app',t,y))),
        rule('rev_nil',F('rev',N),N),
        rule('rev_cons',F('rev',F('cons',h,t)),F('app',F('rev',t),F('cons',h,N))),
        rule('qrev_nil',F('qrev',N,a),a),
        rule('qrev_cons',F('qrev',F('cons',h,t),a),F('qrev',t,F('cons',h,a)))]

def match(p,t,allowed,env):
    if p.op in allowed:
        if p.sort != t.sort or (p.op in env and env[p.op] != t):
            return False
        env[p.op] = t
        return True
    return p.op == t.op and p.sort == t.sort and len(p.args)==len(t.args) and all(
        match(a,b,allowed,env) for a,b in zip(p.args,t.args))

def positions(t, path=()):
    for i,a in enumerate(t.args):
        yield from positions(a,path+(i,))
    yield path,t

def replace(t,path,value):
    if not path:
        if t.sort != value.sort:
            raise ValueError('sort mismatch')
        return value
    i,*rest = path
    if type(i) is not int or i < 0 or i >= len(t.args):
        raise ValueError('bad position')
    args = list(t.args); args[i] = replace(args[i],rest,value)
    return F(t.op,*args)

def normalize(t,rules,limit=1000):
    trace=[]
    for _ in range(limit):
        step=None
        for path,sub in positions(t):
            for r in rules:
                env={}
                if match(r.lhs,sub,r.flexible,env):
                    v=subst(r.rhs,env)
                    if v != sub:
                        step=(path,r,env,v);break
            if step:break
        if step is None:
            return t,trace
        path,r,env,v=step
        trace.append({'path':list(path),'rule':r.name,
                      'subst':{k:serial(v) for k,v in sorted(env.items())}})
        t=replace(t,path,v)
    return None,trace

def mutation_positions():
    """Read recursive definitions to identify modified nonrecursive arguments."""
    out={}
    for r in DEFS:
        op=r.lhs.op
        for _,call in positions(r.rhs):
            if call.op==op:
                for i,(before,after) in enumerate(zip(r.lhs.args,call.args)):
                    if before.op.startswith('$') and before != after:
                        out.setdefault(op,set()).add(i)
    return out

def suggest_generalization(lhs,rhs,induct):
    mut=mutation_positions();out=set()
    for term in (lhs,rhs):
        for _,call in positions(term):
            for i in mut.get(call.op,()):
                out.update(vars_of(call.args[i]))
    return sorted(out-{induct})

def branches(lhs,rhs,induct,generalized):
    vs=vars_of(lhs)|vars_of(rhs)
    if vs.get(induct) != 'L' or not set(generalized)<=vs.keys()-{induct}:
        raise ValueError('invalid induction/generalization')
    head,tail=V('_head','E'),V('_tail')
    if head.op in vs or tail.op in vs:
        raise ValueError('reserved fresh-name collision')
    base=(subst(lhs,{induct:N}),subst(rhs,{induct:N}))
    env={induct:F('cons',head,tail)}
    step=(subst(lhs,env),subst(rhs,env))
    ih=rule('IH',subst(lhs,{induct:tail}),subst(rhs,{induct:tail}),generalized)
    return base,step,ih

def prove(lhs,rhs,lemmas=(),induct='$x',generalize=True):
    generalized=suggest_generalization(lhs,rhs,induct) if generalize else []
    base,step,ih=branches(lhs,rhs,induct,generalized)
    rules=DEFS+list(lemmas)
    cert={'induct':induct,'generalized':generalized,'branches':[]}
    for (l,r),rs in ((base,rules),(step,rules+[ih])):
        ln,lt=normalize(l,rs);rn,rt=normalize(r,rs)
        if ln is None or rn is None or ln!=rn:
            return None
        cert['branches'].append({'left':lt,'right':rt})
    return cert

def replay(start,trace,rules):
    """Checker does not search or normalize: check the supplied substitutions."""
    table={r.name:r for r in rules};current=start
    if len(table)!=len(rules):
        raise ValueError('duplicate rule name')
    for s in trace:
        r=table[s['rule']]
        env={k:parse(v) for k,v in s['subst'].items()}
        if set(env) != set(r.flexible):
            raise ValueError('illegal or missing instantiation')
        expected_sorts=vars_of(r.lhs)
        if any(env[k].sort != expected_sorts[k] for k in env):
            raise ValueError('bad instantiation sort')
        focus=current
        for i in s['path']:
            if type(i) is not int or not 0<=i<len(focus.args):
                raise ValueError('bad path')
            focus=focus.args[i]
        if focus != subst(r.lhs,env):
            raise ValueError('left side mismatch')
        current=replace(current,s['path'],subst(r.rhs,env))
    return current

def verify(lhs,rhs,cert,lemmas=()):
    """Prior lemmas must themselves have been verified in an acyclic registry."""
    try:
        base,step,ih=branches(lhs,rhs,cert['induct'],cert['generalized'])
        if len(cert['branches']) != 2:
            return False
        for (l,r),b,rs in zip((base,step),cert['branches'],
                              (DEFS+list(lemmas),DEFS+list(lemmas)+[ih])):
            if replay(l,b['left'],rs)!=replay(r,b['right'],rs):
                return False
        return True
    except (ValueError,KeyError,IndexError,TypeError,RecursionError):
        return False

def eval_term(t,env):
    if t.op.startswith('$'):return env[t.op]
    args=[eval_term(a,env) for a in t.args]
    if t.op=='nil':return ()
    if t.op=='cons':return (args[0],)+args[1]
    if t.op=='app':return args[0]+args[1]
    if t.op=='rev':return args[0][::-1]
    if t.op=='qrev':return args[0][::-1]+args[1]
    raise ValueError('unknown function')

def sampled_counterexample(lhs,rhs):
    vs=vars_of(lhs)|vars_of(rhs)
    names=sorted(vs)
    lists=[(),(0,),(1,),(0,1)]
    choices=[lists if vs[v]=='L' else [0,1] for v in names]
    for vals in product(*choices):
        env=dict(zip(names,vals))
        if eval_term(lhs,env)!=eval_term(rhs,env):return env
    return None

def candidate_lemmas():
    """Generate identity/associativity schemas from the function signature."""
    for op,(ins,out) in SIG.items():
        if ins==('L','L') and out=='L':
            yield op+'_right_id',F(op,x,N),x
            yield op+'_assoc',F(op,F(op,x,y),z),F(op,x,F(op,y,z))
    # Unary reversal/append anti-homomorphism is an additional explicit schema.
    yield 'rev_app',F('rev',F('app',x,y)),F('app',F('rev',y),F('rev',x))

def synthesize_lemmas():
    verified=[];records=[]
    for name,lhs,rhs in candidate_lemmas():
        ce=sampled_counterexample(lhs,rhs)
        if ce is not None:
            records.append({'name':name,'status':'rejected_by_counterexample'});continue
        cert=prove(lhs,rhs,verified)
        if cert is None:
            records.append({'name':name,'status':'unknown'});continue
        if not verify(lhs,rhs,cert,verified):raise AssertionError('bad generated proof')
        verified.append(rule(name,lhs,rhs))
        records.append({'name':name,'status':'proved','lhs':serial(lhs),'rhs':serial(rhs),'certificate':cert})
    return verified,records

def verify_bundle(records, required=()):
    """Replay a topologically ordered lemma/theorem bundle from definitions only.

    Only proved entries are admitted; each entry can use earlier entries, never
    itself or later conjectures. Names of definitions and the local IH are reserved.
    Every name in required must actually be proved, not merely listed as a conjecture.
    """
    checked=[]; names={r.name for r in DEFS}|{'IH'}
    try:
        for rec in records:
            if rec['status']!='proved':
                continue
            name=rec['name']
            if not isinstance(name,str) or name in names:
                return False
            lhs,rhs=parse(rec['lhs']),parse(rec['rhs'])
            lv,rv=vars_of(lhs),vars_of(rhs)
            if lhs.sort!=rhs.sort or any(lv[k]!=rv[k] for k in lv.keys()&rv.keys()):
                return False
            if not verify(lhs,rhs,rec['certificate'],checked):
                return False
            checked.append(rule(name,lhs,rhs));names.add(name)
        return set(required) <= {r.name for r in checked}
    except (KeyError,ValueError,TypeError,IndexError,RecursionError):
        return False
