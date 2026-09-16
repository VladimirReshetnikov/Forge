"""Traced bounded noncommutative completion over rational coefficients.

Every successful search exports a two-sided ideal membership identity.
A nonzero remainder is UNKNOWN, not a refutation in the user's algebra.
"""
from collections import deque
from fractions import Fraction as F
from .wire import q

class BudgetExceeded(Exception): pass

def clean(p): return {w:c for w,c in p.items() if c}

def add(p,r,scale=F(1)):
    out=dict(p)
    for w,c in r.items(): out[w]=out.get(w,F(0))+scale*c
    return clean(out)

def ctx(p,left=(),right=(),scale=F(1)):
    return clean({left+w+right:scale*c for w,c in p.items()})

def mul(p,r):
    out={}
    for u,c in p.items():
        for v,d in r.items():
            out[u+v]=out.get(u+v,F(0))+c*d
    return clean(out)

def power(p,n):
    out={():F(1)}
    for _ in range(n): out=mul(out,p)
    return out

def wire(p):
    return [[list(w),str(c)] for w,c in sorted(p.items(),key=lambda x:(len(x[0]),x[0])) if c]

def read(p): return {tuple(w):q(c) for w,c in p}

def leading(p): return max(p,key=lambda w:(len(w),w))

def receipt_add(a,b,scale=F(1)):
    out=dict(a)
    for k,c in b.items(): out[k]=out.get(k,F(0))+scale*c
    return {k:c for k,c in out.items() if c}

def receipt_ctx(a,l=(),r=(),s=F(1)):
    return {(l+left,i,right+r):c*s for (left,i,right),c in a.items() if c*s}

class Rule:
    def __init__(self,p,proof):
        w=leading(p); c=p[w]
        self.p=ctx(p,scale=1/c)
        self.proof=receipt_ctx(proof,s=1/c)
        self.lead=w

class Engine:
    def __init__(self,relations,max_steps=100_000,max_terms=200_000,max_rules=100):
        self.rules=[Rule(p,{((),i,()):F(1)}) for i,p in enumerate(relations) if p]
        self.steps=0; self.max_steps=max_steps; self.max_terms=max_terms; self.max_rules=max_rules
        self.pairs=0
    def reduce(self,p):
        p=dict(p); used={}
        while True:
            choice=None
            for w in sorted(p,key=lambda w:(len(w),w),reverse=True):
                for rule in self.rules:
                    k=len(rule.lead)
                    for pos in range(len(w)-k+1):
                        if w[pos:pos+k]==rule.lead:
                            choice=w,rule,pos,k; break
                    if choice: break
                if choice: break
            if not choice: return p,used
            w,rule,pos,k=choice; c=p[w]; l,r=w[:pos],w[pos+k:]
            p=add(p,ctx(rule.p,l,r),-c)
            used=receipt_add(used,receipt_ctx(rule.proof,l,r,c))
            self.steps+=1
            if self.steps>self.max_steps or len(p)+len(used)>self.max_terms:
                raise BudgetExceeded('Reduction budget')
    def compositions(self,a,b):
        u,v=a.lead,b.lead
        # Proper overlaps and prefix/suffix cases. Full equal overlap is harmless.
        for k in range(1,min(len(u),len(v))+1):
            if u[-k:]==v[:k]:
                l,r=u[:-k],v[k:]
                yield add(ctx(a.p,right=r),ctx(b.p,left=l),-F(1)),\
                      receipt_add(receipt_ctx(a.proof,r=r),receipt_ctx(b.proof,l=l),-F(1))
        # Inclusion ambiguities, including an empty leading word.
        for pos in range(len(u)-len(v)+1):
            if u[pos:pos+len(v)]==v:
                l,r=u[:pos],u[pos+len(v):]
                yield add(a.p,ctx(b.p,l,r),-F(1)),\
                      receipt_add(a.proof,receipt_ctx(b.proof,l,r),-F(1))
    def search(self,target,complete=True,max_pairs=5000):
        rem,proof=self.reduce(target)
        if not rem: return proof
        if not complete: return None
        queue=deque((i,j) for i in range(len(self.rules)) for j in range(len(self.rules)))
        while queue:
            i,j=queue.popleft()
            for comp,origin in self.compositions(self.rules[i],self.rules[j]):
                self.pairs+=1
                if self.pairs>max_pairs: raise BudgetExceeded('Critical-pair budget')
                rem,used=self.reduce(comp)
                if not rem: continue
                if len(self.rules)>=self.max_rules: raise BudgetExceeded('Rule budget')
                new=Rule(rem,receipt_add(origin,used,-F(1)))
                k=len(self.rules); self.rules.append(new)
                queue.extend((h,k) for h in range(k+1))
                queue.extend((k,h) for h in range(k))
                rem,proof=self.reduce(target)
                if not rem: return proof
        return None

def prove(problem,complete=True,**budgets):
    e=Engine([read(p) for p in problem['relations']],**budgets)
    try:
        c=e.search(read(problem['target']),complete)
        if c is None:
            return {'kind':'unknown','reason':'Nonzero remainder; no model refutation was attempted',
                    'steps':e.steps,'pairs':e.pairs,'rules':len(e.rules)}
        return {'kind':'proved','terms':[
            {'left':list(l),'relation':i,'right':list(r),'coefficient':str(a)}
            for (l,i,r),a in sorted(c.items())],
            'steps':e.steps,'pairs':e.pairs,'rules':len(e.rules)}
    except BudgetExceeded as ex:
        return {'kind':'unknown','reason':str(ex),'steps':e.steps,'pairs':e.pairs,'rules':len(e.rules)}
