"""Demand-driven tabled Horn search and a fair forward comparison engine.

Scope: one-sorted first-order terms, exact syntactic matching, head-covering
Horn rules, explicit term-depth/fact bounds. There is no Lean elaboration,
unification modulo equality, or higher-order reasoning in this prototype.
"""
from __future__ import annotations
from collections import defaultdict,deque
from dataclasses import dataclass
from itertools import product

@dataclass(frozen=True,order=True)
class Term:
    symbol: str
    args: tuple['Term',...]=()
    def __post_init__(self):
        if not self.symbol or (self.symbol.startswith('?') and self.args):
            raise ValueError('variables must be leaves')
    @property
    def variable(self): return self.symbol.startswith('?')
    @property
    def depth(self): return 0 if not self.args else 1+max(t.depth for t in self.args)
    def variables(self):
        return {self.symbol} if self.variable else set().union(*(t.variables() for t in self.args))
    def subst(self,s):
        if self.variable: return s.get(self.symbol,self)
        return Term(self.symbol,tuple(t.subst(s) for t in self.args))
    def text(self): return self.symbol if not self.args else f"{self.symbol}({','.join(a.text() for a in self.args)})"

@dataclass(frozen=True,order=True)
class Atom:
    predicate: str
    args: tuple[Term,...]
    def variables(self): return set().union(*(a.variables() for a in self.args))
    @property
    def depth(self): return max((a.depth for a in self.args),default=0)
    def subst(self,s): return Atom(self.predicate,tuple(a.subst(s) for a in self.args))
    def text(self): return f"{self.predicate}({','.join(a.text() for a in self.args)})"

@dataclass(frozen=True)
class Rule:
    name: str
    head: Atom
    body: tuple[Atom,...]
    def __post_init__(self):
        if not set().union(*(p.variables() for p in self.body)) <= self.head.variables():
            raise ValueError('prototype requires all body variables to occur in the head')


def match_term(pattern: Term,ground: Term,s: dict) -> bool:
    if pattern.variable:
        if pattern.symbol in s: return s[pattern.symbol]==ground
        s[pattern.symbol]=ground; return True
    return (pattern.symbol==ground.symbol and len(pattern.args)==len(ground.args)
            and all(match_term(p,g,s) for p,g in zip(pattern.args,ground.args)))


def match_atom(pattern: Atom,ground: Atom,subst=None) -> dict | None:
    s=dict(subst or {})
    if (pattern.predicate!=ground.predicate or len(pattern.args)!=len(ground.args)
            or not all(match_term(p,g,s) for p,g in zip(pattern.args,ground.args))):
        return None
    return s

@dataclass(frozen=True)
class ProofNode:
    conclusion: Atom
    rule: int | None
    substitution: tuple[tuple[str,Term],...]=()
    premises: tuple[int,...]=()

@dataclass(frozen=True)
class HornCertificate:
    nodes: tuple[ProofNode,...]
    root: int


def check_horn(facts: tuple[Atom,...],rules: tuple[Rule,...],goal: Atom,c: HornCertificate) -> bool:
    """Validate only ground instances and an acyclic proof DAG; no search calls."""
    try:
        if goal.variables() or any(f.variables() for f in facts): return False
        if type(c.root) is not int or not 0<=c.root<len(c.nodes): return False
        factset=set(facts)
        for i,node in enumerate(c.nodes):
            if node.conclusion.variables(): return False
            if node.rule is None:
                if node.substitution or node.premises or node.conclusion not in factset: return False
                continue
            if type(node.rule) is not int or not 0<=node.rule<len(rules): return False
            rule=rules[node.rule]
            keys=[k for k,_ in node.substitution]
            if len(keys)!=len(set(keys)) or set(keys)!=rule.head.variables(): return False
            s=dict(node.substitution)
            if any(v.variables() for v in s.values()): return False
            if rule.head.subst(s)!=node.conclusion or len(node.premises)!=len(rule.body): return False
            for prem,j in zip(rule.body,node.premises):
                if type(j) is not int or not 0<=j<i or prem.subst(s)!=c.nodes[j].conclusion: return False
        return c.nodes[c.root].conclusion==goal
    except (ValueError,TypeError,IndexError,AttributeError):
        return False


def trim(nodes:list[ProofNode],root:int) -> HornCertificate:
    used=set(); todo=[root]
    while todo:
        i=todo.pop()
        if i not in used:
            used.add(i); todo.extend(nodes[i].premises)
    order=sorted(used); mapping={old:new for new,old in enumerate(order)}
    new=tuple(ProofNode(nodes[i].conclusion,nodes[i].rule,nodes[i].substitution,
                        tuple(mapping[j] for j in nodes[i].premises)) for i in order)
    return HornCertificate(new,mapping[root])

@dataclass
class HornResult:
    status: str
    certificate: HornCertificate | None
    terms_or_facts: int
    instances: int
    reason: str=''


def demand_prove(facts: tuple[Atom,...],rules: tuple[Rule,...],goal: Atom,
                 *,max_depth:int=40,max_demands:int=100000) -> HornResult:
    if goal.variables() or any(f.variables() for f in facts): raise ValueError('ground input required')
    demands=set(); queue=deque([goal]); instances=[]; limited=False
    by_head=defaultdict(list)
    for j,r in enumerate(rules): by_head[r.head.predicate].append((j,r))
    while queue:
        a=queue.popleft()
        if a in demands: continue
        if a.depth>max_depth or len(demands)>=max_demands:
            limited=True; continue
        demands.add(a)
        if a in facts: continue  # no need to expand proved base facts
        for j,r in by_head[a.predicate]:
            s=match_atom(r.head,a)
            if s is None: continue
            body=tuple(p.subst(s) for p in r.body)
            instances.append((a,j,tuple(sorted(s.items())),body))
            queue.extend(body)
    # Tabled fixed point, not DFS cycle-as-failure. A cycle alone never proves a fact.
    nodes=[]; proved={}; waiters=defaultdict(list); remaining=[]; done=deque()
    for f in facts:
        if f in demands and f not in proved:
            proved[f]=len(nodes); nodes.append(ProofNode(f,None)); done.append(f)
    for idx,(_,_,_,body) in enumerate(instances):
        pending=set(body)-proved.keys(); remaining.append(pending)
        for p in pending: waiters[p].append(idx)
    ready=deque(i for i,p in enumerate(remaining) if not p)
    while ready or done:
        while ready:
            k=ready.popleft(); a,j,s,body=instances[k]
            if a not in proved and all(p in proved for p in body):
                proved[a]=len(nodes)
                nodes.append(ProofNode(a,j,s,tuple(proved[p] for p in body))); done.append(a)
        if done:
            f=done.popleft()
            for k in waiters[f]:
                remaining[k].discard(f)
                if not remaining[k]: ready.append(k)
    if goal in proved:
        cert=trim(nodes,proved[goal])
        assert check_horn(facts,rules,goal,cert)
        return HornResult('proved',cert,len(demands),len(instances))
    return HornResult('unknown',None,len(demands),len(instances),
                      'demand budget reached' if limited else 'demand closure has no proof')


def forward_prove(facts:tuple[Atom,...],rules:tuple[Rule,...],goal:Atom,
                  *,max_depth:int=40,max_facts:int=100000) -> HornResult:
    """Fair agenda-based semi-naive forward chaining, with body joins."""
    if goal.variables() or any(f.variables() for f in facts): raise ValueError('ground input required')
    nodes=[]; known={}; index=defaultdict(list); queue=deque(); fired=set()
    for f in facts:
        if f not in known:
            known[f]=len(nodes); nodes.append(ProofNode(f,None)); index[f.predicate].append(f); queue.append(f)
    if goal in known: return HornResult('proved',trim(nodes,known[goal]),len(known),0)
    # Ground empty-body clauses are seeded; universally quantified empty-body
    # rules require term enumeration and are outside this forward implementation.
    for j,r in enumerate(rules):
        if not r.body and not r.head.variables() and r.head not in known:
            known[r.head]=len(nodes); nodes.append(ProofNode(r.head,j)); index[r.head.predicate].append(r.head); queue.append(r.head)
    instances=0; limited=False
    while queue:
        newest=queue.popleft()
        for j,r in enumerate(rules):
            for selected,pattern in enumerate(r.body):
                s=match_atom(pattern,newest)
                if s is None: continue
                states=[(s,{selected:newest})]
                for k,p in enumerate(r.body):
                    if k==selected: continue
                    nxt=[]
                    for subst,used in states:
                        for f in index[p.predicate]:
                            ns=match_atom(p,f,subst)
                            if ns is not None: nxt.append((ns,{**used,k:f}))
                    states=nxt
                for s,used in states:
                    head=r.head.subst(s)
                    if head.variables(): continue
                    key=(j,tuple(sorted(s.items())))
                    if key in fired: continue
                    fired.add(key); instances+=1
                    if head in known: continue
                    if head.depth>max_depth or len(known)>=max_facts:
                        limited=True; continue
                    known[head]=len(nodes)
                    nodes.append(ProofNode(head,j,key[1],tuple(known[used[k]] for k in range(len(r.body)))))
                    index[head.predicate].append(head); queue.append(head)
                    if head==goal:
                        cert=trim(nodes,known[head]); assert check_horn(facts,rules,goal,cert)
                        return HornResult('proved',cert,len(known),instances)
    return HornResult('unknown',None,len(known),instances,
                      'fact/depth budget reached' if limited else 'saturated without proof')
