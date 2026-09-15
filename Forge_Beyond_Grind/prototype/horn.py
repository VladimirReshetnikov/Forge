"""Finite ground-Horn demand slicing + indexed forward chaining.

Not an E-matcher or a model of stock grind. The ablation isolates one useful
relevance idea and includes index construction in total-work accounting.
"""
from __future__ import annotations
from collections import defaultdict, deque
from dataclasses import dataclass
from time import perf_counter

@dataclass(frozen=True)
class Rule:
    name: str
    premises: tuple[str,...]
    conclusion: str

@dataclass(frozen=True)
class Proof:
    # Topologically ordered applications. Input facts are not proof nodes.
    applications: tuple[tuple[int,str],...]


def check(facts: frozenset[str],rules: tuple[Rule,...],target: str,proof: Proof) -> bool:
    known=set(facts)
    try:
        for i,c in proof.applications:
            if type(i) is not int or not 0<=i<len(rules): return False
            r=rules[i]
            if c!=r.conclusion or any(p not in known for p in r.premises): return False
            known.add(c)
        return target in known
    except (TypeError,ValueError,AttributeError): return False


def solve(facts: frozenset[str],rules: tuple[Rule,...],target: str,*,demand: bool,
          budget: int=1000000) -> tuple[Proof|None,dict]:
    t=perf_counter()
    by_head=defaultdict(list)
    for i,r in enumerate(rules): by_head[r.conclusion].append(i)
    active=set(range(len(rules)))
    if demand:
        active=set()
        needed={target}
        queue=deque([target])
        while queue:
            h=queue.popleft()
            for i in by_head[h]:
                if i in active: continue
                active.add(i)
                for p in rules[i].premises:
                    if p not in needed:
                        needed.add(p)
                        queue.append(p)
    index_seconds=perf_counter()-t
    ts=perf_counter()
    waiting=defaultdict(list)
    remaining={}
    queue=deque(sorted(facts))
    known=set(facts)
    reasons={}
    scanned=0
    ready=deque()
    for i in sorted(active):
        remaining[i]=len(set(rules[i].premises))
        if not remaining[i]: ready.append(i)
        for p in set(rules[i].premises): waiting[p].append(i)
    fired=0
    exhausted=False
    while (queue or ready) and target not in known:
        if ready:
            i=ready.popleft()
            if fired>=budget:
                exhausted=True
                break
            fired+=1
            c=rules[i].conclusion
            if c not in known:
                known.add(c)
                reasons[c]=i
                queue.append(c)
        else:
            p=queue.popleft()
            for i in waiting[p]:
                scanned+=1
                remaining[i]-=1
                if remaining[i]==0: ready.append(i)
    stats={'input_rules':len(rules),'index_rule_visits':len(rules),'active_rules':len(active),
           'rule_firings':fired,'premise_notifications':scanned,
           'index_seconds':index_seconds,'search_seconds':perf_counter()-ts,
           'status':'unknown_budget' if exhausted else 'unknown'}
    if target not in known: return None,stats
    nodes=[]
    seen=set(facts)
    def extract(c):
        if c in seen: return
        i=reasons[c]
        for p in rules[i].premises: extract(p)
        seen.add(c)
        nodes.append((i,c))
    extract(target)
    proof=Proof(tuple(nodes))
    if not check(facts,rules,target,proof): raise RuntimeError('Internal proof replay failure')
    stats.update(status='checked_python',proof_nodes=len(nodes))
    return proof,stats


def chain_problem(length: int,decoys: int):
    if length<1 or decoys<0: raise ValueError('Bad problem size')
    # Decoy rules intentionally precede the useful chain: an adversarial workload.
    rs=[Rule(f'junk{j}',('p0',),f'junk{j}') for j in range(decoys)]
    rs += [Rule(f'chain{i}',(f'p{i}',),f'p{i+1}') for i in range(length)]
    return frozenset({'p0'}),tuple(rs),f'p{length}'
