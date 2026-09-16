"""Deterministic examples and seeded model generators for the experiments."""
from __future__ import annotations
from copy import deepcopy
import random


def mutex(bug: bool = False) -> dict:
    # lock, active A, active B, waiting A, waiting B
    enter_b = [0 if bug else 1, 0, 0, 0, 1]
    edges = [([1,0,0,1,0], [0,1,0,0,0]), ([0,1,0,0,0], [1,0,0,1,0]),
             (enter_b, [0,0,1,0,0]), ([0,0,1,0,0], [1,0,0,0,1])]
    return {'dimension':5, 'controls':1,
            'initials':[{'control':0, 'base':[1,0,0,0,0], 'rays':[[0,0,0,1,0],[0,0,0,0,1]]}],
            'transitions':[{'src':0,'dst':0,'consume':a,'produce':b} for a,b in edges],
            'bad':[{'control':0,'vector':[0,1,1,0,0]}]}


def axes() -> dict:
    return {'dimension':2, 'controls':1,
            'initials':[{'control':0,'base':[1,0],'rays':[[1,0]]},
                        {'control':0,'base':[0,1],'rays':[[0,1]]}],
            'transitions':[{'src':0,'dst':0,'consume':[1,0],'produce':[2,0]},
                           {'src':0,'dst':0,'consume':[0,1],'produce':[0,2]}],
            'bad':[{'control':0,'vector':[1,1]}]}


def delayed(length: int = 101) -> dict:
    return {'dimension':1,'controls':1,'initials':[{'control':0,'base':[0],'rays':[]}],
            'transitions':[{'src':0,'dst':0,'consume':[0],'produce':[1]}],
            'bad':[{'control':0,'vector':[length]}]}


def enabling_trap() -> dict:
    return {'dimension':1,'controls':2,'initials':[{'control':0,'base':[0],'rays':[]}],
            'transitions':[{'src':0,'dst':1,'consume':[1],'produce':[1]}],
            'bad':[{'control':1,'vector':[0]}]}


def lru(fifo: bool = False, atom_output: bool = False) -> dict:
    hit0 = ['eq',['input'],['reg',0]]
    hit1 = ['eq',['input'],['reg',1]]
    keep = [['reg',0],['reg',1]]
    move = [['input'],['reg',0]]
    if atom_output:
        outputs = [['atom',['null']],['atom',['null']],['atom',['reg',1]]]
    else:
        outputs = [['bool',True],['bool',True],['bool',False]]
    return {'registers':2,'constants':0,'controls':1,'tags':['request'],
            'initial_control':0,'initial_registers':[None,None],
            'rules':[{'src':0,'dst':0,'tag':'request','guard':g,'update':u,'output':o}
                     for g,u,o in [(hit0,keep,outputs[0]), (hit1,keep if fifo else move,outputs[1]),
                                   (True,move,outputs[2])]]}


def permute_registers(machine: dict, permutation: list[int]) -> dict:
    """Old register i is stored in new register permutation[i]."""
    assert sorted(permutation) == list(range(machine['registers']))
    result = deepcopy(machine)
    def rewrite(e):
        if not isinstance(e,list): return e
        if e and e[0] == 'reg': return ['reg',permutation[e[1]]]
        return [rewrite(x) for x in e]
    regs = [None] * len(permutation)
    for i, value in enumerate(machine['initial_registers']): regs[permutation[i]] = value
    result['initial_registers'] = regs
    for old, new in zip(machine['rules'],result['rules']):
        new['guard'] = rewrite(old['guard'])
        new['output'] = rewrite(old['output'])
        updated = [None] * len(permutation)
        for i, e in enumerate(old['update']): updated[permutation[i]] = rewrite(e)
        new['update'] = updated
    return result


def constant_detector() -> dict:
    return {'registers':0,'constants':1,'controls':1,'tags':['request'],
            'initial_control':0,'initial_registers':[],
            'rules':[{'src':0,'dst':0,'tag':'request','guard':True,'update':[],
                      'output':['bool',['eq',['input'],['const',0]]]}]}


def owner_pool(bug: bool = False) -> dict:
    # counters: free lock, active leases, arbitrary waiting requests
    return {'registers':1,'constants':0,'controls':1,'tags':['acquire','release'],
            'initial_control':0,'initial_registers':[None], 'dimension':3,
            'initials':[{'control':0,'base':[1,0,0],'rays':[[0,0,1]]}],
            'rules':[
                {'src':0,'dst':0,'tag':'acquire',
                 'guard':['not',['eq',['input'],['reg',0]]], 'update':[['input']],
                 'consume':[0 if bug else 1,0,1],'produce':[0,1,0]},
                {'src':0,'dst':0,'tag':'release',
                 'guard':['eq',['input'],['reg',0]],'update':[['null']],
                 'consume':[0,1,0],'produce':[1,0,1]}],
            'bad':[{'control':0,'guard':True,'vector':[0,2,0]}]}


def composition(n: int, d: int, rng: random.Random) -> list[int]:
    result = [0]*d
    for _ in range(n): result[rng.randrange(d)] += 1
    return result


def random_vass(rng: random.Random) -> dict:
    d, q, mass = rng.randint(1,4), rng.randint(1,3), rng.randint(0,5)
    edges = []
    for _ in range(rng.randint(1,7)):
        weight = rng.randint(0,3)
        edges.append({'src':rng.randrange(q),'dst':rng.randrange(q),
                      'consume':composition(weight,d,rng),'produce':composition(weight,d,rng)})
    return {'dimension':d,'controls':q,
            'initials':[{'control':rng.randrange(q),'base':composition(mass,d,rng),'rays':[]}],
            'transitions':edges,'bad':[{'control':rng.randrange(q),'vector':composition(rng.randint(0,6),d,rng)}]}


def random_machine(rng: random.Random) -> dict:
    k, c, q = rng.randint(0,2), rng.randint(0,1), rng.randint(1,2)
    selectors = [['input'],['null']] + [['reg',i] for i in range(k)] + [['const',i] for i in range(c)]
    def condition():
        if rng.random() < 0.3: return bool(rng.randrange(2))
        return ['eq',deepcopy(rng.choice(selectors)),deepcopy(rng.choice(selectors))]
    def output():
        return ['bool',condition()] if rng.random() < .6 else ['atom',deepcopy(rng.choice(selectors))]
    rules=[]
    for control in range(q):
        for tag in ['a','b']:
            for g in [condition(),True]:
                rules.append({'src':control,'dst':rng.randrange(q),'tag':tag,'guard':g,
                              'update':[deepcopy(rng.choice(selectors)) for _ in range(k)],'output':output()})
    return {'registers':k,'constants':c,'controls':q,'tags':['a','b'],'initial_control':0,
            'initial_registers':[None]*k,'rules':rules}


def random_register_net(rng: random.Random) -> dict:
    k,c,q,d = rng.randint(0,2),rng.randint(0,1),rng.randint(1,2),rng.randint(1,3)
    selectors = [['input'],['null']] + [['reg',i] for i in range(k)] + [['const',i] for i in range(c)]
    rules=[]
    for _ in range(rng.randint(1,6)):
        weight=rng.randint(0,2)
        g = True if rng.random()<.4 else ['eq',deepcopy(rng.choice(selectors)),deepcopy(rng.choice(selectors))]
        rules.append({'src':rng.randrange(q),'dst':rng.randrange(q),'tag':rng.choice(['a','b']),
                      'guard':g,'update':[deepcopy(rng.choice(selectors)) for _ in range(k)],
                      'consume':composition(weight,d,rng),'produce':composition(weight,d,rng)})
    return {'registers':k,'constants':c,'controls':q,'tags':['a','b'],'initial_control':0,
            'initial_registers':[None]*k, 'dimension':d,
            'initials':[{'control':0,'base':composition(rng.randint(0,4),d,rng),'rays':[]}],
            'rules':rules,'bad':[{'control':rng.randrange(q),'guard':True,
                               'vector':composition(rng.randint(0,5),d,rng)}]}
