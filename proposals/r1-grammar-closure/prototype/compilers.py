"""Small source frontends, not a Lean Expr reifier.

CFG source semantics uses column-state execution:
M(a1...an) = M(an)...M(a1). A production's child occurrences are independent.
The checker interprets the original source rather than trusting these tensors.
"""
from fractions import Fraction as Q
from itertools import product

def term(o, ids, q):
    return {'out':o,'in':list(ids),'q':str(Q(q))}

def matrix_multiply(a,b):
    n=len(a)
    return [[sum((a[i][k]*b[k][j] for k in range(n)),Q(0))
             for j in range(n)] for i in range(n)]

def cfg(name, sorts, matrices, rules, targets):
    n=len(next(iter(matrices.values())))
    matrices={k:[[Q(v) for v in row] for row in m] for k,m in matrices.items()}
    def interpret(rhs,children):
        state=[[Q(int(i==j)) for j in range(n)] for i in range(n)]
        child=iter(children)
        for token in rhs:
            if token.startswith('t:'):
                part=matrices[token[2:]]
            else:
                v=next(child)
                part=[list(v[i*n:(i+1)*n]) for i in range(n)]
            state=matrix_multiply(part,state)
        return [x for row in state for x in row]
    ops=[]
    for oi,rule in enumerate(rules):
        args=[x[2:] for x in rule['rhs'] if x.startswith('n:')]
        entries=[]
        for indices in product(range(n*n),repeat=len(args)):
            children=[tuple(Q(int(i==j)) for j in range(n*n)) for i in indices]
            value=interpret(rule['rhs'],children)
            for o,q in enumerate(value):
                if q:
                    entries.append(term(o,indices,q))
        ops.append({'name':f'rule_{oi}','out':rule['lhs'],
                    'inputs':args,'terms':entries})
    return {'schema':'forge.mlc.problem.v1','name':name,
            'sorts':{s:n*n for s in sorts},'operations':ops,'targets':targets,
            'source':{'kind':'cfg','dimension':n,
                      'matrices':{k:[[str(v) for v in row] for row in m]
                                  for k,m in matrices.items()},'rules':rules}}

def multiaffine(name, raw_dimensions, operations, targets):
    """Each raw output is a list {q, factors:[[child-slot,coordinate],...] }.

    Repeated child slots in one monomial are rejected, even when coordinates
    differ. Affine omissions are homogenized with that child's coordinate 0.
    """
    ops=[]
    for op in operations:
        args=op['inputs']
        acc={}
        def add(o,inds,c):
            key=(o,tuple(inds));acc[key]=acc.get(key,Q(0))+c
        add(0,[0]*len(args),Q(1))
        if len(op['polynomials']) != raw_dimensions[op['out']]:
            raise ValueError('raw output dimension')
        for o,p in enumerate(op['polynomials'],start=1):
            for monomial in p:
                inds=[0]*len(args)
                used=set()
                for slot,coordinate in monomial['factors']:
                    if slot in used:
                        raise ValueError('non-multiaffine: repeated child slot')
                    if not 0 <= slot < len(args) or not 0 <= coordinate < raw_dimensions[args[slot]]:
                        raise ValueError('invalid source coordinate')
                    used.add(slot);inds[slot]=coordinate+1
                add(o,inds,Q(monomial['q']))
        terms=[term(o,inds,q) for (o,inds),q in sorted(acc.items()) if q]
        ops.append({'name':op['name'],'out':op['out'],'inputs':args,'terms':terms})
    return {'schema':'forge.mlc.problem.v1','name':name,
            'sorts':{s:d+1 for s,d in raw_dimensions.items()},
            'operations':ops,'targets':targets,
            'source':{'kind':'multiaffine','raw_dimensions':raw_dimensions,
                      'operations':operations}}

def monomial(q, *factors):
    return {'q':str(Q(q)),'factors':[list(f) for f in factors]}

def leaf_count(noise=False):
    if not noise:
        operations=[{'name':'leaf','out':'T','inputs':[],
                     'polynomials':[[monomial(1)],[]]},
                    {'name':'node','out':'T','inputs':['T','T'],
                     'polynomials':[[monomial(1,(0,0)),monomial(1,(1,0))],
                                    [monomial(1),monomial(1,(0,1)),monomial(1,(1,1))]]}]
        return multiaffine('leaf_count',{'T':2},operations,
                          [{'sort':'T','q':['-1','1','-1']}])
    operations=[]
    for x in range(3):
        operations.append({'name':f'leaf{x}','out':'T','inputs':[],
                           'polynomials':[[monomial(1)],[],[monomial(x)],[]]})
    operations.append({'name':'node','out':'T','inputs':['T','T'],
      'polynomials':[[monomial(1,(0,0)),monomial(1,(1,0))],
                     [monomial(1),monomial(1,(0,1)),monomial(1,(1,1))],
                     [monomial(1,(0,2)),monomial(1,(1,2))],
                     [monomial(1,(0,3)),monomial(1,(1,3)),monomial(1,(0,2),(1,2))]]})
    return multiaffine('observable_leaf_count_with_noise',{'T':4},operations,
                      [{'sort':'T','q':['0','1','0','0','0']}])

def dyck(perturb=False):
    # a = translation +1, b = -1. Every balanced word is identity.
    mats={'a':[[1,1],[0,1]],'b':[[1,-1 if not perturb else 0],[0,1]]}
    rules=[{'lhs':'S','rhs':[]},
           {'lhs':'S','rhs':['t:a','n:S','t:b']},
           {'lhs':'S','rhs':['n:S','n:S']}]
    return cfg('dyck_bad_return' if perturb else 'dyck_translation', ['S'],mats,rules,
               [{'sort':'S','q':['0','1','0','0']}])

def noncommuting_control():
    # Sole word ab: under column-state order its matrix is B*A, not A*B.
    return cfg('noncommuting_order',['S'],
               {'a':[[1,1],[0,1]],'b':[[1,0],[1,1]]},
               [{'lhs':'S','rhs':['t:a','t:b']}],
               [{'sort':'S','q':['1','0','0','-1']}])

def exponential_word(depth=60):
    sorts=[f'N{i}' for i in range(depth+1)]
    rules=[{'lhs':'N0','rhs':['t:a']}]+[
        {'lhs':f'N{i}','rhs':[f'n:N{i-1}',f'n:N{i-1}']} for i in range(1,depth+1)]
    return cfg(f'exponential_word_{depth}',sorts,{'a':[[1]]},rules,
               [{'sort':f'N{depth}','q':['1']}])
