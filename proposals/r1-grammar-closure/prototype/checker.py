"""Independent certificate replay: no search, rank test, or third-party library.

Authoritative input is the separately supplied original problem. When present,
CFG or multiaffine source is interpreted here independently of compiler tensors.
A Python acceptance is NOT a Lean proof. Limits are useful bounds, not a claim
of hostile-input hardening (big-integer intermediate allocation is still real).
"""
from __future__ import annotations
from fractions import Fraction
from itertools import product
from math import prod
import json
import sys

class Invalid(ValueError):
    pass

MAX_DIM=256
MAX_ARITY=4
MAX_ITEMS=200000
MAX_BITS=16384
MAX_TEXT=16*1024*1024

def require(condition, message):
    if not condition:
        raise Invalid(message)

def keys(x, required, optional=()):
    require(type(x) is dict, 'expected object')
    require(set(required) <= x.keys() <= set(required)|set(optional), 'object fields')

def integer(x, lower=0, upper=MAX_ITEMS):
    require(type(x) is int and lower <= x <= upper, 'integer bound/type')
    return x

def rational(x):
    require(type(x) is str and len(x) <= 6000, 'rational must be bounded canonical text')
    try:
        q=Fraction(x)
    except (ValueError, ZeroDivisionError):
        raise Invalid('invalid rational') from None
    require(str(q)==x, 'noncanonical rational')
    require(max(q.numerator.bit_length(),q.denominator.bit_length())<=MAX_BITS,
            'rational bit limit')
    return q

def vector(x,n):
    require(type(x) is list and len(x)==n,'vector length')
    return tuple(rational(a) for a in x)

def sequence(x):
    require(type(x) is list and len(x)<=MAX_ITEMS,'list limit/type')
    return x

def name(x):
    require(type(x) is str and 0 < len(x)<=128,'name type/length')
    return x

def decode_problem(p):
    keys(p,('schema','name','sorts','operations','targets'),('source',))
    require(p['schema']=='forge.mlc.problem.v1','problem schema')
    name(p['name'])
    require(type(p['sorts']) is dict and 0<len(p['sorts'])<=MAX_ITEMS,'sorts')
    dims={name(s):integer(d,0,MAX_DIM) for s,d in p['sorts'].items()}
    ops=[]; names=set()
    for op in sequence(p['operations']):
        keys(op,('name','out','inputs','terms'))
        require(name(op['name']) not in names,'duplicate operation name')
        names.add(op['name'])
        out=op['out'];args=sequence(op['inputs'])
        require(out in dims and len(args)<=MAX_ARITY and all(s in dims for s in args),
                'operation signature')
        entries=[];seen=set()
        for e in sequence(op['terms']):
            keys(e,('out','in','q'))
            o=integer(e['out'],0,max(0,dims[out]-1))
            require(o<dims[out],'zero-dimensional output')
            ids=sequence(e['in'])
            require(len(ids)==len(args),'tensor arity')
            for s,j in zip(args,ids):
                integer(j,0,max(0,dims[s]-1));require(j<dims[s],'tensor index')
            key=(o,tuple(ids));require(key not in seen,'duplicate tensor entry');seen.add(key)
            q=rational(e['q']);require(q!=0,'explicit zero tensor entry')
            entries.append((o,tuple(ids),q))
        ops.append({'out':out,'inputs':tuple(args),'terms':entries,'name':op['name']})
    targets=[]
    for t in sequence(p['targets']):
        keys(t,('sort','q'));require(t['sort'] in dims,'target sort')
        targets.append((t['sort'],vector(t['q'],dims[t['sort']])))
    source=p.get('source')
    if source is not None:
        require(type(source) is dict,'source object')
        if source.get('kind')=='cfg':
            keys(source,('kind','dimension','matrices','rules'))
            n=integer(source['dimension'],1,16)
            require(all(d==n*n for d in dims.values()),'CFG summary dimensions')
            require(type(source['matrices']) is dict,'CFG matrices')
            matrices={}
            for k,m in source['matrices'].items():
                name(k);require(type(m) is list and len(m)==n,'matrix height')
                matrices[k]=[vector(row,n) for row in m]
            rules=sequence(source['rules']);require(len(rules)==len(ops),'rule coverage')
            for rule,op in zip(rules,ops):
                keys(rule,('lhs','rhs'));rhs=sequence(rule['rhs'])
                require(rule['lhs']==op['out'],'rule result sort')
                args=[]
                for token in rhs:
                    require(type(token) is str and token[:2] in ('t:','n:'),'CFG token')
                    if token.startswith('t:'):
                        require(token[2:] in matrices,'unknown terminal')
                    else:
                        require(token[2:] in dims,'unknown nonterminal');args.append(token[2:])
                require(tuple(args)==op['inputs'],'CFG child occurrence signature')
            source={'kind':'cfg','dimension':n,'matrices':matrices,'rules':rules}
        elif source.get('kind')=='multiaffine':
            keys(source,('kind','raw_dimensions','operations'))
            raw=source['raw_dimensions']
            require(type(raw) is dict and set(raw)==set(dims),'raw sorts')
            for s,d in raw.items():
                integer(d,0,MAX_DIM-1);require(d+1==dims[s],'homogeneous dimension')
            rawops=sequence(source['operations']);require(len(rawops)==len(ops),'raw op coverage')
            parsed=[]
            for original,op in zip(rawops,ops):
                keys(original,('name','out','inputs','polynomials'))
                require(original['name']==op['name'] and original['out']==op['out'] and
                        tuple(original['inputs'])==op['inputs'],'raw op signature')
                polynomials=sequence(original['polynomials'])
                require(len(polynomials)==raw[op['out']],'raw outputs')
                ps=[]
                for polynomial in polynomials:
                    mons=[]
                    for m in sequence(polynomial):
                        keys(m,('q','factors'));q=rational(m['q']);fs=[];used=set()
                        for factor in sequence(m['factors']):
                            require(type(factor) is list and len(factor)==2,'factor')
                            slot=integer(factor[0],0,max(0,len(op['inputs'])-1))
                            require(slot<len(op['inputs']) and slot not in used,
                                    'repeated/nonexistent child slot')
                            used.add(slot);d=raw[op['inputs'][slot]]
                            coord=integer(factor[1],0,max(0,d-1));require(coord<d,'raw coordinate')
                            fs.append((slot,coord))
                        mons.append((q,tuple(fs)))
                    ps.append(mons)
                parsed.append(ps)
            source={'kind':'multiaffine','polynomials':parsed}
        else:
            raise Invalid('unknown source kind')
    return {'dims':dims,'ops':ops,'targets':targets,'source':source}

def tensor_value(p,oi,children):
    op=p['ops'][oi]
    # Deliberately organize by output coordinate, unlike the producer.
    result=[]
    for output in range(p['dims'][op['out']]):
        summands=[]
        for o,indices,q in op['terms']:
            if o==output:
                summands.append(q*prod((children[k][j] for k,j in enumerate(indices)),
                                      start=Fraction(1)))
        result.append(sum(summands,start=Fraction(0)))
    return tuple(result)

def source_value(p,oi,children):
    source=p['source']
    if source is None:
        return tensor_value(p,oi,children)
    if source['kind']=='multiaffine':
        hom=prod((v[0] for v in children),start=Fraction(1))
        result=[hom]
        for polynomial in source['polynomials'][oi]:
            total=Fraction(0)
            for coefficient,factors in polynomial:
                selected={slot:coord+1 for slot,coord in factors}
                total+=coefficient*prod((v[selected.get(k,0)] for k,v in enumerate(children)),
                                       start=Fraction(1))
            result.append(total)
        return tuple(result)
    n=source['dimension']
    # Interpret column action on EACH initial coordinate vector, not by the
    # producer's matrix product routine. No word expansion occurs.
    columns=[]
    for initial in range(n):
        state=[Fraction(int(i==initial)) for i in range(n)]
        nextchild=0
        for token in source['rules'][oi]['rhs']:
            if token.startswith('t:'):
                m=source['matrices'][token[2:]]
            else:
                child=children[nextchild];nextchild+=1
                m=[child[k*n:(k+1)*n] for k in range(n)]
            state=[sum((m[i][j]*state[j] for j in range(n)),start=Fraction(0))
                   for i in range(n)]
        columns.append(state)
    return tuple(columns[j][i] for i in range(n) for j in range(n))

def audit_frontend(p):
    if p['source'] is None:
        return 0
    checks=0
    for oi,op in enumerate(p['ops']):
        count=prod(p['dims'][s] for s in op['inputs'])
        require(checks+count<=MAX_ITEMS,'frontend tensor audit limit')
        for ids in product(*(range(p['dims'][s]) for s in op['inputs'])):
            children=[tuple(Fraction(int(k==i)) for k in range(p['dims'][s]))
                      for s,i in zip(op['inputs'],ids)]
            require(source_value(p,oi,children)==tensor_value(p,oi,children),
                    'compiled tensor disagrees with source')
            checks+=1
    return checks

def scalar(row,v):
    return sum((row[i]*v[i] for i in range(len(row))),start=Fraction(0))

def combination(basis,coeff,dimension):
    return tuple(sum((basis[j][i]*coeff[j] for j in range(len(basis))),start=Fraction(0))
                 for i in range(dimension))

def enclosure(p,c):
    keys(c,('basis','closures'))
    raw=c['basis'];require(type(raw) is dict and set(raw)==set(p['dims']),'basis sorts')
    B={s:[vector(v,p['dims'][s]) for v in sequence(raw[s])] for s in p['dims']}
    require(all(len(bs)<=MAX_DIM for bs in B.values()),'basis size limit')
    required=set()
    for oi,op in enumerate(p['ops']):
        count=prod(len(B[s]) for s in op['inputs'])
        require(len(required)+count<=MAX_ITEMS,'closure tuple limit')
        required.update((oi,ids) for ids in product(*(range(len(B[s])) for s in op['inputs'])))
    H={}
    for rec in sequence(c['closures']):
        keys(rec,('op','children','coeff'))
        oi=integer(rec['op'],0,max(0,len(p['ops'])-1));require(oi<len(p['ops']),'closure op')
        ids=tuple(sequence(rec['children']))
        for j in ids:integer(j)
        key=(oi,ids);require(key in required and key not in H,'duplicate/foreign closure tuple')
        op=p['ops'][oi]
        coeff=vector(rec['coeff'],len(B[op['out']]))
        actual=source_value(p,oi,[B[s][j] for s,j in zip(op['inputs'],ids)])
        require(actual==combination(B[op['out']],coeff,p['dims'][op['out']]),
                'false constructor closure identity')
        H[key]=coeff
    require(set(H)==required,'missing constructor closure tuple')
    return B,H

def replay(original,certificate):
    p=decode_problem(original);frontend_checks=audit_frontend(p)
    require(type(certificate) is dict,'certificate object')
    require(certificate.get('schema')=='forge.mlc.certificate.v1','certificate schema')
    kind=certificate.get('kind')
    if kind in ('invariant','enclosure'):
        keys(certificate,('schema','kind','basis','closures'))
        B,H=enclosure(p,{k:certificate[k] for k in ('basis','closures')})
        if kind=='invariant':
            for s,q in p['targets']:
                require(all(scalar(q,v)==0 for v in B[s]),'target not annihilated')
        return {'accepted':True,'claim':'universal_zero' if kind=='invariant' else 'enclosure',
                'closure_identities':len(H),'frontend_checks':frontend_checks}
    if kind=='counterexample':
        keys(certificate,('schema','kind','nodes','root','target','claimed_value'))
        values=[];sorts=[];tree_sizes=[];word_lengths=[]
        for i,node in enumerate(sequence(certificate['nodes'])):
            keys(node,('op','children'));oi=integer(node['op'],0,max(0,len(p['ops'])-1))
            require(oi<len(p['ops']),'witness operation');op=p['ops'][oi]
            child=sequence(node['children']);require(len(child)==len(op['inputs']),'witness arity')
            for s,j in zip(op['inputs'],child):
                integer(j,0,max(0,i-1));require(j<i,'witness not acyclic')
                require(sorts[j]==s,'witness child sort')
            val=source_value(p,oi,[values[j] for j in child])
            values.append(val);sorts.append(op['out'])
            tree_sizes.append(1+sum(tree_sizes[j] for j in child))
            if p['source'] and p['source']['kind']=='cfg':
                literal=sum(t.startswith('t:') for t in p['source']['rules'][oi]['rhs'])
                word_lengths.append(literal+sum(word_lengths[j] for j in child))
        root=integer(certificate['root'],0,max(0,len(values)-1));require(root<len(values),'root')
        ti=integer(certificate['target'],0,max(0,len(p['targets'])-1));require(ti<len(p['targets']),'target')
        s,q=p['targets'][ti];require(sorts[root]==s,'root sort')
        actual=scalar(q,values[root])
        require(actual!=0 and actual==rational(certificate['claimed_value']),'invalid counterexample value')
        answer={'accepted':True,'claim':'nonzero_derivation','value':str(actual),
                'dag_nodes':len(values),'expanded_tree_nodes':str(tree_sizes[root]),
                'frontend_checks':frontend_checks}
        if word_lengths:answer['word_length']=str(word_lengths[root])
        return answer
    if kind=='quotient':
        keys(certificate,('schema','kind','enclosure','maps','sections','left_inverses','model'))
        B,H=enclosure(p,certificate['enclosure'])
        qp=decode_problem(certificate['model'])
        require(qp['source'] is None,'quotient must be a plain tensor model')
        require(set(qp['dims'])==set(p['dims']),'quotient sorts')
        require(len(qp['ops'])==len(p['ops']) and len(qp['targets'])==len(p['targets']),
                'quotient signature sizes')
        for a,b in zip(p['ops'],qp['ops']):
            require((a['out'],a['inputs'],a['name'])==(b['out'],b['inputs'],b['name']),
                    'quotient operation signature')
        C={};R={};L={}
        for field in ('maps','sections','left_inverses'):
            require(type(certificate[field]) is dict and set(certificate[field])==set(p['dims']),
                    'quotient map sorts')
        for s,d in p['dims'].items():
            r=len(B[s]);k=qp['dims'][s]
            cs=sequence(certificate['maps'][s]);rs=sequence(certificate['sections'][s])
            ls=sequence(certificate['left_inverses'][s])
            require(len(cs)==k and len(rs)==r and len(ls)==r,'map row counts')
            C[s]=[vector(row,r) for row in cs]
            R[s]=[vector(row,k) for row in rs]
            L[s]=[vector(row,d) for row in ls]
            for i in range(r):
                for j in range(r):
                    require(scalar(L[s][i],B[s][j])==int(i==j),'invalid basis left inverse')
            for i in range(k):
                for j in range(k):
                    require(sum((C[s][i][a]*R[s][a][j] for a in range(r)),start=Fraction(0))
                            ==int(i==j),'invalid quotient section')
        for (oi,ids),h in H.items():
            op=p['ops'][oi]
            child=[tuple(row[j] for row in C[s]) for s,j in zip(op['inputs'],ids)]
            lhs=tuple(scalar(row,h) for row in C[op['out']])
            require(lhs==tensor_value(qp,oi,child),'quotient constructor diagram')
        for (s,q),(t,beta) in zip(p['targets'],qp['targets']):
            require(s==t,'quotient target sort')
            for j,v in enumerate(B[s]):
                require(scalar(q,v)==sum((beta[i]*C[s][i][j] for i in range(len(beta))),
                                        start=Fraction(0)),'quotient target diagram')
        return {'accepted':True,'claim':'all_observations_preserved',
                'closure_identities':len(H),'quotient_dimensions':qp['dims'],
                'frontend_checks':frontend_checks}
    raise Invalid('unsupported certificate kind')

def verify(problem,certificate):
    try:
        return replay(problem,certificate)
    except (Invalid,KeyError,TypeError,ValueError,IndexError,OverflowError) as e:
        return {'accepted':False,'reason':str(e)}

def load(path):
    with open(path,'rb') as f:
        data=f.read(MAX_TEXT+1)
    require(len(data)<=MAX_TEXT,'JSON byte limit')
    def pairs(items):
        ans={}
        for k,v in items:
            require(k not in ans,'duplicate JSON key');ans[k]=v
        return ans
    return json.loads(data,object_pairs_hook=pairs,
                      parse_constant=lambda _: (_ for _ in ()).throw(Invalid('nonfinite JSON')))

if __name__=='__main__':
    if len(sys.argv)!=3:
        print('Usage: python -S checker.py PROBLEM.json CERTIFICATE.json',file=sys.stderr)
        raise SystemExit(2)
    try:
        result=verify(load(sys.argv[1]),load(sys.argv[2]))
    except (OSError,ValueError) as e:
        result={'accepted':False,'reason':str(e)}
    print(json.dumps(result,indent=2,sort_keys=True))
    raise SystemExit(0 if result['accepted'] else 1)
