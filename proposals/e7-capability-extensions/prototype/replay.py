"""Independent exact replay. Standard library only; no search-module imports.

This is a research checker, not a formally verified or hostile-input-certified
verifier. Its success establishes the encoded identities/inequalities only;
Lean reification, theorem construction, and kernel replay are separate gates.
"""
from __future__ import annotations
from fractions import Fraction
from math import gcd
import argparse
import json
from pathlib import Path

LIMIT_TERMS = 20000

class Rejected(ValueError):
    pass

def integer(x):
    if type(x) is not int or abs(x).bit_length()>4096:
        raise Rejected('expected bounded integer, not bool/float')
    return x


def rational(x):
    if not isinstance(x,list) or len(x)!=2:
        raise Rejected('rational pair required')
    a,b=map(integer,x)
    if b<=0 or gcd(abs(a),b)!=1:
        raise Rejected('noncanonical rational')
    return Fraction(a,b)


def poly(data, n):
    if not isinstance(data,list) or len(data)>LIMIT_TERMS:
        raise Rejected('bad polynomial size')
    out={}
    for term in data:
        if not isinstance(term,list) or len(term)!=2:
            raise Rejected('bad term')
        e,c=term
        if not isinstance(e,list) or len(e)!=n:
            raise Rejected('exponent arity')
        e=tuple(integer(a) for a in e)
        if any(a<0 or a>64 for a in e):
            raise Rejected('exponent bound')
        c=rational(c)
        if not c or e in out:
            raise Rejected('zero/duplicate monomial')
        out[e]=c
    return out


def plus(a,b):
    d=dict(a)
    for e,c in b.items():
        d[e]=d.get(e,Fraction(0))+c
        if not d[e]:
            del d[e]
    return d


def times(a,b):
    d={}
    for x,u in a.items():
        for y,v in b.items():
            e=tuple(xi+yi for xi,yi in zip(x,y))
            d[e]=d.get(e,Fraction(0))+u*v
    if len(d)>LIMIT_TERMS:
        raise Rejected('expanded term bound')
    return {e:c for e,c in d.items() if c}


def linear_combination(cs, ps):
    if len(cs)!=len(ps):
        raise Rejected('coefficient/basis length')
    out={}
    for c,p in zip(cs,ps):
        out=plus(out,{e:c*v for e,v in p.items() if c*v})
    return out


def substitute(p, xs, n):
    # Intentionally repeated multiplication, not the search-side power routine.
    out={}
    for es,c in p.items():
        z={(0,)*n:c}
        for e,x in zip(es,xs):
            for _ in range(e):
                z=times(z,x)
        out=plus(out,z)
    return out


def check_space(problem, certificate, require_target=True):
    try:
        if certificate.get('kind')!='pullback-space-v1':
            raise Rejected('wrong certificate kind')
        n=integer(problem['n']); k=integer(problem['init_parameters'])
        degree=integer(problem['degree'])
        if not 1<=n<=8 or not 0<=k<=8 or not 0<=degree<=12:
            raise Rejected('problem limits')
        init=[poly(p,k) for p in problem['init']]
        if len(init)!=n:
            raise Rejected('initialization arity')
        maps=[[poly(p,n) for p in f] for f in problem['transitions']]
        if any(len(f)!=n for f in maps):
            raise Rejected('transition arity')
        basis=[poly(p,n) for p in certificate['basis']]
        if len(basis)>256 or any(sum(e)>degree for p in basis for e in p):
            raise Rejected('basis limit')
        if any(substitute(p,init,k) for p in basis):
            raise Rejected('initial relation does not vanish')
        actions=certificate['actions']
        if len(actions)!=len(maps):
            raise Rejected('missing transition action')
        for f,a in zip(maps,actions):
            if len(a)!=len(basis):
                raise Rejected('wrong action dimension')
            for p,row in zip(basis,a):
                cs=[rational(c) for c in row]
                if substitute(p,f,n)!=linear_combination(cs,basis):
                    raise Rejected('pullback identity fails')
        cs=certificate['target_coefficients']
        if cs is None:
            if require_target:
                raise Rejected('target was not derived')
        else:
            target=poly(problem['target'],n)  # externally supplied target
            if target!=linear_combination([rational(c) for c in cs],basis):
                raise Rejected('wrong target identity')
        return True, 'accepted encoded polynomial identities'
    except (Rejected,KeyError,TypeError,IndexError,AttributeError,ValueError) as e:
        return False,str(e)


def affine(data,n):
    if not isinstance(data,list) or len(data)!=n+1:
        raise Rejected('affine arity')
    return tuple(Fraction(integer(x)) for x in data)


def affine_subtract(a,b):
    return tuple(x-y for x,y in zip(a,b))


def affine_substitute(row,updates):
    out=[row[0]]+[Fraction(0)]*(len(row)-1)
    for c,f in zip(row[1:],updates):
        for j,v in enumerate(f):
            out[j]+=c*v
    return tuple(out)


def guards_with_domain(edge,n):
    gs=[affine(g,n) for g in edge['guards']]
    gs += [tuple(Fraction(int(j==i+1)) for j in range(n+1)) for i in range(n)]
    gs += [tuple(Fraction(int(j==0)) for j in range(n+1))]
    return gs


def check_cone(target, guards, weights):
    cs=[rational(x) for x in weights]
    if len(cs)!=len(guards) or any(c<0 for c in cs):
        raise Rejected('invalid nonnegative combination')
    got=tuple(sum((c*g[i] for c,g in zip(cs,guards)),Fraction(0))
              for i in range(len(target)))
    if tuple(target)!=got:
        raise Rejected('inequality certificate mismatch')


def check_rank(problem,cert):
    try:
        if cert.get('kind')!='ranking-v1':
            raise Rejected('wrong certificate kind')
        n=integer(problem['n'])
        if not 1<=n<=8:
            raise Rejected('dimension limit')
        nodes=problem['nodes']
        if len(nodes)!=len(set(nodes)) or not 1<=len(nodes)<=32:
            raise Rejected('invalid nodes')
        layers=cert['layers']
        if not 1<=len(layers)<=8:
            raise Rejected('ranking tuple length')
        parsed=[]
        for layer in layers:
            if set(layer)!=set(nodes):
                raise Rejected('node/phase mismatch')
            a={q:affine(v,n) for q,v in layer.items()}
            if any(c<0 for r in a.values() for c in r):
                raise Rejected('rank must map all natural states to naturals')
            parsed.append(a)
        edges=problem['edges']; witnesses=cert['edges']
        if len(edges)!=len(witnesses):
            raise Rejected('edge coverage')
        for edge,w in zip(edges,witnesses):
            src,dst=edge['source'],edge['target']
            if src not in nodes or dst not in nodes:
                raise Rejected('unknown node')
            updates=[affine(f,n) for f in edge['updates']]
            if len(updates)!=n:
                raise Rejected('update count')
            gs=guards_with_domain(edge,n)
            dom=w['target_nonnegative']
            if len(dom)!=n:
                raise Rejected('missing natural-domain obligation')
            for f,c in zip(updates,dom):
                check_cone(f,gs,c)
            pivot=integer(w['pivot'])
            if not 0<=pivot<len(parsed):
                raise Rejected('lexicographic pivot')
            for layer in parsed[:pivot]:
                if any(affine_subtract(layer[src],
                                      affine_substitute(layer[dst],updates))):
                    raise Rejected('earlier lexicographic component not equal')
            layer=parsed[pivot]
            difference=list(affine_subtract(layer[src],
                               affine_substitute(layer[dst],updates)))
            difference[0]-=1  # integral strictness, NOT merely non-increase
            check_cone(difference,gs,w['decrease'])
        return True,'accepted encoded natural-valued ranking'
    except (Rejected,KeyError,TypeError,IndexError,AttributeError,ValueError) as e:
        return False,str(e)


def check_church_index(problem,cert):
    """Check a narrow symbolic algebra contract, not sampled behavior.

    The denotation theorem proved in the article applies to encodings of finite
    lists. This checker does not assert parametricity for arbitrary Church values.
    Names are opaque lexical IDs, and the four local binders must be fresh.
    """
    try:
        if cert.get('kind')!='church-index-v1' or problem['semantics']!='encoded-finite-list-index-v1':
            raise Rejected('unsupported Church semantics')
        free=[problem[k] for k in ('default','input','index')]+problem['irrelevant_element_binders']
        if any(not isinstance(x,str) for x in free) or len(free)!=len(set(free)):
            raise Rejected('invalid free lexical IDs')
        used=set(free)
        INT={'tag':'Int','args':[]}; A={'tag':'A','args':[]}
        R={'tag':'arrow','args':[INT,A]}
        def variable(t,x):
            return t=={'op':'var','id':x}
        def binder(t,ty):
            if t['op']!='lam' or t['type']!=ty or not isinstance(t['id'],str) or t['id'] in used:
                raise Rejected('wrong binder type or escaped lexical identity')
            used.add(t['id'])
            return t['id'],t['body']
        root=cert['term']
        if root['op']!='app' or not variable(root['arg'],problem['index']):
            raise Rejected('wrong outer application')
        f=root['fn']
        if f['op']!='fold' or not variable(f['input'],problem['input']) or f['carrier']!=R:
            raise Rejected('wrong carrier or input')
        _,base=binder(f['base'],INT)
        if not variable(base,problem['default']):
            raise Rejected('base contract')
        h,s=binder(f['step'],A); k,s=binder(s,R); i,s=binder(s,INT)
        if s['op']!='intcase' or not variable(s['index'],i):
            raise Rejected('guard contract')
        if not variable(s['negative'],problem['default']) or not variable(s['zero'],h):
            raise Rejected('negative/zero branch contract')
        p=s['positive']
        if p['op']!='app' or not variable(p['fn'],k):
            raise Rejected('continuation contract')
        def index_affine(t,depth=0):
            if depth>64: raise Rejected('index term depth')
            if variable(t,i): return (1,0)
            if t['op']=='shift':
                a,b=index_affine(t['arg'],depth+1)
                return (a,b+integer(t['offset']))
            raise Rejected('non-affine or escaped index')
        if index_affine(p['arg'])!=(1,-1):
            raise Rejected('positive branch index is not predecessor')
        return True,'accepted encoded-list indexing algebra contract'
    except (Rejected,KeyError,TypeError,IndexError,AttributeError,ValueError) as e:
        return False,str(e)


def polynomial_problem(problem):
    n=integer(problem['n']);k=integer(problem['init_parameters'])
    if not 1<=n<=8 or not 0<=k<=8:raise Rejected('problem dimensions')
    init=[poly(p,k) for p in problem['init']]
    fs=[[poly(p,n) for p in f] for f in problem['transitions']]
    if len(init)!=n or any(len(f)!=n for f in fs):raise Rejected('problem arity')
    return n,k,init,fs,poly(problem['target'],n)


def polynomial_combination(cs,gs,n):
    if len(cs)!=len(gs):raise Rejected('polynomial multiplier dimension')
    out={}
    for c,g in zip(cs,gs):out=plus(out,times(poly(c,n),g))
    return out


def check_ideal(problem,cert):
    try:
        if cert.get('kind')!='pullback-ideal-v1':raise Rejected('wrong ideal kind')
        n,k,init,fs,target=polynomial_problem(problem)
        gs=[poly(g,n) for g in cert['generators']]
        if len(gs)>256:raise Rejected('generator count')
        if any(substitute(g,init,k) for g in gs):raise Rejected('generator nonzero initially')
        if len(cert['actions'])!=len(fs):raise Rejected('ideal transition coverage')
        for f,rows in zip(fs,cert['actions']):
            if len(rows)!=len(gs):raise Rejected('ideal row count')
            for g,row in zip(gs,rows):
                if substitute(g,f,n)!=polynomial_combination(row,gs,n):
                    raise Rejected('ideal pullback identity')
        if target!=polynomial_combination(cert['target_coefficients'],gs,n):
            raise Rejected('ideal target identity')
        return True,'accepted encoded inductive ideal certificate'
    except (Rejected,KeyError,TypeError,IndexError,AttributeError,ValueError) as e:
        return False,str(e)


def check_orbit_counterexample(problem,cert):
    try:
        if cert.get('kind')!='polynomial-orbit-counterexample-v1':raise Rejected('wrong counterexample kind')
        n,k,init,fs,target=polynomial_problem(problem)
        params=[rational(x) for x in cert['parameters']]
        if len(params)!=k or len(cert['word'])>256:raise Rejected('counterexample shape')
        point=[substitute(p,[{():x} if x else {} for x in params],0) for p in init]
        for a in cert['word']:
            a=integer(a)
            if not 0<=a<len(fs):raise Rejected('invalid transition label')
            point=[substitute(p,point,0) for p in fs[a]]
        if not substitute(target,point,0):raise Rejected('target still zero')
        return True,'accepted counterexample to the encoded unguarded orbit property'
    except (Rejected,KeyError,TypeError,IndexError,AttributeError,ValueError) as e:
        return False,str(e)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('file',type=Path)
    args=p.parse_args()
    if args.file.stat().st_size>16_000_000:
        raise SystemExit('input too large')
    data=json.loads(args.file.read_text())
    count=0
    for entry in data['certificates']:
        c=entry['certificate']; problem=entry['problem']
        if c['kind']=='pullback-space-v1':
            ok,msg=check_space(problem,c,entry.get('require_target',True))
        elif c['kind']=='ranking-v1':
            ok,msg=check_rank(problem,c)
        elif c['kind']=='church-index-v1':
            ok,msg=check_church_index(problem,c)
        elif c['kind']=='pullback-ideal-v1':
            ok,msg=check_ideal(problem,c)
        elif c['kind']=='polynomial-orbit-counterexample-v1':
            ok,msg=check_orbit_counterexample(problem,c)
        else:
            ok,msg=False,'unknown kind'
        if not ok:
            raise SystemExit(f"REJECTED {problem['name']}: {msg}")
        count+=1
    print(json.dumps({'accepted_certificates':count,'checker':'standalone exact Python',
                      'lean_kernel_checked':False}))

if __name__=='__main__':
    main()
