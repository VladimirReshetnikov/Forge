"""Independent, standard-library replay. Imports neither algebra nor search.

Accepted objects establish facts about the exact finite object-language problem;
this program is NOT a verified checker and does not produce a Lean proof.
All equality problems mean universal associative unital Q-algebras. Operator and
trace problems mean real square matrices, of arbitrary finite dimension, whose
transpose agrees with the declared atom involution. Positive premises are PSD.
These interpretations are fixed by the schema, not selected by a certificate.
"""
from __future__ import annotations
from fractions import Fraction
from math import gcd
from dataclasses import dataclass
import json

MAX_ATOMS=12
MAX_WORD=24
MAX_TERMS=10000
MAX_BITS=8192
MAX_DIMENSION=100
MAX_PRODUCTS=2_000_000

class Rejected(ValueError): pass

def demand(test, message):
    if not test: raise Rejected(message)

def keys(obj, required):
    demand(type(obj) is dict and set(obj)==set(required), 'unexpected or missing object field')

def integer(x, lo=None, hi=None):
    demand(type(x) is int, 'integer required (not bool or float)')
    demand(x.bit_length()<=MAX_BITS, 'integer bit cap')
    demand(lo is None or x>=lo, 'integer below allowed range')
    demand(hi is None or x<=hi, 'integer above allowed range')
    return x

def fraction(pair):
    demand(type(pair) is list and len(pair)==2, 'rational pair required')
    a,b=integer(pair[0]),integer(pair[1],1)
    demand(gcd(a,b)==1, 'rational must be reduced with positive denominator')
    return Fraction(a,b)

def sequence(x, bound=MAX_TERMS):
    demand(type(x) is list and len(x)<=bound, 'bounded list required')
    return x

def word(x,m):
    return tuple(integer(i,0,m-1) for i in sequence(x,MAX_WORD))

def polynomial(x,m):
    out={}; last=None
    for term in sequence(x):
        demand(type(term) is list and len(term)==3, 'polynomial term shape')
        w=word(term[0],m); c=fraction(term[1:])
        demand(c!=0 and (last is None or last<w), 'noncanonical polynomial')
        out[w]=c; last=w
    return out

@dataclass
class Meter:
    products:int=0
    def use(self, count=1):
        self.products+=count
        demand(self.products<=MAX_PRODUCTS,'replay product cap')

# Deliberately small, separate implementation: accumulate monomial streams.
def collect(terms):
    result={}
    for w,c in terms:
        result[w]=result.get(w,Fraction(0))+c
    return {w:c for w,c in result.items() if c}

def product(a,b,meter):
    meter.use(len(a)*len(b))
    return collect((u+v,c*d) for u,c in a.items() for v,d in b.items())

def adjoint(a,inv):
    return collect((tuple(inv[t] for t in w[::-1]),c) for w,c in a.items())

def replay_ideal(items,rels,m,meter):
    contributions=[]
    for item in sequence(items):
        keys(item,('relation','left','right','weight'))
        j=integer(item['relation'],0,len(rels)-1)
        u,v=word(item['left'],m),word(item['right'],m)
        c=fraction(item['weight'])
        meter.use(len(rels[j]))
        contributions.extend((u+w+v,c*d) for w,d in rels[j].items())
    return collect(contributions)

def mat_identity(n):
    return [[Fraction(i==j) for j in range(n)] for i in range(n)]

def mat_product(a,b,meter):
    n=len(a); meter.use(n*n*n)
    return [[sum((a[i][k]*b[k][j] for k in range(n)),Fraction(0))
             for j in range(n)] for i in range(n)]

def evaluate_matrix(poly,matrices,n,meter):
    value=[[Fraction(0) for _ in range(n)] for _ in range(n)]
    # Evaluate every complete word as a matrix, not merely on the witness vector.
    for w,c in poly.items():
        term=mat_identity(n)
        for i in w: term=mat_product(term,matrices[i],meter)
        for i in range(n):
            for j in range(n): value[i][j]+=c*term[i][j]
    return value

def _verify(problem, certificate):
    keys(problem,('schema','kind','atoms','involution','target','relations','positives'))
    demand(problem['schema']=='ncforge.problem.v1','problem schema mismatch')
    kind=problem['kind']; demand(kind in ('equality','operator','trace'),'unsupported problem kind')
    m=integer(problem['atoms'],1,MAX_ATOMS)
    inv=sequence(problem['involution'],MAX_ATOMS)
    demand(len(inv)==m,'involution arity')
    inv=[integer(t,0,m-1) for t in inv]
    demand(all(inv[inv[i]]==i for i in range(m)),'not an involution')
    p=polynomial(problem['target'],m)
    rels=[polynomial(r,m) for r in sequence(problem['relations'],200)]
    gs=[polynomial(g,m) for g in sequence(problem['positives'],200)]
    if kind=='equality': demand(not gs,'equality schema has no positivity assumptions')
    else:
        demand(adjoint(p,inv)==p,'positivity target must be formally self-adjoint')
        demand(all(adjoint(g,inv)==g for g in gs),'positive premise not self-adjoint')
    demand(type(certificate) is dict,'certificate object required')
    ck=certificate.get('kind'); meter=Meter()
    demand(certificate.get('schema')=='ncforge.certificate.v1','certificate schema mismatch')
    if ck=='matrix_countermodel':
        demand(kind=='equality','matrix countermodel is for universal algebra equality only')
        keys(certificate,('schema','kind','dimension','matrices','vector'))
        n=integer(certificate['dimension'],1,MAX_DIMENSION)
        matrices=sequence(certificate['matrices'],MAX_ATOMS)
        demand(len(matrices)==m,'matrix atom count')
        ms=[]
        for a in matrices:
            a=sequence(a,MAX_DIMENSION); demand(len(a)==n,'matrix row count')
            rows=[]
            for row in a:
                row=sequence(row,MAX_DIMENSION); demand(len(row)==n,'matrix column count')
                rows.append([fraction(x) for x in row])
            ms.append(rows)
        v=sequence(certificate['vector'],MAX_DIMENSION); demand(len(v)==n,'vector dimension')
        v=[fraction(x) for x in v]
        for r in rels:
            demand(all(x==0 for row in evaluate_matrix(r,ms,n,meter) for x in row),
                   'relation fails as a whole matrix')
        target=evaluate_matrix(p,ms,n,meter)
        demand(any(sum((a*b for a,b in zip(row,v)),Fraction(0))!=0 for row in target),
               'target does not separate the vector')
        return {'accepted':True,'meaning':'counterexample_to_universal_algebra_equality',
                'products':meter.products}
    demand(ck==kind,'certificate interpretation does not match original problem')
    if kind=='equality': keys(certificate,('schema','kind','ideal'))
    elif kind=='operator': keys(certificate,('schema','kind','ideal','squares'))
    else: keys(certificate,('schema','kind','ideal','squares','commutators'))
    total=list(replay_ideal(certificate['ideal'],rels,m,meter).items())
    if kind!='equality':
        for s in sequence(certificate['squares']):
            keys(s,('weight','positive','q'))
            c=fraction(s['weight']); demand(c>=0,'negative positivity weight')
            j=integer(s['positive'],-1,len(gs)-1)
            q=polynomial(s['q'],m); g={():Fraction(1)} if j==-1 else gs[j]
            t=product(product(adjoint(q,inv),g,meter),q,meter)
            total.extend((w,c*a) for w,a in t.items())
    if kind=='trace':
        for c in sequence(certificate['commutators']):
            keys(c,('weight','left','right'))
            a,b=word(c['left'],m),word(c['right'],m)
            t=fraction(c['weight']); total.extend(((a+b,t),(b+a,-t)))
            meter.use(2)
    demand(collect(total)==p,'expanded certificate does not equal original target')
    return {'accepted':True,'meaning':{'equality':'universal_algebra_equality',
            'operator':'conditional_positive_semidefiniteness','trace':'conditional_nonnegative_trace'}[kind],
            'products':meter.products}

def verify(problem:dict, certificate:dict) -> dict:
    """Fail closed on malformed evidence. Resource limits also mean rejection, not falsity."""
    try: return _verify(problem,certificate)
    except (Rejected,ValueError,TypeError,KeyError,IndexError,OverflowError,RecursionError) as exc:
        return {'accepted':False,'reason':str(exc)}

def load_json(path):
    """Reject duplicate object keys and nonstandard NaN/Infinity constants."""
    def pairs(xs):
        d={}
        for k,v in xs:
            if k in d: raise Rejected('duplicate JSON object key')
            d[k]=v
        return d
    def constant(s): raise Rejected('nonstandard JSON constant')
    with open(path,encoding='utf8') as f:
        return json.load(f,object_pairs_hook=pairs,parse_constant=constant)
