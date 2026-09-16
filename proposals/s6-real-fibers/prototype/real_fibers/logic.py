"""Boolean formulas and their characteristic functions on {-1,0,1}^m."""
from fractions import Fraction as Q
from .exact import P, Reject, Limit, integer

RELS={'lt':lambda s:s<0, 'le':lambda s:s<=0, 'eq':lambda s:s==0,
      'ne':lambda s:s!=0,'ge':lambda s:s>=0,'gt':lambda s:s>0}


def validate_formula(f,m,depth=0):
    if depth>40: raise Limit('formula depth cap')
    if not isinstance(f,list) or not f: raise Reject('formula syntax')
    op=f[0]
    if op in ('true','false'):
        if len(f)!=1: raise Reject('Boolean literal arity')
    elif op=='atom':
        if len(f)!=3 or f[2] not in RELS: raise Reject('atom syntax')
        integer(f[1],0,m-1)
    elif op=='not':
        if len(f)!=2: raise Reject('not arity')
        validate_formula(f[1],m,depth+1)
    elif op in ('and','or','implies','iff'):
        if len(f)!=3: raise Reject('connective arity')
        validate_formula(f[1],m,depth+1);validate_formula(f[2],m,depth+1)
    else: raise Reject('unknown formula operator')


def eval_formula(f,signs):
    op=f[0]
    if op=='true': return True
    if op=='false': return False
    if op=='atom': return RELS[f[2]](signs[f[1]])
    if op=='not': return not eval_formula(f[1],signs)
    a,b=eval_formula(f[1],signs),eval_formula(f[2],signs)
    return {'and':a and b,'or':a or b,'implies':not a or b,'iff':a==b}[op]


def sign_reduce(p):
    return P.make(p.n,[(tuple(0 if k==0 else 1+(k-1)%2 for k in e),c) for e,c in p.terms])


def sign_mul(a,b): return sign_reduce(a*b)


def indicator(f,m):
    """Replay compiler: recursive Boolean arithmetic, not truth-table interpolation."""
    validate_formula(f,m)
    one=P.const(m,1)
    def go(f):
        op=f[0]
        if op=='true':return one
        if op=='false':return P.const(m)
        if op=='atom':
            s=P.var(m,f[1]);sp=(s*s+s)*Q(1,2);sn=(s*s-s)*Q(1,2)
            return {'gt':sp,'lt':sn,'eq':one-s*s,'ne':s*s,'ge':one-sn,'le':one-sp}[f[2]]
        if op=='not':return one-go(f[1])
        a,b=go(f[1]),go(f[2]);ab=sign_mul(a,b)
        return {'and':ab,'or':a+b-ab,'implies':one-a+ab,
                'iff':one-a-b+2*ab}[op]
    return sign_reduce(go(f))
