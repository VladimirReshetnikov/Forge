"""Rational interval/vanishing-jet proposer for one-variable elementary ASTs.

No floating-point operation is used. Positive output is a Python certificate,
not a Lean theorem. Domain failures and exhausted resources return UNKNOWN.
"""
from fractions import Fraction as F
from math import factorial
from .wire import q

class Unknown(Exception): pass

def C(x): return ['c',str(q(x))]
X=['x']

def op(k,*args):
    if k=='neg':
        a=args[0]
        if a[0]=='c': return C(-q(a[1]))
        if a[0]=='neg': return a[1]
    if k in ('add','mul','div'):
        a,b=args
        if a[0]==b[0]=='c':
            x,y=q(a[1]),q(b[1])
            if k=='add': return C(x+y)
            if k=='mul': return C(x*y)
            if y: return C(x/y)
        if k=='add':
            if a==C(0): return b
            if b==C(0): return a
        if k=='mul':
            if a==C(0) or b==C(0): return C(0)
            if a==C(1): return b
            if b==C(1): return a
        if k=='div' and b==C(1): return a
    if k=='pow':
        a,n=args
        if n==0: return C(1)
        if n==1: return a
        if a[0]=='c': return C(q(a[1])**n)
    return [k,*args]

def sub(a,b): return op('add',a,op('neg',b))

def derivative(e):
    k=e[0]
    if k=='c': return C(0)
    if k=='x': return C(1)
    a=e[1]; da=derivative(a)
    if k=='neg': return op('neg',da)
    if k=='add': return op('add',da,derivative(e[2]))
    if k=='mul': return op('add',op('mul',da,e[2]),op('mul',a,derivative(e[2])))
    if k=='div':
        b=e[2]
        return op('div',sub(op('mul',da,b),op('mul',a,derivative(b))),op('pow',b,2))
    if k=='pow':
        n=e[2]
        return C(0) if n==0 else op('mul',op('mul',C(n),op('pow',a,n-1)),da)
    d={'exp':op('exp',a),'log':op('div',C(1),a),
       'sin':op('cos',a),'cos':op('neg',op('sin',a))}[k]
    return op('mul',d,da)

def exact_at(e,x):
    k=e[0]
    if k=='c': return q(e[1])
    if k=='x': return x
    a=exact_at(e[1],x)
    if k=='neg': return -a
    if k=='add': return a+exact_at(e[2],x)
    if k=='mul': return a*exact_at(e[2],x)
    if k=='div': return a/exact_at(e[2],x)
    if k=='pow': return a**e[2]
    if k=='exp' and a==0: return F(1)
    if k=='log' and a==1: return F(0)
    if k=='sin' and a==0: return F(0)
    if k=='cos' and a==0: return F(1)
    raise Unknown('No exact anchor rule')

def plus(a,b): return a[0]+b[0],a[1]+b[1]
def minus(a): return -a[1],-a[0]
def times(a,b):
    v=[x*y for x in a for y in b]
    return min(v),max(v)
def power(a,n):
    if n==0: return F(1),F(1)
    if n%2: return a[0]**n,a[1]**n
    return (F(0) if a[0]<=0<=a[1] else min(a[0]**n,a[1]**n)),max(a[0]**n,a[1]**n)

def point_exp(x,n):
    r=abs(x)
    if r>=n+2: raise Unknown('Exp tail ratio is not below one')
    s=sum((x**k/F(factorial(k)) for k in range(n+1)),F(0))
    err=r**(n+1)/factorial(n+1)/(1-r/F(n+2))
    return s-err,s+err

def point_log(x,n):
    if x<=0: raise Unknown('Log domain')
    t=(x-1)/(x+1); r=abs(t)
    s=2*sum((t**(2*k+1)/F(2*k+1) for k in range(n)),F(0))
    err=2*r**(2*n+1)/((2*n+1)*(1-r*r))
    return s-err,s+err

def enclose(e,box,n):
    k=e[0]
    if k=='c': return q(e[1]),q(e[1])
    if k=='x': return box
    a=enclose(e[1],box,n)
    if k=='neg': return minus(a)
    if k=='add': return plus(a,enclose(e[2],box,n))
    if k=='mul': return times(a,enclose(e[2],box,n))
    if k=='div':
        b=enclose(e[2],box,n)
        if b[0]<=0<=b[1]: raise Unknown('Division domain')
        return times(a,(1/b[1],1/b[0]))
    if k=='pow': return power(a,e[2])
    if k=='exp': return point_exp(a[0],n)[0],point_exp(a[1],n)[1]
    if k=='log': return point_log(a[0],n)[0],point_log(a[1],n)[1]
    if k in ('sin','cos'):
        s=(F(0),F(0))
        for j in range(n+1):
            if j%2 == (1 if k=='sin' else 0):
                sign=(-1)**((j-1)//2 if k=='sin' else j//2)
                s=plus(s,times((F(sign,factorial(j)),)*2,power(a,j)))
        r=max(map(abs,a)); err=r**(n+1)/factorial(n+1)
        return max(F(-1),s[0]-err),min(F(1),s[1]+err)
    raise Unknown('Unsupported expression')

def tree(e,box,depth=8,orders=(8,16,32),budget=None):
    if budget is None: budget=[1024]
    budget[0]-=1
    if budget[0]<0: raise Unknown('Tree node budget')
    for n in orders:
        try:
            b=enclose(e,box,n)
            if b[0]>=0: return {'kind':'leaf','order':n,'bound':list(map(str,b))}
        except Unknown: pass
    if depth==0: raise Unknown('Subdivision depth')
    mid=sum(box)/2
    if mid==box[0] or mid==box[1]: raise Unknown('Degenerate box')
    return {'kind':'split','at':str(mid),
            'left':tree(e,(box[0],mid),depth-1,orders,budget),
            'right':tree(e,(mid,box[1]),depth-1,orders,budget)}

def prove(problem,jet_order=0,anchor=0,**options):
    e=problem['expr']; box=tuple(map(q,problem['box']))
    try:
        if jet_order:
            a=q(anchor)
            if not box[0]<=a<=box[1]: raise Unknown('Anchor outside interval')
            if jet_order%2 and box[0]<a: raise Unknown('Odd jet needs right-sided interval')
            for _ in range(jet_order):
                if exact_at(e,a)!=0: raise Unknown('Nonvanishing jet')
                e=derivative(e)
            return {'kind':'jet','order':jet_order,'anchor':str(a),'tree':tree(e,box,**options)}
        return {'kind':'interval','tree':tree(e,box,**options)}
    except (Unknown,ZeroDivisionError) as ex:
        return {'kind':'unknown','reason':str(ex)}

def auto_prove(problem,depth=4,max_jet=6):
    """Bounded automatic anchor/order proposal. No numerical zero guessing.

Try a shallow plain interval proof, then exact jets at 0 and box endpoints.
Each proposal has its own bounded tree; the total number of proposals is finite.
"""
    plain=prove(problem,depth=depth)
    if plain['kind']!='unknown': return plain
    lo,hi=map(q,problem['box']); tried=1
    for a in dict.fromkeys([F(0),lo,hi]):
        if not lo<=a<=hi: continue
        e=problem['expr']
        for m in range(1,max_jet+1):
            try:
                if exact_at(e,a)!=0: break
                e=derivative(e)
            except (Unknown,ZeroDivisionError): break
            if m%2 and lo<a: continue
            c=prove(problem,jet_order=m,anchor=a,depth=depth);tried+=1
            if c['kind']!='unknown':
                c['discovery']={'attempts':tried,'policy':'zero-and-endpoints-v1'}
                return c
    return {'kind':'unknown','reason':'Bounded interval and exact-jet discovery exhausted','attempts':tried}
