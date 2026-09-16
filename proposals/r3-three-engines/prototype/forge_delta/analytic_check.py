"""Independent analytic replay; does not import the search implementation.

Its symbolic derivative rules are intentionally unsimplified. Series bounds
are recomputed by recurrences, rather than the searcher's power/factorial sums.
This is executable research evidence, not a formally proved checker.
"""
from fractions import Fraction as F
from .wire import q,require

def validate(e,depth=0):
    require(depth<=100 and isinstance(e,list) and e,'AST')
    k=e[0]
    if k=='c': require(len(e)==2,'Constant arity'); q(e[1]); return
    if k=='x': require(len(e)==1,'Variable arity'); return
    require(k in ('neg','add','mul','div','pow','exp','log','sin','cos'),'Operation')
    require(len(e)==(3 if k in ('add','mul','div','pow') else 2),'Arity')
    validate(e[1],depth+1)
    if k in ('add','mul','div'): validate(e[2],depth+1)
    if k=='pow': require(type(e[2]) is int and 0<=e[2]<=64,'Exponent')

def d(e):
    k=e[0]; c=lambda n:['c',str(n)]
    if k=='c': return c(0)
    if k=='x': return c(1)
    a=e[1]; da=d(a)
    if k=='neg': return ['neg',da]
    if k=='add': return ['add',da,d(e[2])]
    if k=='mul': return ['add',['mul',da,e[2]],['mul',a,d(e[2])]]
    if k=='div':
        b=e[2]
        return ['div',['add',['mul',da,b],['neg',['mul',a,d(b)]]],['pow',b,2]]
    if k=='pow':
        n=e[2]
        return c(0) if n==0 else ['mul',['mul',c(n),['pow',a,n-1]],da]
    outer={'exp':['exp',a],'log':['div',c(1),a],
           'sin':['cos',a],'cos':['neg',['sin',a]]}[k]
    return ['mul',outer,da]

def at(e,x):
    k=e[0]
    if k=='c': return q(e[1])
    if k=='x': return x
    a=at(e[1],x)
    if k=='neg': return -a
    if k=='add': return a+at(e[2],x)
    if k=='mul': return a*at(e[2],x)
    if k=='div': return a/at(e[2],x)
    if k=='pow': return a**e[2]
    require((k in ('exp','sin','cos') and a==0) or (k=='log' and a==1),'Exact anchor')
    return F(k in ('exp','cos'))

def primitive(k,x,n):
    if k=='exp':
        t=F(1); s=t
        for j in range(1,n+1): t*=x/j; s+=t
        t=abs(t*x/(n+1)); ratio=abs(x)/F(n+2)
        require(ratio<1,'Tail ratio')
        r=t/(1-ratio)
    else:
        require(x>0,'Log domain')
        z=(x-1)/(x+1); term=z; s=F(0)
        for j in range(n):
            s+=2*term/(2*j+1); term*=z*z
        r=2*abs(term)/((2*n+1)*(1-z*z))
    return s-r,s+r

def interval(e,b,n):
    k=e[0]
    if k=='c': return (q(e[1]),)*2
    if k=='x': return b
    a=interval(e[1],b,n)
    if k=='neg': return -a[1],-a[0]
    if k in ('add','mul','div'):
        t=interval(e[2],b,n)
        if k=='add': return a[0]+t[0],a[1]+t[1]
        if k=='div':
            require(not t[0]<=0<=t[1],'Division domain')
            t=(1/t[1],1/t[0])
        v=[a[i]*t[j] for i in (0,1) for j in (0,1)]
        return min(v),max(v)
    if k=='pow':
        j=e[2]
        if j==0: return F(1),F(1)
        v=[a[0]**j,a[1]**j]
        if not j%2 and a[0]<=0<=a[1]: v.append(F(0))
        return min(v),max(v)
    if k in ('exp','log'): return primitive(k,a[0],n)[0],primitive(k,a[1],n)[1]
    require(k in ('sin','cos'),'Trig')
    # Recompute coefficients by recurrence; evaluate each monomial range.
    coeff=F(1); lo=hi=F(0)
    for j in range(n+1):
        if j: coeff/=j
        if j%2 == (1 if k=='sin' else 0):
            vals=[a[0]**j,a[1]**j]
            if j>0 and not j%2 and a[0]<=0<=a[1]: vals.append(F(0))
            c=coeff*((-1)**(j//2))
            vals=[c*v for v in vals]
            lo+=min(vals); hi+=max(vals)
    r=max(abs(a[0]),abs(a[1]))**(n+1)*coeff/(n+1)
    return max(F(-1),lo-r),min(F(1),hi+r)

def domain(e,b,n):
    # Evaluate original tree too: derivative simplification must not erase a pole.
    interval(e,b,n)

def check(problem,cert):
    try:
        require(cert['kind'] in ('interval','jet'),'Positive certificate')
        e=problem['expr']; validate(e)
        b=tuple(map(q,problem['box'])); require(len(b)==2 and b[0]<=b[1],'Box')
        original=e
        if cert['kind']=='jet':
            m=cert['order']; a=q(cert['anchor'])
            require(type(m) is int and 1<=m<=6,'Jet order')
            require(b[0]<=a<=b[1] and (m%2==0 or b[0]>=a),'Jet orientation')
            for _ in range(m):
                require(at(e,a)==0,'Vanishing condition'); e=d(e)
        count=[0]
        def visit(t,bb,depth=0):
            count[0]+=1; require(count[0]<=10000 and depth<=32,'Tree budget')
            if t['kind']=='split':
                x=q(t['at']); require(bb[0]<x<bb[1],'Coverage')
                visit(t['left'],(bb[0],x),depth+1); visit(t['right'],(x,bb[1]),depth+1)
            else:
                require(t['kind']=='leaf','Node kind')
                n=t['order']; require(type(n) is int and 1<=n<=128,'Series order')
                domain(original,bb,n)
                lo,hi=interval(e,bb,n)
                claim=tuple(map(q,t['bound']))
                # Search may simplify derivatives, so exact interval equality is
                # needlessly restrictive. Verify the advertised enclosure is wider.
                require(len(claim)==2 and 0<=claim[0]<=lo<=hi<=claim[1],'Enclosure')
        visit(cert['tree'],b)
        return True
    except (ValueError,KeyError,TypeError,IndexError,ZeroDivisionError,RecursionError):
        return False
