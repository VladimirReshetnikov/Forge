"""Direct two-sided identity checker; no rewriting, completion, or normal forms."""
from fractions import Fraction
from .wire import q,require

def word(w,n):
    require(type(w) is list and len(w)<=10000)
    require(all(type(i) is int and 0<=i<n for i in w))
    return tuple(w)

def polynomial(p,n):
    require(type(p) is list and len(p)<=200000)
    out={}
    for item in p:
        require(len(item)==2)
        w=word(item[0],n); c=q(item[1])
        require(c!=0 and w not in out)
        out[w]=c
    return out

def check(problem,cert):
    try:
        n=problem['generators']; require(type(n) is int and 0<n<=100)
        target=polynomial(problem['target'],n)
        rel=[polynomial(p,n) for p in problem['relations']]
        require(cert['kind']=='proved' and len(cert['terms'])<=200000)
        accumulated={}
        for t in cert['terms']:
            l=word(t['left'],n); r=word(t['right'],n)
            i=t['relation']; require(type(i) is int and 0<=i<len(rel))
            c=q(t['coefficient']); require(c!=0)
            for w,a in rel[i].items():
                k=l+w+r
                accumulated[k]=accumulated.get(k,Fraction(0))+c*a
        return {w:a for w,a in accumulated.items() if a}==target
    except (ValueError,KeyError,TypeError,IndexError,ZeroDivisionError):
        return False
