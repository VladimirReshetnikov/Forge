"""Local orbit/edge checker. No imports from any producer module."""
from fractions import Fraction
from math import gcd
from .checker import require, integer, sequence, shape, CheckLimit, VerifiedChain

def polynomial(raw, degree, max_terms=100_000):
    result = {}
    previous = None
    for row in sequence(raw,max_terms):
        sequence(row,3); require(len(row)==3,'polynomial row arity')
        e = tuple(integer(x) for x in sequence(row[0],degree))
        require(len(e)==degree, 'monomial dimension')
        require(previous is None or previous<e, 'monomials must be strictly sorted')
        a,b = row[1:]
        require(type(a) is int and a!=0, 'nonzero integer numerator required')
        integer(b,lower=1)
        require(gcd(abs(a),b)==1,'rational coefficient must be reduced')
        result[e] = Fraction(a,b); previous=e
    return result

def verify_projection(chain: VerifiedChain, terms, certificate, *, max_monomials=100_000):
    source = polynomial(terms,chain.degree,max_monomials)
    shape(certificate,{'format','orbits','output'})
    require(certificate['format']=='forge.symmetry.reynolds.v1','wrong Reynolds format')
    expected = {}
    covered = set()
    rows = sequence(certificate['orbits'],len(source))
    total = 0
    def move(g,e):
        answer = [0]*chain.degree
        for i in range(chain.degree): answer[g[i]]=e[i]
        return tuple(answer)
    for tree in rows:
        sequence(tree,max_monomials); require(bool(tree),'empty monomial orbit')
        points=[]; members=set()
        for j,row in enumerate(tree):
            total+=1
            if total>max_monomials: raise CheckLimit('monomial replay budget exceeded')
            sequence(row,3); require(len(row)==3,'monomial edge arity')
            exponent = tuple(integer(x) for x in sequence(row[0],chain.degree))
            require(len(exponent)==chain.degree,'monomial edge dimension')
            require(exponent not in members and exponent not in covered,'duplicate monomial')
            if j==0:
                require(row[1] is None and row[2] is None,'orbit root schema')
                require(exponent in source,'orbit root must occur in original support')
            else:
                parent=integer(row[1],upper=j-1)
                label=integer(row[2],upper=len(chain.generators)-1)
                require(move(chain.generators[label],points[parent])==exponent,'incorrect monomial edge')
            points.append(exponent);members.add(exponent)
        # Finite closure under bijections implies inverse closure too.
        for e in points:
            for g in chain.generators:
                require(move(g,e) in members,'monomial orbit is not closed')
        covered.update(members)
        coefficient = sum((source.get(e,Fraction()) for e in members),Fraction()) / len(members)
        if coefficient:
            for e in members: expected[e]=coefficient
    require(set(source)<=covered,'source support not fully covered')
    supplied = polynomial(certificate['output'],chain.degree,max_monomials)
    require(supplied==expected,'incorrect Reynolds coefficients')
    return {'output':certificate['output'], 'orbit_count':len(rows), 'monomial_count':total}
