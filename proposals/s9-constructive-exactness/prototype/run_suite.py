#!/usr/bin/env python3
"""Deterministic, non-Lean research tests. Writes only to the chosen output.

python run_suite.py --output ../reproduced-results
Search uses SymPy. Replay/checker and independent minor oracle do not.
"""
from __future__ import annotations
import argparse, collections, copy, csv, itertools, json, math, platform, random, sys, time
from pathlib import Path
from sympy import Matrix, eye, zeros
import sympy
from exactness import producer as P
from exactness import checker as C

SEED=20260915
rng=random.Random(SEED)
CASES=[]; ROWS=[]; MUTATIONS=[]; ORACLES=[]; ABLATIONS=[]; CONTROLS=[]

def add(name,family,problem,make,expected,oracle=None):
    a=time.perf_counter(); cert=make(); b=time.perf_counter()
    result=C.check(problem,cert); c=time.perf_counter()
    assert result['kind']==expected,(name,result,expected)
    if oracle is not None: oracle(result,cert)
    CASES.append(dict(name=name,family=family,problem=problem,certificate=cert,expected=expected))
    ROWS.append(dict(name=name,family=family,outcome=expected,proposal_call_seconds=b-a,
                     check_seconds=c-b,certificate_bytes=len(json.dumps(cert,separators=(',',':')))))
    return cert,result

def rejected(name,problem,cert):
    try: C.check(problem,cert)
    except C.Rejected as e:
        MUTATIONS.append(dict(name=name,rejected=True,reason=str(e))); return
    raise AssertionError('accepted invalid control '+name)

def uni(n,steps=6):
    U=eye(n)
    if not n:return U
    for _ in range(steps):
        if n==1:
            if rng.randrange(2): U[0,0]=-U[0,0]
        else:
            i,j=rng.sample(range(n),2); a=rng.choice([-2,-1,1,2])
            U.row_op(i,lambda x,k:x+a*U[j,k])
    return U

def graded_uni(degrees):
    U=eye(len(degrees))
    for degree in sorted(set(degrees)):
        ids=[i for i,d in enumerate(degrees) if d==degree]; block=uni(len(ids))
        for a,i in enumerate(ids):
            for b,j in enumerate(ids): U[i,j]=block[a,b]
    return U

def prob(kind,**kw):
    return dict(kind=kind,domain='Z',**{k:P.pack(v) if isinstance(v,Matrix) else v for k,v in kw.items()})

def determinant(a):
    # Small exact permutation oracle: no SymPy, elimination, or checker Mat.
    n=len(a)
    if not n:return 1
    result=0
    for p in itertools.permutations(range(n)):
        inversions=sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))
        result+=(-1 if inversions%2 else 1)*math.prod(a[i][p[i]] for i in range(n))
    return result

def minor_invariants(M):
    a=[[int(M[i,j]) for j in range(M.cols)] for i in range(M.rows)]
    previous=1; ds=[]
    for k in range(1,min(M.shape)+1):
        g=0
        for rows in itertools.combinations(range(M.rows),k):
            for cols in itertools.combinations(range(M.cols),k):
                g=math.gcd(g,abs(determinant([[a[i][j] for j in cols] for i in rows])))
        if not g:break
        assert g%previous==0
        ds.append(g//previous); previous=g
    return ds

def make_model(n,m,p):
    r=rng.randrange(min(n,m)+1); k=n-r; s=rng.randrange(min(k,p)+1)
    B0=zeros(m,n); A0=zeros(n,p)
    for i in range(r):B0[i,i]=rng.randint(1,5)
    d=1; invariants=[]
    for i in range(s):
        d*=rng.choice([1,1,2,3]); A0[r+i,i]=d; invariants.append(d)
    V,U,Q=uni(n),uni(m),uni(p)
    A=V*A0*Q; B=U*B0*V.inv()
    return dict(A=A,B=B,A0=A0,B0=B0,V=V,U=U,Q=Q,r=r,s=s,k=k,ds=invariants)

def segment_tests():
    for case in range(96):
        n,m,p=(rng.randrange(6) for _ in range(3)); model=make_model(n,m,p)
        A,B=model['A'],model['B']; ds=model['ds']; s=model['s']; k=model['k']; r=model['r']
        hp=prob('homology',A=A,B=B)
        expected=dict(kind='homology',free_rank=k-s,torsion=[d for d in ds if d>1])
        hc,_=add(f'segment-{case}','integral_coordinates',hp,lambda:P.homology(A,B)[0],
                 'homology',lambda result,c:assert_equal(result,expected))
        bad=copy.deepcopy(hc); bad['free_rank']+=1
        rejected(f'false-rank-{case}',hp,bad)
        if m:
            bad=copy.deepcopy(hc); bad['normalB']['Uinv']['data'][0]+=1
            rejected(f'bad-inverse-{case}',hp,bad)
        # Directly prescribed original coordinates provide an independent model oracle.
        w=Matrix(p,1,[rng.randint(-3,3) for _ in range(p)]); z=A*w
        add(f'boundary-{case}','cycle_filling',prob('cycle',A=A,B=B,z=z),
            lambda:P.cycle(A,B,z),'fill')
        y=Matrix(k,1,[rng.randint(-4,4) for _ in range(k)])
        z=model['V']*Matrix(n,1,[0]*r+list(y))
        is_boundary=all(int(y[i])%ds[i]==0 for i in range(s)) and all(y[i]==0 for i in range(s,k))
        expected='fill' if is_boundary else 'obstruction'
        cp=prob('cycle',A=A,B=B,z=z)
        cc,_=add(f'cycle-{case}','cycle_classification',cp,lambda:P.cycle(A,B,z),expected)
        if expected=='obstruction':
            bad=copy.deepcopy(cc); bad['phi']['data']=[0]*n
            rejected(f'zero-separator-{case}',cp,bad)
        if case<32:
            cs,_=P.smith(B); M=C.matrix(P.pack(B)); got=C.smith(M,cs)['diag']; want=minor_invariants(B)
            assert got==want
            ORACLES.append(dict(name=f'all-minors-B-{case}',kind='determinantal_divisors',shape=list(B.shape),expected=want,achieved=got))
            C0=model['A0'][r:n,:]*model['Q']
            cs,_=P.smith(C0); got=C.smith(C.matrix(P.pack(C0)),cs)['diag']; want=minor_invariants(C0)
            assert got==want
            ORACLES.append(dict(name=f'all-minors-C-{case}',kind='determinantal_divisors',shape=list(C0.shape),expected=want,achieved=got))
        if case<24:
            scale=rng.randint(-3,3); F=scale*eye(n); E=scale*eye(m); G=scale*eye(p)
            ip=prob('induced',A=A,B=B,At=A,Bt=B,F=F,E=E,G=G)
            ic,_=add(f'induced-scale-{case}','induced_maps',ip,lambda:P.induced(A,B,A,B,F),'induced')
            assert P.unpack(ic['M'])==scale*eye(k)
            if k:
                bad=copy.deepcopy(ic); bad['M']['data'][0]+=1
                rejected(f'bad-induced-{case}',ip,bad)
            V2,U2,Q2=uni(n),uni(m),uni(p)
            At=V2*model['A0']*Q2; Bt=U2*model['B0']*V2.inv()
            F=V2*model['V'].inv(); E=U2*model['U'].inv(); G=Q2.inv()*model['Q']
            ip=prob('induced',A=A,B=B,At=At,Bt=Bt,F=F,E=E,G=G)
            i1,_=add(f'induced-basis-{case}','induced_maps',ip,lambda:P.induced(A,B,At,Bt,F),'induced')
            inv=P.induced(At,Bt,A,B,F.inv())
            # Compare coordinate composition (not merely ranks or scalar invariants).
            assert P.unpack(inv['M'])*P.unpack(i1['M'])==eye(k)
            ORACLES.append(dict(name=f'map-composition-{case}',kind='coordinate_composition',passed=True))

def assert_equal(a,b):
    assert a==b,(a,b)

def simplicial(facets,augmented=False):
    cells=set()
    for facet in facets:
        facet=tuple(sorted(facet))
        for k in range(1,len(facet)+1):cells.update(itertools.combinations(facet,k))
    if augmented:cells.add(())
    cells=sorted(cells,key=lambda x:(len(x),x)); lookup={c:i for i,c in enumerate(cells)}
    D=zeros(len(cells)); degrees=[len(c)-1 for c in cells]
    for c,j in lookup.items():
        for i in range(len(c)):
            face=c[:i]+c[i+1:]
            if face in lookup:D[lookup[face],j]=(-1)**i
    return degrees,D

def reduction_tests():
    examples=[('point',[(0,)]),('edge',[(0,1)]),('circle',[(0,1),(0,2),(1,2)]),
              ('triangle',[(0,1,2)]),('tetra-boundary',list(itertools.combinations(range(4),3))),
              ('tetrahedron',[(0,1,2,3)]),('disconnected',[(0,1),(2,3)]),
              ('square',[(0,1),(1,2),(2,3),(0,3)])]
    for name,facets in examples:
        for aug in [False,True]:
            ds,D=simplicial(facets,aug)
            for scramble in [False,True]:
                d=D
                if scramble:
                    U=graded_uni(ds); d=U*D*U.inv()
                problem=prob('reduction',source=P.chain_pack(ds,d))
                cert,_=add(f'reduce-{name}-{aug}-{scramble}','unit_reduction',problem,
                           lambda:P.reduction(ds,d)[0],'reduction')
                if len(cert['reduced']['degrees'])<len(ds):
                    bad=copy.deepcopy(cert); bad['h']['data']=[0]*(len(ds)**2)
                    rejected(f'no-h-reduce-{name}-{aug}-{scramble}',problem,bad)
    for i in range(24):
        q=rng.randrange(1,7); ds=[0]*q+[1]*q; D=zeros(2*q)
        for j in range(q):D[j,q+j]=rng.choice([-1,0,1,2,4,6])
        U=graded_uni(ds); D=U*D*U.inv()
        add(f'reduce-random-{i}','unit_reduction',prob('reduction',source=P.chain_pack(ds,D)),
            lambda:P.reduction(ds,D)[0],'reduction')
    # A cap leaves an honest, checkable intermediate object.
    ds,D=simplicial([(0,1,2,3)],True)
    cert,stats=P.reduction(ds,D,max_steps=1)
    add('reduce-one-step-cap','partial_reduction',prob('reduction',source=P.chain_pack(ds,D)),
        lambda:cert,'reduction')
    CONTROLS.append(dict(name='step_cap_retains_valid_partial_reduction',steps=stats['steps'],after=stats['after']))
    # Every nonzero entry is a nonunit, but determinant 1 means this complex is contractible.
    M=Matrix([[2,3],[3,5]]); D=zeros(4); D[:2,2:4]=M; ds=[0,0,1,1]
    cert,stats=P.reduction(ds,D)
    add('reduce-nonunit-stagnation','heuristic_boundary',prob('reduction',source=P.chain_pack(ds,D)),lambda:cert,'reduction')
    hp=prob('homotopy',source=P.chain_pack(ds,D),target=P.chain_pack(ds,D),F=eye(4),G=zeros(4))
    hc,_=add('stagnation-rescued-by-homotopy','heuristic_boundary',hp,lambda:P.homotopy(ds,D,ds,D,eye(4),zeros(4))[0],'homotopy')
    CONTROLS.append(dict(name='unit_pivot_incompleteness',before=4,after=stats['after'],contractible=True))

def homotopy_tests():
    for p in range(2,10):
        sd=[0,1]; td=[1,2]; d=Matrix([[0,p],[0,0]])
        for t in range(-2*p,2*p+1):
            F=Matrix([[0,t],[0,0]]); G=zeros(2)
            problem=prob('homotopy',source=P.chain_pack(sd,d),target=P.chain_pack(td,d),F=F,G=G)
            outcome='homotopy' if t%p==0 else 'no_homotopy'
            cert,_=add(f'ext-p{p}-t{t}','secondary_homotopy',problem,
                       lambda:P.homotopy(sd,d,td,d,F,G)[0],outcome)
            if outcome=='no_homotopy':
                bad=copy.deepcopy(cert); bad['W']['data']=[0]*4
                rejected(f'zero-W-p{p}-t{t}',problem,bad)
            # Independent enumeration of the two homotopy parameters modulo p.
            solutions=[(a,b) for a in range(p) for b in range(p) if (p*a+p*b-t)%p==0]
            assert bool(solutions)==(outcome=='homotopy')
            ORACLES.append(dict(name=f'ext-modular-p{p}-t{t}',kind='finite_modular_enumeration',
                                assignments=p*p,has_solution=bool(solutions)))
    # Random null-homotopic maps with independently chosen graded H.
    for case in range(48):
        nc,nd=rng.randrange(1,5),rng.randrange(1,5)
        sd=[0]*nc+[1]*nc; td=[0]*nd+[1]*nd
        dC=zeros(2*nc); dD=zeros(2*nd)
        for i in range(nc):dC[i,nc+i]=rng.randint(0,5)
        for i in range(nd):dD[i,nd+i]=rng.randint(0,5)
        Uc,Ud=graded_uni(sd),graded_uni(td); dC=Uc*dC*Uc.inv(); dD=Ud*dD*Ud.inv()
        H=zeros(2*nd,2*nc)
        for i in range(nd):
            for j in range(nc):H[nd+i,j]=rng.randint(-4,4)
        F=dD*H+H*dC; G=zeros(2*nd,2*nc)
        problem=prob('homotopy',source=P.chain_pack(sd,dC),target=P.chain_pack(td,dD),F=F,G=G)
        cert,_=add(f'random-homotopy-{case}','constructed_homotopies',problem,
                   lambda:P.homotopy(sd,dC,td,dD,F,G)[0],'homotopy')
        if F!=G:
            bad=copy.deepcopy(cert); bad['H']['data']=[0]*(4*nd*nc)
            rejected(f'zero-H-{case}',problem,bad)
    # Free obstruction: no differential and nonzero map on homology.
    ds=[0]; d=zeros(1)
    add('free-homotopy-obstruction','free_obstruction',
        prob('homotopy',source=P.chain_pack(ds,d),target=P.chain_pack(ds,d),F=eye(1),G=zeros(1)),
        lambda:P.homotopy(ds,d,ds,d,eye(1),zeros(1))[0],'no_homotopy')
    # Empty complexes and all zero-dimensional equation/variable combinations.
    for ns,nt in [(0,0),(0,2),(2,0)]:
        sd=[0]*ns;td=[0]*nt;dC=zeros(ns);dD=zeros(nt);F=zeros(nt,ns)
        add(f'empty-homotopy-{ns}-{nt}','empty_shapes',
            prob('homotopy',source=P.chain_pack(sd,dC),target=P.chain_pack(td,dD),F=F,G=F),
            lambda:P.homotopy(sd,dC,td,dD,F,F)[0],'homotopy')

def transport_tests():
    for q in [1,2,4,6,8,10,12]:
        ds=[0]*q+[1]*q; d=zeros(2*q); d[:q,q:]=eye(q)
        U=graded_uni(ds); d=U*d*U.inv()
        H=zeros(2*q); H[q:,:q]=Matrix(q,q,[rng.randint(-2,2) for _ in range(q*q)])
        T=d*H+H*d
        cr,_=P.reduction(ds,d); dr,_=P.reduction(ds,d)
        for tag,c in [('C',cr),('D',dr)]:
            add(f'transport-reduction-{q}-{tag}','transport_prerequisite',
                prob('reduction',source=P.chain_pack(ds,d)),lambda:c,'reduction')
        cd=P.unpack(cr['reduced']['d']); dd=P.unpack(dr['reduced']['d'])
        cdeg=cr['reduced']['degrees']; ddeg=dr['reduced']['degrees']
        Tbar=P.unpack(dr['f'])*T*P.unpack(cr['g'])
        cbar,smallstats=P.homotopy(cdeg,cd,ddeg,dd,Tbar,zeros(Tbar.rows,Tbar.cols))
        assert cbar['kind']=='homotopy'
        C.check(prob('homotopy',source=cr['reduced'],target=dr['reduced'],F=Tbar,G=zeros(Tbar.rows,Tbar.cols)),cbar)
        lifted=P.transport_homotopy(cr,dr,T,P.unpack(cbar['H']))
        cp=prob('homotopy',source=P.chain_pack(ds,d),target=P.chain_pack(ds,d),F=T,G=zeros(2*q))
        add(f'lifted-homotopy-{q}','transported_homotopies',cp,
            lambda:dict(kind='homotopy',H=P.pack(lifted)),'homotopy')
        start=time.perf_counter()
        try:
            original,stats=P.homotopy(ds,d,ds,d,T,zeros(2*q))
            C.check(cp,original); status=original['kind']
        except P.SearchLimit:
            status='UNKNOWN_resource_cap'
        direct_seconds=time.perf_counter()-start
        ABLATIONS.append(dict(pairs=q,source_cells=2*q,target_cells=2*q,
                              original_equations=2*q*q,original_variables=q*q,
                              reduced_equations=smallstats['equations'],reduced_variables=smallstats['variables'],
                              direct_outcome=status,direct_seconds=direct_seconds,transport_outcome='homotopy'))
    # Nontrivial reduced object: mixed torsion/contractible components, Hbar nonzero.
    sd=[0,0,1,1]; d=zeros(4);d[0,2]=1;d[1,3]=2
    F=2*eye(4); cr,_=P.reduction(sd,d); Tbar=P.unpack(cr['f'])*F*P.unpack(cr['g'])
    rd=cr['reduced']['degrees'];dd=P.unpack(cr['reduced']['d'])
    bar,_=P.homotopy(rd,dd,rd,dd,Tbar,zeros(*Tbar.shape));assert bar['kind']=='homotopy'
    H=P.transport_homotopy(cr,cr,F,P.unpack(bar['H']))
    add('lifted-nonzero-reduced-homotopy','transported_homotopies',
        prob('homotopy',source=P.chain_pack(sd,d),target=P.chain_pack(sd,d),F=F,G=zeros(4)),
        lambda:dict(kind='homotopy',H=P.pack(H)),'homotopy')

def worked_examples():
    B=Matrix([[-1,-1,0],[1,0,-1],[0,1,1]]); z=Matrix([1,-1,1]); A=2*z
    for scale,expected in [(1,'obstruction'),(2,'fill')]:
        add(f'doubled-face-cycle-{scale}','worked_example',prob('cycle',A=A,B=B,z=scale*z),
            lambda:P.cycle(A,B,scale*z),expected)
    add('doubled-face-homology','worked_example',prob('homology',A=A,B=B),lambda:P.homology(A,B)[0],'homology')
    # Same abstract invariants are not source identity.
    cert=P.cycle(A,B,z)
    rejected('rebind-obstruction-to-zero-cycle',prob('cycle',A=A,B=B,z=zeros(3,1)),cert)
    bad=copy.deepcopy(cert);bad['modulus']=1
    rejected('modulus-one',prob('cycle',A=A,B=B,z=z),bad)
    wrong=prob('cycle',A=A,B=B,z=z);wrong['domain']='Q'
    rejected('wrong-coefficient-domain',wrong,cert)
    for x,label in [(True,'boolean'),(1.0,'floating')]:
        wrong=prob('cycle',A=A,B=B,z=z);wrong['A']['data'][0]=x
        rejected(label+'-coefficient',wrong,cert)
    wrong=prob('cycle',A=A,B=B,z=Matrix([1,0,0]))
    rejected('not-a-cycle',wrong,cert)
    rejected('certificate-list-not-object',prob('cycle',A=A,B=B,z=z),[])
    bad=copy.deepcopy(cert);bad['untrusted_extra_field']='ignore me'
    rejected('unexpected-field',prob('cycle',A=A,B=B,z=z),bad)
    for label,text in [('duplicate','{"kind":1,"kind":2}'),('nan','{"a":NaN}'),('float','{"a":1e0}')]:
        try:C.strict_loads(text)
        except C.Rejected as e:MUTATIONS.append(dict(name='json-'+label,rejected=True,reason=str(e)))
        else:raise AssertionError('bad JSON accepted')
    # Invalid squares in an otherwise legitimate induced-map request.
    F=eye(3); E=eye(3); G=eye(1); ic=P.induced(A,B,A,B,F)
    E[0,0]=2
    rejected('incorrect-lower-square',prob('induced',A=A,B=B,At=A,Bt=B,F=F,E=E,G=G),ic)
    G[0,0]=2
    rejected('incorrect-upper-square',prob('induced',A=A,B=B,At=A,Bt=B,F=F,E=eye(3),G=G),ic)

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,default=Path('../reproduced-results'))
    args=parser.parse_args();out=args.output;out.mkdir(parents=True,exist_ok=True)
    start=time.perf_counter()
    segment_tests(); reduction_tests(); homotopy_tests(); transport_tests();worked_examples()
    summary=dict(seed=SEED,python=sys.version,sympy=sympy.__version__,platform=platform.platform(),
                 certificate_cases=len(CASES),outcomes=dict(collections.Counter(c['expected'] for c in CASES)),
                 families=dict(collections.Counter(c['family'] for c in CASES)),
                 rejection_controls=len(MUTATIONS),oracle_checks=dict(collections.Counter(x['kind'] for x in ORACLES)),
                 ablation_rows=len(ABLATIONS),elapsed_seconds=time.perf_counter()-start,
                 lean_status='NOT_RUN: no Lean executable available',
                 limits=dict(matrix_dimension=C.MAX_DIM,input_coefficient_bits=C.MAX_BITS,
                             homotopy_equations=256,homotopy_variables=256),
                 note='Counts are different units. No Forge/grind tactic comparison. No kernel proof.')
    for name,obj in [('corpus.json',CASES),('summary.json',summary),('mutations.json',MUTATIONS),
                     ('oracles.json',ORACLES),('ablations.json',ABLATIONS),('controls.json',CONTROLS)]:
        (out/name).write_text(json.dumps(obj,indent=2)+'\n')
    with (out/'cases.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(ROWS[0]));writer.writeheader();writer.writerows(ROWS)
    def matrices(obj):
        if isinstance(obj,dict):
            if set(obj)=={'rows','cols','data'}: yield obj
            else:
                for value in obj.values(): yield from matrices(value)
        elif isinstance(obj,list):
            for value in obj: yield from matrices(value)
    mats=list(matrices(CASES))
    sizes=dict(max_matrix_dimension=max(max(m['rows'],m['cols']) for m in mats),
               max_coefficient_bits=max(abs(x).bit_length() for m in mats for x in m['data']),
               serialized_corpus_bytes=(out/'corpus.json').stat().st_size,
               largest_certificate_compact_bytes=max(r['certificate_bytes'] for r in ROWS))
    (out/'corpus-size.json').write_text(json.dumps(sizes,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':main()
