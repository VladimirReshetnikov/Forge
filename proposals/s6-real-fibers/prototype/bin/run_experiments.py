#!/usr/bin/env python3
"""Generate reproducible evidence. Default never overwrites the delivered run."""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
import argparse,json,random,time,platform,copy,traceback
from datetime import datetime,timezone
from fractions import Fraction as Q
from itertools import product
import sympy as s
from real_fibers.producer import produce,make_problem,sparse,produce_outer,produce_witness,truth_table_indicator
from real_fibers.checker import verify,check_charpoly
from real_fibers.exact import P,Reject,Limit,qjson,sgn,signature_from_signs,poly
from real_fibers.logic import indicator,eval_formula
from real_fibers.outer import verify_outer
from real_fibers.witness import verify_witness
SEED=20260915
rng=random.Random(SEED)
x,y,t,u=s.symbols('x y t u')
A=lambda i,r:['atom',i,r]
C=lambda rel,n:['count',rel,n]
AND=lambda a,b:['and',a,b]
IFF=lambda a,b:['iff',a,b]
IMP=lambda a,b:['implies',a,b]
NOT=lambda a:['not',a]

def random_formula(m,depth=2):
    if depth==0 or rng.random()<.4:return A(rng.randrange(m),rng.choice(['lt','le','eq','ne','ge','gt']))
    if rng.random()<.15:return NOT(random_formula(m,depth-1))
    return [rng.choice(['and','or','iff','implies']),random_formula(m,depth-1),random_formula(m,depth-1)]

def root_oracle(f,qs,formula):
    """SymPy root isolation/counting, not matrix signatures or replay Sturm code."""
    F=s.Poly(f,x,domain=s.QQ);allpoly=F
    for q in qs:
        q=s.Poly(q,x,domain=s.QQ)
        if not q.is_zero:allpoly*=q
    total=0
    for (a,b),_ in s.intervals(allpoly.sqf_part(),eps=s.Rational(1,4096)):
        if a==b:
            if F.eval(a)!=0:continue
            signs=[int(s.sign(q.subs(x,a))) for q in qs]
        else:
            if F.count_roots(a,b)!=1:continue
            signs=[]
            for q in qs:
                Qp=s.Poly(q,x,domain=s.QQ)
                if Qp.is_zero or Qp.count_roots(a,b)==1:signs.append(0)
                else:signs.append(int(s.sign(Qp.eval((a+b)/2))))
        total+=int(eval_formula(formula,signs))
    return total

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[2]/'reproduced-results')
    out=parser.parse_args().output
    if out.exists() and any(out.iterdir()):raise SystemExit('Refusing to overwrite nonempty run directory; choose another --output.')
    out.mkdir(parents=True,exist_ok=True);(out/'certificates').mkdir()
    summary={'seed':SEED,'python':sys.version,'sympy':s.__version__,'platform':platform.platform(),
      'started_utc':datetime.now(timezone.utc).isoformat(),'lean_status':'NOT_RUN: no Lean executable available','counts':{},
      'notes':['Not combined with any Forge repository run.','Python replay is not Lean kernel checking.',
               'Producer and root oracle both use SymPy; matrix-signature replay does not.',
               'Outer product assembly and verdict evaluation are shared with the producer.']}
    mutations=[];saved=[];start=time.perf_counter()
    def event(kind,**fields):
        with (out/'records.jsonl').open('a') as fd:fd.write(json.dumps({'kind':kind,**fields},sort_keys=True)+'\n')
    def save(name,kind,problem,cert,**extra):
        b={'kind':kind,'name':name,'problem':problem,'certificate':cert,**extra}
        (out/'certificates'/f'{name}.json').write_text(json.dumps(b,sort_keys=True,indent=2)+'\n');saved.append(b)
    def mutate(name,kind,problem,cert,label,change):
        p,c=copy.deepcopy(problem),copy.deepcopy(cert);change(p,c)
        try:{'fiber':verify,'outer':verify_outer,'witness':verify_witness}[kind](p,c)
        except Reject as e:
            mutations.append({'name':name,'kind':kind,'problem':p,'certificate':c,'mutation':label,'expected':'reject','reason':str(e)});return
        raise AssertionError(f'accepted mutation {name}: {label}')
    try:
        booleans=[];observations=0
        for i in range(160):
            m=1+i%4;form=random_formula(m,3);p=indicator(form,m);a=truth_table_indicator(form,m);assert p==a
            for signs in product((-1,0,1),repeat=m):
                assert p.eval(signs)==int(eval_formula(form,signs));observations+=1
            booleans.append({'m':m,'formula':form,'indicator':p.data()})
        (out/'boolean-fixtures.json').write_text(json.dumps(booleans))
        summary['counts'].update(boolean_formulas=160,boolean_truth_assignments=observations)
        print('Boolean formulas:',160,'truth assignments:',observations,flush=True)
        signatures=[]
        for i in range(90):
            d=1+i%6;diag=[rng.randint(-3,3) for _ in range(d)];T=s.eye(d)
            for r in range(d):
                for c in range(r):T[r,c]=rng.randint(-2,2)
            H=T.T*s.diag(*diag)*T;cs=H.charpoly().all_coeffs()
            Hp=[[P.const(0,int(H[r,c])) for c in range(d)] for r in range(d)]
            cp=[P.const(0,int(a)) for a in cs];check_charpoly(Hp,cp)
            actual=signature_from_signs([sgn(int(a)) for a in cs]);expected=sum(sgn(a) for a in diag);assert actual==expected
            signatures.append({'diagonal':diag,'unit_lower_triangular':[[int(a) for a in row] for row in T.tolist()],
              'hermite':[[int(a) for a in row] for row in H.tolist()],'charpoly':[int(a) for a in cs],'expected_signature':expected})
        (out/'signature-fixtures.json').write_text(json.dumps(signatures));summary['counts']['signature_matrices']=90
        print('Signature matrices:',90,flush=True)
        unique_nonneg=IFF(C('eq',1),A(0,'ge'));unique_pos=IFF(C('eq',1),A(0,'gt'))
        piece_shift=AND(IMP(A(0,'lt'),C('eq',0)),AND(IMP(A(0,'eq'),C('eq',1)),AND(IMP(AND(A(0,'gt'),A(1,'lt')),C('eq',2)),IMP(A(1,'ge'),C('eq',1)))))
        total_cubic=AND(IMP(A(0,'gt'),C('eq',3)),IMP(A(0,'le'),C('eq',1)))
        specs=[
          ('sqrt_nonnegative',[x*x-t],[x],A(0,'ge'),[t],unique_nonneg,True,lambda z:int(z>=0)),
          ('sqrt_positive',[x*x-t],[x],A(0,'gt'),[t],unique_pos,True,lambda z:int(z>0)),
          ('shifted_positive',[(x-2)**2-t],[x],A(0,'gt'),[t,t-4],piece_shift,True,lambda z:0 if z<0 else (2 if 0<z<4 else 1)),
          ('cubic_total',[x**3-t*x],[],['true'],[t],total_cubic,True,lambda z:3 if z>0 else 1),
          ('cubic_positive',[x**3-t*x],[x],A(0,'gt'),[t],unique_pos,True,lambda z:int(z>0)),
          ('nested_positive',[x*x-t,y*y-x],[y],A(0,'gt'),[t],unique_pos,True,lambda z:int(z>0)),
          ('quadrant',[x*x-t,y*y-t],[x,y],AND(A(0,'gt'),A(1,'gt')),[t],unique_pos,True,lambda z:int(z>0)),
          ('correlation',[x*x-1],[x,-x],AND(A(0,'gt'),A(1,'gt')),[],C('eq',0),True,lambda z:0),
          ('repeated_root',[(x-t)**4],[x],A(0,'gt'),[t],unique_pos,True,lambda z:int(z>0)),
          ('empty_real_fiber',[x*x+1],[],['true'],[],C('eq',0),True,lambda z:0),
          ('nonzero_roots',[x*x-t],[x],A(0,'ne'),[t],AND(IMP(A(0,'gt'),C('eq',2)),IMP(A(0,'le'),C('eq',0))),True,lambda z:2 if z>0 else 0),
          ('fourth_root',[x**4-t],[x],A(0,'ge'),[t],unique_nonneg,True,lambda z:int(z>=0)),
          ('boundary_only_false',[x*x-t],[x],A(0,'gt'),[t],IMP(A(0,'ge'),C('eq',1)),False,lambda z:int(z>0)),
          ('algebraic_boundary_false',[x*x-(t*t-2)],[x],A(0,'gt'),[t*t-2],IMP(A(0,'ge'),C('eq',1)),False,lambda z:int(z*z>2)),
          ('algebraic_boundary_true',[x*x-(t*t-2)],[x],A(0,'gt'),[t*t-2],IFF(C('eq',1),A(0,'gt')),True,lambda z:int(z*z>2)),
          ('quintic_positive',[x**5-x-t],[x],A(0,'gt'),[t],IMP(A(0,'ge'),C('eq',1)),True,lambda z:1 if z>=0 else (2 if 3125*z**4<256 else (1 if 3125*z**4==256 else 0))),
          ('all_fiber_points_nonnegative',[x*x-t],[x],A(0,'lt'),[t],IFF(C('eq',0),A(0,'le')),True,lambda z:int(z>0)),
        ]
        specialized=0;outer_cells=0;named_data=[]
        grid=sorted(set([Q(i,3) for i in range(-15,19)]+[Q(0),Q(4),Q(1),Q(2)]))
        for name,fs,qs,form,pas,condition,want,expect in specs:
            xs=[x] if len(fs)==1 else [x,y];p=make_problem([t],xs,fs,qs,form)
            o={'schema':'outer-one-parameter-v1','fiber':p,'parameter_atoms':[sparse(a,(t,)).data() for a in pas],'condition':condition,'quantifier':'forall'}
            st=time.perf_counter();c=produce_outer(o);production=time.perf_counter()-st
            st=time.perf_counter();v=verify_outer(o,c);replay=time.perf_counter()-st;assert v.value==want
            cf=verify(p,c['fiber_certificate']);sample_rows=[]
            for z in grid:
                got=cf.count([z]);assert got==expect(z),(name,z,got,expect(z));specialized+=1
                sample_rows.append({'parameters':[qjson(z)],'count':got})
            if name in ('boundary_only_false','algebraic_boundary_false'):
                assert all(row['condition'] for row in v.cells if row['kind']=='sector')
                assert any(not row['condition'] for row in v.cells if row['kind']=='section')
            outer_cells+=len(v.cells);save(name,'outer',o,c,expected=want,specializations=sample_rows,cells=v.cells)
            row={'name':name,'dimension':cf.fiber.d,'atoms':len(qs),'queries':len(c['fiber_certificate']['queries']),
                 'full_sign_queries':3**len(qs),'outer_product_degree':v.root_degree,'cells':len(v.cells),'value':v.value,
                 'producer_seconds':production,'replay_seconds':replay,'certificate_bytes':len(json.dumps(c,separators=(',',':')))}
            named_data.append(row);event('named_outer',**row)
            mutate(name,'outer',o,c,'flip verdict',lambda p,c:c.__setitem__('claim',not c['claim']))
            if c['roots']:
                mutate(name,'outer',o,c,'omit boundary',lambda p,c:c['roots'].pop())
                mutate(name,'outer',o,c,'degenerate interval',lambda p,c:c['roots'][0].__setitem__(1,c['roots'][0][0]))
            print('Outer:',name,'=',v.value,'cells',len(v.cells),flush=True)
        summary['counts'].update(named_outer_problems=len(specs),named_parameter_specializations=specialized,outer_cells=outer_cells,
          outer_true=sum(row['value'] for row in named_data),outer_false=sum(not row['value'] for row in named_data))
        for name,ff,form,pas,condition,want in [
          ('existential_impossible',x*x-t,A(0,'gt'),[],C('eq',2),False),
          ('existential_algebraic_section',x*x-(t*t-2),A(0,'ge'),[t*t-2],AND(A(0,'eq'),C('eq',1)),True)]:
            p=make_problem([t],[x],[ff],[x],form)
            o={'schema':'outer-one-parameter-v1','fiber':p,'parameter_atoms':[sparse(a,(t,)).data() for a in pas],
               'condition':condition,'quantifier':'exists'}
            cert=produce_outer(o);v=verify_outer(o,cert);assert v.value==want
            if want:assert v.cells[v.decisive_cell]['kind']=='section'
            save(name,'outer',o,cert,expected=want,cells=v.cells)
            summary['counts']['outer_cells']+=len(v.cells)
            summary['counts']['outer_true']+=int(want);summary['counts']['outer_false']+=int(not want)
            mutate(name,'outer',o,cert,'flip existential verdict',lambda p,c:c.__setitem__('claim',not c['claim']))
            print('Existential:',name,'=',v.value,flush=True)
        summary['counts']['existential_outer_problems']=2
        summary['named_outer']=named_data
        for name,f,qs,form in [('depressed_cubic',x**3+t*x+u,[x],A(0,'gt')),('two_parameter_collision',x*x-(t-u)**2,[x],A(0,'gt'))]:
            p=make_problem([t,u],[x],[f],qs,form);c=produce(p);v=verify(p,c);samples=[]
            for a,b in product(range(-3,4),repeat=2):
                got=v.count([a,b]);want=root_oracle(f.subs({t:a,u:b}),[q.subs({t:a,u:b}) for q in qs],form);assert got==want
                samples.append({'parameters':[qjson(a),qjson(b)],'count':got})
            save(name,'fiber',p,c,specializations=samples)
        summary['counts'].update(two_parameter_families=2,two_parameter_specializations=98)
        print('Two-parameter specializations:',98,flush=True)
        for i in range(48):
            d=1+i%5;f=x**d+sum(rng.randint(-3,3)*x**j for j in range(d))
            if i%6==0:f=(x-rng.randint(-2,2))**min(d+1,5)
            qs=[x+rng.randint(-2,2),x*x+rng.randint(-2,2)*x+rng.randint(-2,2)];form=random_formula(2,2)
            p=make_problem([],[x],[f],qs,form);c=produce(p);v=verify(p,c);want=root_oracle(f,qs,form)
            assert v.count([])==want,(f,qs,form,v.count([]),want)
            save(f'random_univariate_{i:03}','fiber',p,c,specializations=[{'parameters':[],'count':want}])
        summary['counts']['random_univariate_problems']=48;print('Random univariate:',48,flush=True)
        for i in range(24):
            rs=[Q(rng.randint(-3,3)) for _ in range(2+i%2)];a,b,c,d=[rng.randint(-2,2) for _ in range(4)]
            fx=s.prod(x-s.Rational(z.numerator,z.denominator) for z in rs);fy=(y-(a*x+b))*(y-(c*x+d))
            qs=[x+y-rng.randint(-2,2),x*y-rng.randint(-2,2)];form=random_formula(2,2)
            p=make_problem([],[x,y],[fx,fy],qs,form);cert=produce(p);v=verify(p,cert)
            points={(xx,yy) for xx in rs for yy in (a*xx+b,c*xx+d)};ps=[sparse(q,(x,y)) for q in qs]
            want=sum(eval_formula(form,[sgn(q.eval(z)) for q in ps]) for z in points);assert v.count([])==want
            save(f'random_triangular_{i:03}','fiber',p,cert,specializations=[{'parameters':[],'count':want}],
                 oracle_points=[[qjson(xx),qjson(yy)] for xx,yy in sorted(points)])
        summary['counts']['random_triangular_problems']=24;print('Random triangular:',24,flush=True)
        witness_specs=[('sqrt2_witness',x*x-2,[x],A(0,'gt')),
          ('sqrt3_bounded',x*x-3,[x-1,2-x],AND(A(0,'gt'),A(1,'gt'))),
          ('repeated_witness',(x*x-2)**2,[x],A(0,'gt')),
          ('equality_witness',(x-1)*(x+2),[x-1],A(0,'eq')),
          ('fifth_root_witness',x**5-x-1,[x-1,2-x],AND(A(0,'gt'),A(1,'gt'))),
          ('negative_witness',x*x-2,[x],A(0,'lt'))]
        for name,f,qs,form in witness_specs:
            p=make_problem([],[x],[f],qs,form);c=produce_witness(p);assert c is not None;v=verify_witness(p,c)
            save(name,'witness',p,c,expected_signs=v['atom_signs'])
            mutate(name,'witness',p,c,'negate contract',lambda p,c:p.__setitem__('formula',NOT(p['formula'])))
            mutate(name,'witness',p,c,'collapsed isolator',lambda p,c:c['interval'].__setitem__(1,c['interval'][0]))
        summary['counts']['algebraic_witnesses']=len(witness_specs);print('Witnesses:',len(witness_specs),flush=True)
        def changed_poly(data,n):return (poly(data,n)+1).data()
        for bundle in list(saved):
            if bundle['kind'] not in ('fiber','outer'):continue
            kind=bundle['kind'];p=bundle['problem']['fiber'] if kind=='outer' else bundle['problem'];c=bundle['certificate']['fiber_certificate'] if kind=='outer' else bundle['certificate']
            if not c['queries']:continue
            name=bundle['name']
            for j in range(len(c['queries'])):
                mutate(name,'fiber',p,c,f'change matrix query {j}',lambda p,c,j=j:c['queries'][j]['hermite'][0].__setitem__(0,changed_poly(c['queries'][j]['hermite'][0][0],p['parameters'])))
                mutate(name,'fiber',p,c,f'change charpoly query {j}',lambda p,c,j=j:c['queries'][j]['charpoly'].__setitem__(-1,changed_poly(c['queries'][j]['charpoly'][-1],p['parameters'])))
                mutate(name,'fiber',p,c,f'change weight query {j}',lambda p,c,j=j:c['queries'][j].__setitem__('coefficient',qjson(Q(*c['queries'][j]['coefficient'])+1)))
            mutate(name,'fiber',p,c,'omit query',lambda p,c:c['queries'].pop())
        b=saved[0];p=b['problem']['fiber'];c=b['certificate']['fiber_certificate']
        mutate('schema','fiber',p,c,'float coefficient',lambda p,c:c['queries'][0].__setitem__('coefficient',[0.5,1]))
        mutate('schema','fiber',p,c,'bool parameter arity',lambda p,c:p.__setitem__('parameters',True))
        mutate('schema','fiber',p,c,'nonmonic equation',lambda p,c:p['equations'].__setitem__(0,(2*P.make(2,[((0,2),1)])).data()))
        mutate('source','fiber',p,c,'change source polynomial',lambda p,c:p['equations'].__setitem__(0,(P.make(2,[((0,2),1),((1,0),-1)])+1).data()))
        mutate('source','fiber',p,c,'change strictness',lambda p,c:p.__setitem__('formula',A(0,'gt')))
        (out/'mutations.json').write_text(json.dumps(mutations,sort_keys=True))
        summary['counts'].update(invalid_mutations_rejected=len(mutations),stored_valid_bundles=len(saved))
        summary['elapsed_seconds']=time.perf_counter()-start;summary['finished_utc']=datetime.now(timezone.utc).isoformat();summary['status']='PASS'
        (out/'summary.json').write_text(json.dumps(summary,indent=2,sort_keys=True)+'\n');print(json.dumps(summary['counts'],indent=2),flush=True)
    except Exception:
        summary['status']='FAIL';summary['elapsed_seconds']=time.perf_counter()-start
        (out/'summary.json').write_text(json.dumps(summary,indent=2,sort_keys=True)+'\n');(out/'failure.txt').write_text(traceback.format_exc());raise
if __name__=='__main__':main()
