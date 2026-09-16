"""Targeted invalid-evidence controls, kept separate from positive examples."""
from pathlib import Path
from copy import deepcopy
import json,time
from atlas.io import load
from atlas.checker import verify
ROOT=Path(__file__).resolve().parents[1]

def changes(p,c):
    def emit(name,fn,source=False):
        pp,cc=deepcopy(p),deepcopy(c);fn(pp if source else cc);return name,pp,cc
    yield emit('missing_base_stack',lambda z:z['stacks'].pop())
    yield emit('wrong_projected_truth',lambda z:z['truth_by_x'].__setitem__(0,not z['truth_by_x'][0]))
    yield emit('wrong_closed_result',lambda z:z.__setitem__('closed_value',not z['closed_value']))
    yield emit('malformed_quantifier',lambda z:z.__setitem__('inner','almost_all'),True)
    yield emit('invalid_atom',lambda z:z.__setitem__('formula',['eq',len(z['polynomials'])]),True)
    yield emit('float_x_sample',lambda z:z['stacks'][0].__setitem__('sample',0.0))
    yield emit('noncanonical_x_sample',lambda z:z['stacks'][0].__setitem__('sample','0/1'))
    yield emit('missing_y_sign_row',lambda z:z['stacks'][0]['signs'].pop())
    yield emit('missing_y_sector_sample',lambda z:z['stacks'][0]['y_samples'].pop())
    yield emit('wrong_inner_result',lambda z:z['stacks'][0].__setitem__('value',not z['stacks'][0]['value']))
    yield emit('wrong_factorization_scalar',lambda z:z['factorizations'][0].__setitem__('scalar',str(int(z['factorizations'][0]['scalar'])+1)))
    if c['stacks'][0]['signs'][0]:
        yield emit('incorrect_sign',lambda z:z['stacks'][0]['signs'][0].__setitem__(0,1 if z['stacks'][0]['signs'][0][0]!=1 else -1))
        yield emit('boolean_in_sign_row',lambda z:z['stacks'][0]['signs'][0].__setitem__(0,True))
    if c['derivative_guards']:
        yield emit('missing_derivative_guard',lambda z:z['derivative_guards'].pop())
        yield emit('zero_derivative_guard',lambda z:z['derivative_guards'][0].__setitem__('guard',[]))
        yield emit('boolean_derivative_index',lambda z:z['derivative_guards'][0].__setitem__('factor',False))
    if c['pair_guards']:
        yield emit('missing_pair_guard',lambda z:z['pair_guards'].pop())
        yield emit('zero_pair_guard',lambda z:z['pair_guards'][0].__setitem__('guard',[]))
    if c['base_roots']:
        yield emit('missing_base_root',lambda z:z['base_roots'].pop())
        yield emit('invalid_base_cut',lambda z:z['base_roots'].__setitem__(0,['5','-5']))
    for i,s in enumerate(c['stacks']):
        if s['y_roots']:
            yield emit('missing_fiber_root',lambda z:z['stacks'][i]['y_roots'].pop())
            yield emit('invalid_fiber_cut',lambda z:z['stacks'][i]['y_roots'].__setitem__(0,['5','-5']))
            break
    for i,s in enumerate(c['stacks']):
        if s['selection'] is not None:
            yield emit('selection_out_of_range',lambda z:z['stacks'][i].__setitem__('selection',100000))
            break
    if c['factors']:
        yield emit('factor_with_float',lambda z:z['factors'][0][0].__setitem__(2,1.0))
        yield emit('missing_factorization_power',lambda z:next(f for f in z['factorizations'] if f['powers'])['powers'].pop())

def main():
    records=[];t=time.perf_counter()
    for pp in sorted((ROOT/'examples').glob('*/problem.json')):
        p,c=load(pp),load(pp.with_name('certificate.json'))
        verify(p,c)
        for name,p2,c2 in changes(p,c):
            try:verify(p2,c2)
            except (ValueError,ArithmeticError,TypeError,KeyError,IndexError) as e:
                records.append({'example':p['name'],'mutation':name,'rejected':True,'reason':str(e)})
            else:raise AssertionError(('accepted invalid mutation',p['name'],name))
    out={'attempts':len(records),'rejected':len(records),'seconds':time.perf_counter()-t,'records':records}
    (ROOT/'results'/'mutations.json').write_text(json.dumps(out,indent=2)+'\n')
    print({k:v for k,v in out.items() if k!='records'})
if __name__=='__main__':main()
