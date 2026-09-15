"""Check rational certificates without calling the optimizer or a numeric solver."""
from fractions import Fraction as F
from itertools import product,permutations
import json,hashlib,copy
from pathlib import Path
from exact_oracle import region

def dot(a,b):return sum((u*v for u,v in zip(a,b)),F(0))
def verify(r):
    pi,pj,ti,tj=[list(map(F,r[k])) for k in ['precision_i','precision_j','theta_i','theta_j']]
    assert min(pi+pj)>0
    expected={(s,p,o) for s,p,o in product((''.join(v) for v in product('LMU',repeat=3)),permutations(range(3),2),(False,True))}
    seen=set();lower=[]
    for rec in r['regions']:
        key=(rec['states'],tuple(rec['pair']),rec['opening']);assert key in expected and key not in seen;seen.add(key)
        H,g,c,cons=region(pi,pj,ti,tj,*key)
        assert H[0][1]==H[1][0] and H[0][0]>=0 and H[1][1]>=0 and H[0][0]*H[1][1]>=H[0][1]**2
        multipliers=[(i,F(v)) for i,v in rec['multipliers']]
        assert len({i for i,_ in multipliers})==len(multipliers)
        assert all(0<=i<len(cons) and v>=0 for i,v in multipliers)
        normal=tuple(sum((v*cons[i][0][j] for i,v in multipliers),F(0)) for j in range(2))
        if rec['kind']=='infeasible':
            assert normal==(0,0) and sum((v*cons[i][1] for i,v in multipliers),F(0))>0
        else:
            assert rec['kind']=='optimal';x=tuple(map(F,rec['point']))
            assert all(dot(a,x)>=b for a,b in cons)
            assert all(v*(dot(cons[i][0],x)-cons[i][1])==0 for i,v in multipliers)
            grad=tuple(dot(H[j],x)+g[j] for j in range(2));assert grad==normal
            value=dot(x,tuple(dot(row,x) for row in H))/2+dot(g,x)+c
            assert value==F(rec['value']);lower.append(value)
    assert seen==expected and min(lower)==F(r['value'])
    vi,vj=[list(map(F,r[k])) for k in ['alternative_i','alternative_j']]
    assert max(vi)-min(vi)<=max(vj)-min(vj)
    actual=sum((p*(v-t)**2/2 for pp,vv,tt in [(pi,vi,ti),(pj,vj,tj)] for p,v,t in zip(pp,vv,tt)),F(0))
    assert actual==F(r['value'])
    if r['family']=='cheap_middle':assert 0<=actual/F(r['scalar'])<=9*F(r['eta'])
    if r['family']=='cheap_maximum':assert actual>=F(1,128) and actual/F(r['scalar'])>=(1+3*F(r['eta']))/(16*F(r['eta']))
    if r['family'] in ('tie','flat'):assert actual==0

def must_reject(r):
    try:verify(r)
    except AssertionError:return
    raise AssertionError('Corrupted certificate unexpectedly accepted')

if __name__=='__main__':
    p=Path(__file__).with_name('exact_oracle_certificates.json');data=json.loads(p.read_text())
    for r in data:verify(r)
    x=copy.deepcopy(data[0]);x['value']=str(F(x['value'])+1);must_reject(x)
    x=copy.deepcopy(data[0]);x['regions'].pop();must_reject(x)
    x=copy.deepcopy(data[0]);rec=next(v for v in x['regions'] if v['kind']=='optimal');rec['value']=str(F(rec['value'])+1);must_reject(x)
    x=copy.deepcopy(data[0]);rec=next(v for v in x['regions'] if v['kind']=='infeasible');rec['multipliers']=[];must_reject(x)
    out={'accepted':True,'instances':len(data),'regions_per_instance':324,'regions_verified':sum(len(r['regions']) for r in data),'negative_controls_rejected':4,'certificate_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'scope':'two free relations, three actions, positive rational precisions; tie alternative'}
    Path(__file__).with_name('exact_oracle_verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
