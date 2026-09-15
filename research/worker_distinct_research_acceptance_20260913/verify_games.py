"""Independent full-label and full-query evaluator of saved certificates.
Does not import the optimization code or its orbit coefficient builder.
Each dual representative is expanded to its complete stabilizer orbit.
"""
from pathlib import Path
import sys,json,itertools
sys.path.insert(0,str(Path(__file__).parent/'python_deps'))
import numpy as np

def verify(cell,bias=False):
    q=cell['q'];mu=cell['mu'];eps=cell.get('epsilon',0.);d=cell.get('answer_shell',0)
    n=2*q+1;A=set(range(q+1));B=set(range(q+1-d))|set(range(q+1,q+1+d))
    groups=[A&B,A-B,B-A,set(range(n))-(A|B)]
    labels=[set(x) for x in itertools.combinations(range(n),q+1)]
    queries=[('s',i) for i in range(n+1)]
    queries.extend(('g',set(G),h) for r in range(q+1) for G in itertools.combinations(range(n),r)
                   for h in [False,True] if h or r>=2)
    def key(e):
        if e[0]=='s':return ('s',4 if e[1]==n else next(k for k,g in enumerate(groups) if e[1] in g))
        return ('g',e[2],*(len(e[1]&g) for g in groups))
    def mean(label,margin):
        # Reconstruct from signed actual-coordinate contributions.
        v=[]
        for e in queries:
            if e[0]=='s':v.append(1 if e[1] in label else margin-1 if e[1]==n else 1-margin)
            else:
                k=sum(i not in label for i in e[1])
                v.append((k-1)*(1-margin) if e[2] else 1+k*(1-margin))
        return np.array(v,dtype=float)
    mass={tuple(a['orbit']):a['mass']/a['orbit_size'] for a in cell['allocation']}
    w=np.array([mass.get(key(e),0.) for e in queries]);assert abs(w.sum()-1)<1e-8
    true=mean(A,mu);lo=float('inf');bad=[];maxzero=0.
    for label in labels:
        distance=len(label-B)
        if distance<=eps:continue
        ub=min(1.,2-2*eps/distance)
        off=mean(label,0);slope=mean(label,1)-off;diff=true-off
        if bias:
            diff=diff-diff@w;slope=slope-slope@w
        C=(w*diff**2).sum()/2;H=(w*slope**2).sum()/2;T=-(w*diff*slope).sum()
        nu=min(ub,max(0.,-T/(2*H))) if H>1e-15 else (ub if T<0 else 0.)
        value=C+T*nu+H*nu**2;lo=min(lo,float(value));bad.append(label)
    dualvec=np.zeros(len(queries));psum=0
    for rec in cell['dual_alternatives']:
        rep=set(rec['alternative']);shape=tuple(len(rep&g) for g in groups)
        members=[l for l in labels if tuple(len(l&g) for g in groups)==shape]
        nu=rec['nu'] if bias else rec['nu_in_closure'];u=rec.get('offset',0)
        distance=len(rep-B);assert distance>eps
        assert -1e-9<=nu<=min(1.,2-2*eps/distance)+1e-9
        p=rec['probability'];psum+=p
        for label in members:
            dif=true-mean(label,nu)-u
            dualvec+=p/len(members)*dif**2/2
    assert abs(psum-1)<1e-8
    up=float(dualvec.max())
    assert abs(lo-cell['lower'])<2e-8,(q,eps,d,lo,cell['lower'])
    assert abs(up-cell['upper'])<2e-8,(q,eps,d,up,cell['upper'])
    assert up-lo<5e-8 and lo>=-1e-10
    return {'q':q,'epsilon':eps,'answer_shell':d,'bias':bias,'full_labels':len(labels),
            'full_queries':len(queries),'lower':lo,'upper':up,'gap':up-lo}

def main():
    r=Path(__file__).parent
    approx=json.loads((r/'approximate_game.json').read_text())
    calibration=json.loads((r/'calibration_game.json').read_text())
    out=[verify(c) for x in approx['results'] for c in x['shells']]
    out += [verify(c,True) for c in calibration['results']]
    # Mutation controls independently reject changed claimed bounds and exposure.
    import copy
    rejected=0
    for kind in ['lower','upper','mass']:
        c=copy.deepcopy(approx['results'][0]['shells'][0])
        if kind=='mass':c['allocation'][0]['mass']+=.1
        else:c[kind]+=.1
        try:verify(c)
        except AssertionError:rejected+=1
    assert rejected==3
    (r/'verify_games.json').write_text(json.dumps({'passed':True,'cells':out,
         'mutation_controls_rejected':rejected,'method':'full enumeration independent of solver coefficients'},indent=2)+'\n')
    print(len(out),'certificates checked on all labels/queries;',rejected,'mutations rejected')
if __name__=='__main__':main()
