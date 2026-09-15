"""R2 full legal D6 game. Width counts physical coordinates: |G|+h,
scalar width=1. Cost*variance=r**z. Allocation mass is COST mass.
Oracle B-only width envelopes do not define this game's allocation.
"""
from pathlib import Path
import sys,importlib.util,itertools,json,hashlib,time
# in-repo dependency (the original pointed outside the repo, at a path that
# does not exist here); see DEPENDENCY_HASHES.json for the recorded sha256.
base=Path(__file__).resolve().parents[1]/'worker_distinct_research_acceptance_20260913'
if not (base/'approximate_game.py').exists():
    raise FileNotFoundError(f'game dependency missing: {base}/approximate_game.py')
spec=importlib.util.spec_from_file_location('game',base/'approximate_game.py')
g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)
np=g.np
original=g.problem

def width(key):return 1 if key[0]=='s' else int(key[1])+sum(key[2:])

def solve(q,mu,z):
    def weighted(*args,**kwargs):
        queries,keys,counts,alts=original(*args,**kwargs)
        scale=np.array([width(k)**z for k in keys])
        return queries,keys,counts,[(a,d,c/scale) for a,d,c in alts]
    g.problem=weighted
    try:r=g.solve(q,0,mu,0)
    finally:g.problem=original
    r['z']=z;r['cost_mass_by_width']={str(w):sum(a['mass'] for a in r['allocation'] if width(a['orbit'])==w) for w in range(1,q+2)}
    verify(r)
    return r

def verify(r):
    q=r['q'];mu=r['mu'];z=r['z'];coords=range(2*q+1);j=2*q+1;A=set(range(q+1))
    queries=[('s',i) for i in range(2*q+2)]+[('g',set(G),h) for n in range(q+1) for G in itertools.combinations(coords,n) for h in (0,1) if h or n>=2]
    def key(e):
        if e[0]=='s':return ('s',4 if e[1]==j else 0 if e[1] in A else 3)
        return ('g',bool(e[2]),len(e[1]&A),0,0,len(e[1]-A))
    masses={tuple(a['orbit']):a['mass']/a['orbit_size'] for a in r['allocation']}
    w=np.array([masses.get(key(e),0.) for e in queries]); widths=np.array([1 if e[0]=='s' else len(e[1])+e[2] for e in queries],float)
    def affine(C,e):
        if e[0]=='s':return (1,0) if e[1] in C else (-1,1) if e[1]==j else (1,-1)
        k=len(e[1]-C);h=e[2];return 1+k-2*h,h-k
    true=np.array([a+b*mu for a,b in (affine(A,e) for e in queries)])
    lo=float('inf')
    for tup in itertools.combinations(coords,q+1):
        C=set(tup)
        if C==A:continue
        aa,bb=np.array([affine(C,e) for e in queries]).T
        d=true-aa; ww=w/widths**z
        c=float(ww@(bb*bb)); b=float(ww@(d*bb))
        nu=float(np.clip(b/c,0,1)) if c>1e-15 else 0.
        lo=min(lo,float(ww@((d-bb*nu)**2)/2))
    # Expand the stabilizer orbit of each dual label. Raw representatives alone
    # need not give the same upper bound on individual (non-orbit) queries.
    uppervec=np.zeros(len(queries))
    for d in r['dual_alternatives']:
        C=set(d['alternative']); na=len(C&A);nb=len(C-A)
        labels=[set(a)|set(b) for a in itertools.combinations(sorted(A),na) for b in itertools.combinations(sorted(set(coords)-A),nb)]
        for C in labels:
            means=np.array([a+b*d['nu_in_closure'] for a,b in (affine(C,e) for e in queries)])
            uppervec+=d['probability']/len(labels)*(true-means)**2/(2*widths**z)
    assert abs(w.sum()-1)<1e-8
    assert abs(lo-r['lower'])<1e-8
    assert abs(float(uppervec.max())-r['upper'])<1e-8
    assert float(uppervec.max())-lo<2.1e-8
    r['independent_full_enumeration']={'lower':lo,'upper':float(uppervec.max()),'all_legal_queries':len(queries),'passed':True}

if __name__=='__main__':
    start=time.time();rows=[]
    for q in (3,4):
        for mu in (.25,.5,.75):
            for z in (0,.5,1,1.25,1.5,1.75,2,2.5):
                r=solve(q,mu,z);rows.append(r)
                print(q,mu,z,r['lower'],r['cost_mass_by_width'],flush=True)
    out={'status':'complete','source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'solver_sha256':hashlib.sha256((base/'approximate_game.py').read_bytes()).hexdigest(),
      'model':'Cost mass simplex, cost times variance = physical width**z; width |G|+h, scalar 1. Maximum width q+1 for h=true. No adaptive stopping claim.',
      'seconds':time.time()-start,'results':rows}
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
