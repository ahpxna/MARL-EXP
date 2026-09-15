"""D6 multiple-answer characteristic game, all legal queries, unit variance/cost.
Orbit reduction is under permutations preserving BOTH true label and answer.
Open bad-nuisance intervals are minimized by continuity on their nonempty closure.
Numerical LP bounds are reported with residuals, not called exact certificates.
"""
from pathlib import Path
import sys,itertools,json,math,time
sys.path.insert(0,str(Path(__file__).parent/'python_deps'))
import numpy as np
from scipy.optimize import linprog

def subsets(items,r):
    return (frozenset(x) for x in itertools.combinations(items,r))

def problem(q,shell,mu,calibration=False):
    coords=list(range(2*q+1)); j=2*q+1; A=frozenset(range(q+1))
    B=frozenset(list(range(q+1-shell))+list(range(q+1,q+1+shell)))
    groups=[sorted(A&B),sorted(A-B),sorted(B-A),sorted(set(coords)-(A|B))]
    queries=[('s',i) for i in coords+[j]]
    queries += [('g',G,h) for r in range(q+1) for G in subsets(coords,r)
                for h in [False,True] if h or r>=2]
    def affine(label,e):
        if e[0]=='s':
            i=e[1]
            return (1.,0.) if i in label else ((-1.,1.) if i==j else (1.,-1.))
        k=len(e[1]-label);h=int(e[2]);return 1-h+k-h, -(k-h)
    def key(e):
        if e[0]=='s': return ('s',4 if e[1]==j else next(i for i,g in enumerate(groups) if e[1] in g))
        return ('g',e[2],*(len(e[1]&set(g)) for g in groups))
    keys=list(dict.fromkeys(key(e) for e in queries)); indices={k:i for i,k in enumerate(keys)}
    orbit=np.array([indices[key(e)] for e in queries]); counts=np.bincount(orbit)
    true=np.array([a+b*mu for a,b in [affine(A,e) for e in queries]])
    alternatives=[]
    for nc in itertools.product(*(range(len(g)+1) for g in groups)):
        if sum(nc)!=q+1:continue
        alt=frozenset(x for g,c in zip(groups,nc) for x in g[:c])
        off,slope=np.array([affine(alt,e) for e in queries]).T
        diff=true-off
        coeff=np.array([np.bincount(orbit,weights=t,minlength=len(keys))/counts
                        for t in ([diff**2/2,-diff*slope,slope**2/2,diff,slope] if calibration else [diff**2/2,-diff*slope,slope**2/2])])
        alternatives.append((alt,len(alt-B),coeff))
    return queries,keys,counts,alternatives

def solve(q,shell,mu,eps,tol=2e-8):
    if not (isinstance(q,int) and q>=2 and 0<=mu<=1 and 0<=eps<q):
        raise ValueError('Require integer q>=2, mu in [0,1], epsilon in [0,q).')
    if not (isinstance(shell,int) and 0<=shell<=q and (2-mu)*shell/2<=eps):
        raise ValueError('Answer shell must be epsilon-good under the true nuisance.')
    queries,keys,counts,alts=problem(q,shell,mu)
    alts=[(a,d,c,min(1.,2-2*eps/d)) for a,d,c in alts if d>eps]
    if not alts:raise ValueError('empty bad set needs extended-real treatment')
    coeff=np.array([x[2] for x in alts]);upper=np.array([x[3] for x in alts])
    def rows(nu):return coeff[:,0,:]+nu[:,None]*coeff[:,1,:]+nu[:,None]**2*coeff[:,2,:]
    cuts=list(rows(np.zeros(len(alts))))+list(rows(upper))
    metadata=[(i,0.) for i in range(len(alts))]+[(i,float(u)) for i,u in enumerate(upper)]
    for iteration in range(100):
        mat=np.array(cuts);dim=len(keys)
        lp=linprog(np.r_[np.zeros(dim),-1.],A_ub=np.c_[-mat,np.ones(len(mat))],
                   b_ub=np.zeros(len(mat)),A_eq=np.array([np.r_[np.ones(dim),0.]]),b_eq=[1.],
                   bounds=[(0,None)]*dim+[(None,None)],method='highs',
                   options={'dual_feasibility_tolerance':1e-9,'primal_feasibility_tolerance':1e-9})
        if not lp.success:raise RuntimeError(lp.message)
        w=lp.x[:-1];polys=coeff@w
        nu=np.zeros(len(alts));positive=polys[:,2]>1e-15
        nu[positive]=np.clip(-polys[positive,1]/(2*polys[positive,2]),0,upper[positive])
        nu[~positive]=np.where(polys[~positive,1]<0,upper[~positive],0)
        oracle=rows(nu); values=oracle@w; lower=float(values.min())
        dual=np.maximum(0,-lp.ineqlin.marginals);dual/=dual.sum()
        dual_vector=dual@mat; ub=float(dual_vector.max());gap=ub-lower
        if gap<=tol:break
        violated=np.where(values<ub-tol/3)[0]
        for i in violated:cuts.append(oracle[i]);metadata.append((int(i),float(nu[i])))
    else:raise RuntimeError(('nonconverged',q,shell,mu,eps,gap))
    active=[]
    for row,p in enumerate(dual):
        if p>1e-10:
            i,u=metadata[row]; a,d,c,up=alts[i]
            active.append({'probability':float(p),'alternative':sorted(a),'distance_from_answer':d,
                           'nu_in_closure':u,'strictly_bad':bool(u<2-2*eps/d),
                           'at_excluded_endpoint':bool(abs(u-(2-2*eps/d))<1e-10)})
    return {'q':q,'mu':mu,'epsilon':eps,'answer_shell':shell,'query_count':len(queries),
      'query_orbits':len(keys),'alternative_orbits':len(alts),'iterations':iteration+1,
      'lower':lower,'upper':ub,'gap':gap,'simplex_residual':float(abs(w.sum()-1)),
      'lp_constraint_violation':float(max(0.,(lp.x[-1]-mat@w).max())),
      'allocation':[{'orbit':k,'orbit_size':int(c),'mass':float(x)} for k,c,x in zip(keys,counts,w) if x>1e-10],
      'dual_alternatives':active,
      'closure_warning':'Excluded endpoints are limits of strictly bad alternatives; not attained witnesses.'}

def main():
    results=[];start=time.time()
    for q in [3,4,5]:
        mu=.5;gamma0=None
        for eps in [0.,.74,.75,.76,1.49,1.5,1.51]:
            shells=range(min(q,math.floor(2*eps/(2-mu)))+1)
            cells=[solve(q,d,mu,eps) for d in shells]
            lo=max(c['lower'] for c in cells);up=max(c['upper'] for c in cells)
            if eps==0:gamma0=lo
            result={'q':q,'mu':mu,'epsilon':eps,'lower':lo,'upper':up,
                    'ratio_to_gamma0':lo/gamma0,'best_shell':max(cells,key=lambda c:c['lower'])['answer_shell'],
                    'shells':cells}
            results.append(result)
            print(q,eps,'Gamma',lo,up,'ratio',lo/gamma0,'shell',result['best_shell'],flush=True)
            Path(__file__).with_suffix('.json').write_text(json.dumps({'status':'partial','results':results},indent=2)+'\n')
    assert all(c['gap']<=2e-8 and c['simplex_residual']<1e-8 for r in results for c in r['shells'])
    Path(__file__).with_suffix('.json').write_text(json.dumps({'status':'complete','seconds':time.time()-start,
      'model':'all legal actual D6 queries; independent unit-variance Gaussian observations; unit cost',
      'method':'semi-infinite LP cutting planes with exact quadratic best responses; floating-point bounds',
      'results':results},indent=2)+'\n')
if __name__=='__main__':main()
