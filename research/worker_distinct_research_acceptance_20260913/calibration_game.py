"""Optimize the full legal D6 label game after profiling both nu and common bias.
Numerical bounds, with a separate exact-rational universal balanced-design check.
"""
from approximate_game import *
from fractions import Fraction as F

def exact_balance():
    records=[]
    for q in [2,3,4,5]:
        j=2*q+1;coords=range(j);target=F(q+1,3*q+1);labels=list(subsets(coords,q+1))
        for A in labels:
            offset=sum(F(1,3*q+1) for i in coords)+F(q,3*q+1)*(-1)
            slope=sum(F(-1 if i not in A else 0,3*q+1) for i in coords)+F(q,3*q+1)
            assert offset==target and slope==0
        records.append({'q':q,'labels':len(labels),'nonreference_mass':str(F(1,3*q+1)),
          'reference_mass':str(F(q,3*q+1)),'weighted_mean_for_all_mu':str(target),'slope':0})
    # Correct negative control: uniform all-scalar exposure cancels equal-nu swaps,
    # but fails to cancel arbitrary differences of nuisance margins.
    q=3
    assert F(1-q,2*q+2)!=0
    return records

def solve_bias(q,mu=.5,tol=2e-8):
    queries,keys,counts,alts=problem(q,0,mu,True)
    alts=[(a,d,c) for a,d,c in alts if d>0]
    coeff=np.array([a[2] for a in alts]); dim=len(keys)
    def row(i,nu,u):
        c=coeff[i]
        return c[0]+nu*c[1]+nu**2*c[2]-u*(c[3]-nu*c[4])+u*u/2
    def oracle(w):
        p=coeff@w
        C=p[:,0]-p[:,3]**2/2
        B=p[:,1]+p[:,3]*p[:,4]
        H=p[:,2]-p[:,4]**2/2
        assert H.min()>-1e-9
        nu=np.zeros(len(alts));nz=H>1e-14
        nu[nz]=np.clip(-B[nz]/(2*H[nz]),0,1)
        nu[~nz]=(B[~nz]<0).astype(float)
        u=p[:,3]-nu*p[:,4]
        rows=np.array([row(i,n,t) for i,(n,t) in enumerate(zip(nu,u))])
        return rows,nu,u
    cuts=[row(i,nu,0) for nu in [0.,1.] for i in range(len(alts))]
    meta=[(i,nu,0.) for nu in [0.,1.] for i in range(len(alts))]
    for iteration in range(150):
        mat=np.array(cuts)
        lp=linprog(np.r_[np.zeros(dim),-1],A_ub=np.c_[-mat,np.ones(len(mat))],b_ub=np.zeros(len(mat)),
                   A_eq=np.array([np.r_[np.ones(dim),0]]),b_eq=[1],bounds=[(0,None)]*dim+[(None,None)],
                   method='highs',options={'primal_feasibility_tolerance':1e-9,'dual_feasibility_tolerance':1e-9})
        if not lp.success:raise RuntimeError(lp.message)
        w=lp.x[:-1];r,nu,u=oracle(w);values=r@w;lo=float(values.min())
        dual=np.maximum(0,-lp.ineqlin.marginals);dual/=dual.sum();up=float((dual@mat).max())
        if up-lo<tol:break
        for i in np.where(values<up-tol/3)[0]:
            cuts.append(r[i]);meta.append((int(i),float(nu[i]),float(u[i])))
    else:raise RuntimeError(('not converged',q,lo,up))
    balanced=np.zeros(dim)
    for k,key in enumerate(keys):
        if key[0]=='s':balanced[k]=counts[k]*(q if key[1]==4 else 1)/(3*q+1)
    br,bn,bu=oracle(balanced)
    assert abs(balanced.sum()-1)<1e-12 and abs(bu).max()<1e-12
    active=[]
    for p,(i,n,u0) in zip(dual,meta):
        if p>1e-10:active.append({'probability':float(p),'alternative':sorted(alts[i][0]),'nu':n,'offset':u0})
    return {'q':q,'mu':mu,'query_count':len(queries),'iterations':iteration+1,'lower':lo,'upper':up,'gap':up-lo,
      'balanced_scalar_value':float((br@balanced).min()),'balanced_all_offsets_max_abs':float(abs(bu).max()),
      'allocation':[{'orbit':k,'mass':float(x),'orbit_size':int(c)} for k,x,c in zip(keys,w,counts) if x>1e-10],
      'dual_alternatives':active,'simplex_residual':float(abs(w.sum()-1)),
      'lp_constraint_violation':float(max(0.,(lp.x[-1]-mat@w).max()))}

def main():
    checks=exact_balance();out=[]
    baseline=json.loads(Path(__file__).with_name('approximate_game.json').read_text())['results']
    for q in [3,4,5]:
        r=solve_bias(q);known=next(c['lower'] for c in baseline if c['q']==q and c['epsilon']==0.)
        r['known_offset_value']=known;r['profiled_to_known_ratio']=r['lower']/known;out.append(r)
        print(q,'unknown',r['lower'],r['upper'],'known',known,'ratio',r['profiled_to_known_ratio'],flush=True)
    Path(__file__).with_suffix('.json').write_text(json.dumps({'status':'complete',
      'exact_A_independent_balance':checks,'uniform_scalar_negative_control':True,'results':out},indent=2)+'\n')
if __name__=='__main__':main()
