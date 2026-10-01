import itertools, numpy as np
from scipy.optimize import linprog
def family(m):
    p=(m-1)//2; q=m-2-p
    return [-3,-1,1,3],[1,p,q,1]
def baseline(w,n,k):
    best=None
    for u in itertools.product(*[range(x+1) for x in n]):
        if sum(u)==k:
            s=abs(sum(a*b for a,b in zip(w,u)))
            best=s if best is None else min(best,s)
    return best
def layer(w,n,k,eta,ret=False):
    m=sum(n); D=sum(abs(a)*b for a,b in zip(w,n))
    V=[u for u in itertools.product(*[range(x+1) for x in n]) if sum(u)==k]
    bk=baseline(w,n,k)
    c=np.array([(abs(sum(a*b for a,b in zip(w,u)))-bk)/D for u in V])
    rows=[];rhs=[]
    for t in range(4):
        if n[t]==0: continue
        r=np.array([u[t]/n[t] for u in V])
        rows.append(r);rhs.append(k/m+eta/m);rows.append(-r);rhs.append(-(k/m-eta/m))
    res=linprog(c,A_ub=np.array(rows),b_ub=rhs,A_eq=np.ones((1,len(V))),b_eq=[1],bounds=[(0,None)]*len(V),method='highs')
    if ret: return res.fun,[(V[i],res.x[i]) for i in range(len(V)) if res.x[i]>1e-9]
    return res.fun
if __name__=='__main__':
    for m in range(3,12):
        w,n=family(m); D=m+4
        print('m',m,n)
        for eta in [0,0.5,0.9,1.0,1.1,1.25,1.5,1.75,2.0,2.5,3.0]:
            L=[layer(w,n,k,eta)*m*D for k in range(1,m)]
            print('  eta %.2f'%eta,' '.join('%.3f'%x for x in L))
