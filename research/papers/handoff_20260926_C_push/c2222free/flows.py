import itertools, numpy as np
from fractions import Fraction as Fr
from scipy.optimize import milp, LinearConstraint, Bounds
from certs import REG, cost, padd, pneg, scal, ev, lin
SEQS=sorted(set(itertools.permutations([0,0,1,1,2,2,3,3])))
def states(s):
    v=[0,0,0,0]; out=[tuple(v)]
    for x in s: v[x]+=1; out.append(tuple(v))
    return out
def pathcosts(name,s):
    R=REG[name]; st=states(s)
    return [cost(R,name,st[k]) for k in range(1,8)]
def coef(p,key): return float(p.get(key,0))
def find(name,W):
    R=REG[name]
    P=[(s,pathcosts(name,s)) for s in SEQS]
    n=len(P)
    A=[];lo=[];hi=[]
    def row(wc,zc=None):
        r=np.zeros(2*n); r[:n]=wc
        if zc is not None: r[n:]=zc
        return r
    A.append(row(np.ones(n))); lo.append(1); hi.append(1)
    for k in range(7):
        for key in [(1,0),(0,1)]:
            A.append(row(np.array([coef(c[k],key) for _,c in P]))); lo.append(-np.inf); hi.append(coef(W,key))
    for j in range(n):
        r=np.zeros(2*n); r[j]=1; r[n+j]=-1; A.append(r); lo.append(-np.inf); hi.append(0)
    c=np.concatenate([np.zeros(n),np.ones(n)])
    res=milp(c,constraints=LinearConstraint(np.array(A),lo,hi),integrality=np.concatenate([np.zeros(n),np.ones(n)]),
             bounds=Bounds(np.zeros(2*n),np.ones(2*n)),options={'time_limit':120})
    print(name,res.status,res.message)
    w=res.x[:n]
    return [(P[j][0],Fr(w[j]).limit_denominator(100)) for j in range(n) if w[j]>1e-7]
if __name__=="__main__":
    TN="AaBb"
    for name,W in [('R1',scal(2,lin(1,0))),('R3',scal(2,lin(1,2)))]:
        # R1: a-b = s ; W=2(a-b)/3 -> times 3: we require sum w c <= W/3
        Wt = scal(Fr(1,3),W) if name=='R1' else scal(Fr(1,7),W)
        sol=find(name,Wt)
        for s,w in sol:
            print("  ", "".join(TN[x] for x in s), w, [ {k:str(v) for k,v in c.items()} for c in pathcosts(name,s)])
