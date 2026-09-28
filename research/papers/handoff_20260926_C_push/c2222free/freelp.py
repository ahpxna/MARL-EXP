import itertools, numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix
N=(2,2,2,2); M=8
ST=list(itertools.product(range(3),repeat=4))
L=[[u for u in ST if sum(u)==k] for k in range(M+1)]
def base(w,k): return min(abs(sum(x*y for x,y in zip(w,u))) for u in L[k])
def solve(a,b):
    w=(a,-a,b,-b); D=4*a+4*b
    xi={};fi={};idx=0
    for k in range(M+1):
        for v in L[k]: xi[(k,v)]=idx; idx+=1
    for k in range(M):
        for v in L[k]:
            for t in range(4):
                if v[t]<2: fi[(k,v,t)]=idx; idx+=1
    ti=idx; nv=idx+1
    Aeq=[];beq=[];Aub=[];bub=[]
    Aeq.append({xi[(0,L[0][0])]:1}); beq.append(1)
    for k in range(M):
        for v in L[k]:
            r={xi[(k,v)]:-1}
            for t in range(4):
                if (k,v,t) in fi: r[fi[(k,v,t)]]=1
            Aeq.append(r); beq.append(0)
        for v2 in L[k+1]:
            r={xi[(k+1,v2)]:-1}
            for t in range(4):
                if v2[t]>=1:
                    v=tuple(v2[j]-(1 if j==t else 0) for j in range(4))
                    r[fi[(k,v,t)]]=1
            Aeq.append(r); beq.append(0)
    bs=[base(w,k) for k in range(M+1)]
    for k in range(1,M):
        r={ti:-1}
        for v in L[k]:
            c=(abs(sum(x*y for x,y in zip(w,v)))-bs[k])/D
            if c: r[xi[(k,v)]]=c
        Aub.append(r); bub.append(0)
    def mat(rows):
        A=lil_matrix((len(rows),nv))
        for i,r in enumerate(rows):
            for j,x in r.items(): A[i,j]=x
        return A.tocsr()
    c=np.zeros(nv); c[ti]=1
    res=linprog(c,A_ub=mat(Aub),b_ub=bub,A_eq=mat(Aeq),b_eq=beq,bounds=[(0,None)]*nv,method='highs')
    assert res.status==0
    return res.fun*D
def target(a,b):
    r=a/b
    if r<=2: return 2*(a-b)/3
    if r>=3: return 2*(a-b)/7
    return max(2*b*(3*b-a)/(5*b-a), 2*a*(3*b-a)/(17*b-5*a), 4*b/7)
worst=0
for r in list(np.linspace(1.001,4,300))+[5,7,10,100,1000]:
    W=solve(r,1.0); t=target(r,1.0); worst=max(worst,abs(W-t))
print("worst abs gap (b=1):",worst)
