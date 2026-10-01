"""Interval LP: constant orbit weights valid at both endpoints (homogeneous (a,b))."""
import numpy as np
from fractions import Fraction as Fr
from scipy.optimize import linprog
from paths import ORB, TN, nA
def psums_h(s,a,b):
    w=[a,-a,b,-b]; out=[]; x=0
    for t in s: x+=w[t]; out.append(x)
    return out
def base_h(a,b,regime):
    # regime: 'lo' (1<=r<=2): b3=2b-a ; 'mid' (2<=r<=3): a-2b ; 'hi' (r>=3): b
    b3={'lo':2*b-a,'mid':a-2*b,'hi':b}[regime]
    return [None,b,0,b3,0,b3,0,b]
def costs_h(s,a,b,regime):
    bs=base_h(a,b,regime); ps=psums_h(s,a,b)
    return [abs(ps[k-1])-bs[k] for k in range(1,8)]
def ilp(ends, Wends, regime, eta=None, method='highs-ds', obj=None):
    """ends: list of (a,b); Wends: target W at each; eta: band (None = free)."""
    n=len(ORB)
    A=[];bb=[]
    for (a,b),W in zip(ends,Wends):
        C=np.array([costs_h(s,a,b,regime) for s in ORB])
        for k in range(7):
            A.append(list(C[:,k])); bb.append(float(W))
    if eta is not None:
        NA=np.array([nA(s)[:7] for s in ORB])
        for k in range(7):
            kk=k+1
            A.append(list(NA[:,k])); bb.append(kk/2+eta/2)
            A.append(list(-NA[:,k])); bb.append(-(kk/2-eta/2))
    Aeq=[[1.0]*n]; beq=[1.0]
    c=np.zeros(n) if obj is None else obj
    res=linprog(c,A_ub=np.array(A),b_ub=np.array(bb),A_eq=np.array(Aeq),b_eq=np.array(beq),bounds=[(0,None)]*n,method=method)
    return res
def show(res, ends, regime):
    if res.status!=0:
        print("INFEASIBLE", res.message); return
    w=res.x
    for i in np.argsort(-w):
        if w[i]<1e-10: break
        s=ORB[i]
        print("   %.8f %s  nA=%s"%(w[i],' '.join(TN[t] for t in s),nA(s)[:7]), [ [round(float(c),3) for c in costs_h(s,a,b,regime)] for a,b in ends])
