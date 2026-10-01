from ilp import *
from fractions import Fraction as Fr
import numpy as np
def run(name, rs, Wfun, reg, eta):
    print("=====",name)
    for r in rs:
        # minimize t : use orbit LP from paths.solve style but with homogeneous costs
        n=len(ORB)
        C=np.array([costs_h(s,float(r),1.0,reg) for s in ORB])
        A=[];bb=[]
        for k in range(7):
            A.append(list(C[:,k])+[-1.0]); bb.append(0.0)
        if eta is not None:
            NA=np.array([nA(s)[:7] for s in ORB])
            for k in range(7):
                kk=k+1
                A.append(list(NA[:,k])+[0.0]); bb.append(kk/2+eta/2)
                A.append(list(-NA[:,k])+[0.0]); bb.append(-(kk/2-eta/2))
        from scipy.optimize import linprog
        c=np.zeros(n+1); c[-1]=1
        res=linprog(c,A_ub=np.array(A),b_ub=np.array(bb),A_eq=np.array([[1.0]*n+[0.0]]),b_eq=[1.0],bounds=[(0,None)]*(n+1),method='highs-ds')
        print("r=",r,"t=",res.fun, "target", float(Wfun(r)))
        w=res.x[:-1]
        for i in np.argsort(-w):
            if w[i]<1e-10: break
            s=ORB[i]
            print("   %.8f %-26s nA=%s c=%s"%(w[i],' '.join(TN[t] for t in s),nA(s)[:7],[round(float(x),3) for x in costs_h(s,float(r),1.0,reg)]))
run("V0 [2,7/3]",[2.05,2.15,2.3],lambda r:(5-r)/4,'mid',0.0)
run("Vf [7/3,17/7]",[2.35,2.4,2.42],lambda r:2*r*(3-r)/(17-5*r),'mid',None)
run("Vf [17/7,3]",[2.45,2.6,2.9],lambda r:4/7,'mid',None)
