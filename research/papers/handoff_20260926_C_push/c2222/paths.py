"""Path-mixture LP with flip symmetry (A+<->A-, B+<->B-)."""
import itertools
import numpy as np
from fractions import Fraction as Fr
from scipy.optimize import linprog
TN=['A+','A-','B+','B-']
FLIP=[1,0,3,2]
SEQS=sorted(set(itertools.permutations([0,0,1,1,2,2,3,3])))
def flip(s): return tuple(FLIP[t] for t in s)
ORB=[]
seen=set()
for s in SEQS:
    if s in seen: continue
    f=flip(s); seen.add(s); seen.add(f)
    ORB.append(min(s,f))
def psums(s,a,b=1):
    w=[a,-a,b,-b]; out=[]; x=0
    for t in s: x+=w[t]; out.append(x)
    return out
def nA(s):
    out=[];c=0
    for t in s:
        c+= (1 if t in (0,1) else 0); out.append(c)
    return out
def base(a,b=1):
    # b_k for k=1..7
    b3=min(b,abs(a-2*b))
    return [None,b,0,b3,0,b3,0,b]
def costs(s,a,b=1):
    bs=base(a,b); ps=psums(s,a,b)
    return [abs(ps[k-1])-bs[k] for k in range(1,8)]
def solve(a,eta,orbs=None,band=True,extra_obj=None):
    orbs=orbs or ORB
    n=len(orbs)
    C=np.array([costs(s,a) for s in orbs])  # n x 7
    NA=np.array([nA(s)[:7] for s in orbs])  # n x 7 (k=1..7)
    # vars: w (n), t
    A=[];bb=[]
    for k in range(7):
        A.append(list(C[:,k])+[-1.0]); bb.append(0.0)
    if band:
        for k in range(7):
            kk=k+1
            A.append(list(NA[:,k])+[0.0]); bb.append(kk/2+eta/2)
            A.append(list(-NA[:,k])+[0.0]); bb.append(-(kk/2-eta/2))
    Aeq=[[1.0]*n+[0.0]]; beq=[1.0]
    c=np.zeros(n+1); c[-1]=1.0
    res=linprog(c,A_ub=np.array(A),b_ub=np.array(bb),A_eq=np.array(Aeq),b_eq=np.array(beq),bounds=[(0,None)]*(n+1),method='highs-ds')
    return res
def show(a,eta,band=True):
    res=solve(a,eta,band=band)
    print("a=%g eta=%g W=%.9f"%(a,eta,res.fun))
    w=res.x[:-1]
    for i in np.argsort(-w):
        if w[i]<1e-10: break
        s=ORB[i]
        print("   %.8f %s  ps=%s nA=%s c=%s"%(w[i],' '.join(TN[t] for t in s),[round(x,3) for x in psums(s,a)],nA(s)[:7],[round(x,3) for x in costs(s,a)]))
if __name__=="__main__":
    for a,eta,band in [(1.5,0,True),(2.2,0,True),(2.6,0,True),(4,0,True),(1.5,8,False),(2.1,8,False),(2.3,8,False),(2.7,8,False),(4,8,False)]:
        show(a,eta,band)
