from lp import *
from fractions import Fraction as Fr
TN=['A+','A-','B+','B-']
def decompose(r,eta,band=True):
    global _lp
    v,s,res=value(r,eta) if band else (None,None,None)
    if not band:
        import lp as L
        if L._lp is None: L._lp=L.LP()
        res=L._lp.solve([r,-r,1.0,-1.0],eta,band=False)
    import lp as L
    P=L._lp
    x=res.x
    f={key:x[i] for key,i in P.fi.items() if x[i]>1e-9}
    paths=[]
    while True:
        # start at layer 0
        v=(0,0,0,0); seq=[]; amt=1e9; k=0; edges=[]
        ok=True
        while k<8:
            best=None
            for t in range(4):
                if (k,v,t) in f and f[(k,v,t)]>1e-9:
                    if best is None or f[(k,v,t)]>f[(k,v,best)]: best=t
            if best is None: ok=False;break
            edges.append((k,v,best)); amt=min(amt,f[(k,v,best)])
            seq.append(best); v=tuple(v[j]+(1 if j==best else 0) for j in range(4)); k+=1
        if not ok or amt<1e-9: break
        for e in edges: f[e]-=amt
        paths.append((amt,seq))
    return res,paths
def show(r,eta,band=True):
    res,paths=decompose(r,eta,band)
    D=res.D
    print("r=%g eta=%g W=%.8f npaths=%d"%(r,eta,res.fun*D,len(paths)))
    for amt,seq in paths:
        # prefix sums
        w=[r,-r,1,-1]; s=0; ss=[]
        for t in seq: s+=w[t]; ss.append(round(s,4))
        print("   %.6f %s %s"%(amt,' '.join(TN[t] for t in seq),ss))
if __name__=="__main__":
    import sys
    for r,eta,band in [(1.5,0,True),(2.2,0,True),(2.6,0,True),(4,0,True),(1.5,8,False),(2.1,8,False),(2.3,8,False),(2.7,8,False),(4,8,False)]:
        show(r,eta,band)
