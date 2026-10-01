from ilp import *
from fractions import Fraction as Fr
def W0(r):
    r=Fr(r)
    if r<=2: return Fr(3,4)*(r-1)
    if r<=Fr(7,3): return (5-r)/4
    return (r-1)/2
def Wf(r):
    r=Fr(r)
    if r<=2: return Fr(2,3)*(r-1)
    if r>=3: return Fr(2,7)*(r-1)
    if r>=Fr(17,7): return Fr(4,7)
    import math
    rA=5-2*math.sqrt(2)
    if r<=rA: return 2*(3-r)/(5-r)
    return 2*r*(3-r)/(17-5*r)
def feas(r1,r2,Wfun,reg,eta):
    res=ilp([(float(r1),1.0),(float(r2),1.0)],[Wfun(r1),Wfun(r2)],reg,eta)
    return res.status==0
for (lo,hi,Wfun,reg,eta,name) in [(Fr(2),Fr(7,3),W0,'mid',0.0,'V0mid1'),(Fr(17,7),Fr(3),Wf,'mid',None,'Vf47')]:
    # greedy: from lo, extend as far as possible
    a=lo; pieces=[]
    while a<hi:
        # binary search on b
        l,h=a,hi
        if feas(a,hi,Wfun,reg,eta):
            pieces.append((a,hi)); break
        for _ in range(30):
            m=(l+h)/2
            if feas(a,m,Wfun,reg,eta): l=m
            else: h=m
        pieces.append((a,float(l))); a=Fr(l).limit_denominator(10**6)
        if len(pieces)>10: break
    print(name,[(float(x),float(y)) for x,y in pieces])
