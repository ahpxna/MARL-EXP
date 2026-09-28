from lp import *
from fractions import Fraction as Fr
def pieces(r):
    bps = frontier(r)
    D = 4*(r+1)
    pts = [0.0]+bps+[8.0]
    out=[]
    for i in range(len(pts)-1):
        e0,e1=pts[i],pts[i+1]
        v0=value(r,e0)[0]*D; v1=value(r,e1)[0]*D
        s=(v1-v0)/(e1-e0) if e1>e0 else 0
        icpt=v0-s*e0
        out.append((Fr(e0).limit_denominator(2000), Fr(icpt).limit_denominator(5000), Fr(s).limit_denominator(5000)))
    return out
import sys
for num in range(200,301,5):
    r=num/100
    ps=pieces(r)
    print(r, [(str(e),str(i),str(s)) for e,i,s in ps])
