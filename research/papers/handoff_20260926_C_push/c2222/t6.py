from lp import *
from fractions import Fraction as Fr
import sys
def show(r,eta):
    v,s,res=value(r,eta)
    D=res.D
    print("r=%g eta=%g W=%.9f slopeW=%.9f"%(r,eta,v*D,s*D))
    for tg,mu in zip(res.tags,res.ineqlin.marginals):
        if abs(mu)>1e-9:
            print("   ",tg, "%.9f"%(-mu*(D if tg[0]!='cost' else 1)))
for r,eta in [(2.1,0.3),(2.1,0.7),(2.1,1.5),(2.3,0.2),(2.3,0.5),(2.3,1.5),(2.4,0.05),(2.4,0.25),(2.4,0.43),(2.4,1.0),(2.7,0.1),(2.7,1.0),(1.5,0.3),(1.5,1.0),(4,0.2),(4,1)]:
    show(r,eta)
