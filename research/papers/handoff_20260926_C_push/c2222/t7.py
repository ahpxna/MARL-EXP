from lp import *
from fractions import Fraction as Fr
for r,eta in [(2.3,0.5),(2.2,0.6),(2.1,0.7),(2.05,0.65),(2.4,0.42),(2.35,0.5)]:
    v,s,res=value(r,eta)
    D=res.D
    print("r=",r,"eta",eta,"W",Fr(v*D).limit_denominator(100000))
    out=[]
    for tg,mu in zip(res.tags,res.ineqlin.marginals):
        if abs(mu)>1e-10:
            val=-mu*(D if tg[0]!='cost' else 1)
            out.append((tg,str(Fr(val).limit_denominator(20000))))
    print("  ",out)
