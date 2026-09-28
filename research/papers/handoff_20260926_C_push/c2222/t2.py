from lp import *
from fractions import Fraction as Fr
import numpy as np
rs = [1.01,1.1,1.3,1.5,1.7,1.9,1.99,2.0]+list(np.arange(2.0,3.0001,0.02))+[3.01,3.2,3.5,4,6,10,20]
for r in rs:
    v0,s0,res=value(r,0.0)
    vf,sf,_=value(r,8.0)
    D=res.D
    bps=frontier(r)
    print("%.3f V0D=%.6f VfD=%.6f price=%.6f bps=%s vals=%s slopes0=%.6f" % (r, v0*D, vf*D, v0/vf, [round(x,5) for x in bps], [round(value(r,e)[0]*D,6) for e in bps], s0*D))
