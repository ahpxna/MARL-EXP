from lp import *
import time
t=time.time()
for r in [1.5,2,2.2,3,5]:
    v0,s0,res=value(r,0.0)
    vf,sf,_=value(r,8.0)
    D=res.D
    bps=frontier(r)
    print(r, v0, vf, v0*D, vf*D, v0/vf, [round(x,6) for x in bps], [round(value(r,e)[0]*D,6) for e in bps])
print(time.time()-t)
