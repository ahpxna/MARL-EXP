from dp import *
from fractions import Fraction as Fr
def muF1(r): return {3:Fr(1)/(5-r),4:(3-r)/(5-r),5:Fr(1)/(5-r)}
def muF2(r): 
    q=17-5*r
    return {1:(3-r)/q,2:(3-r)/q,3:1/q,4:(3-r)/q,5:1/q,6:(3-r)/q,7:(3-r)/q}
def muU(r): return {k:Fr(1,7) for k in range(1,8)}
def mu345(r): return {3:Fr(1,3),4:Fr(1,3),5:Fr(1,3)}
F1=lambda r:2*(3-r)/(5-r); F2=lambda r:2*r*(3-r)/(17-5*r)
for i in range(0,41):
    r=Fr(1)+Fr(i,10)
    if r==1: r=Fr(101,100)
    out=[str(r)]
    for name,mu,F in [('F1',muF1,F1),('F2',muF2,F2),('U',muU,None),('345',mu345,None)]:
        try:
            m=mu(r)
            if any(x<0 for x in m.values()): out.append(name+':neg'); continue
            _,v=dp(r,Fr(1),m)
            ref=F(r) if F else None
            out.append("%s:%.5f%s"%(name,float(v),'' if ref is None else ('=' if v==ref else ('<%.5f'%float(ref) if v<ref else '>'))))
        except ZeroDivisionError:
            out.append(name+':div0')
    print(' '.join(out))
