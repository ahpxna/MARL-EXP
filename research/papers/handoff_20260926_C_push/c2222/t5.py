from lp import *
from fit import *
from fractions import Fraction as Fr
def W(r,eta):
    return value(float(r),eta)[0]*4*(float(r)+1)
# L3 intercept: value at eta in the L3 piece, e.g. midpoint between bps
pts=[]
for n in range(202,242,3):
    r=Fr(n,100)
    bps=frontier(float(r))
    # L3 piece is between the last two bps: (bps[-2], bps[-1])
    e0,e1=bps[-2],bps[-1]
    em=(e0+e1)/2
    w=W(r,em)
    slope=-(3-r)**2/(2*(10-3*r))
    I=Fr(w-float(slope)*em).limit_denominator(1000000)
    pts.append((r,I))
print(pts[:4])
for dp,dq in [(1,1),(2,1),(2,2),(3,2),(3,3)]:
    res=ratfit(pts,dp,dq)
    print(dp,dq,res)
