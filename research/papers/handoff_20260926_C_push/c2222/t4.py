from lp import *
from fit import *
from fractions import Fraction as Fr
def W(r,eta):
    return value(float(r),eta)[0]*4*(float(r)+1)
pts=[(Fr(n,100), Fr(W(Fr(n,100),8.0)).limit_denominator(100000)) for n in range(218,242,2)]
print(pts)
for dp,dq in [(1,1),(2,1),(1,2),(2,2)]:
    res=ratfit(pts,dp,dq)
    print(dp,dq,res)
