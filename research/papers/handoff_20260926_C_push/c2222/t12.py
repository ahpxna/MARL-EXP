from gen import *
from fractions import Fraction as Fr
from sym import P
D=P.lin(4,4)
def report(name,mu,ell,reg,r1,r2,r0,Z=P.c(1)):
    phi,node,bad=gen(mu,ell,reg,r1,r2,r0)
    Phi=phi[(0,0,0,0)]; L=ellsum(ell,r0)
    print(name,"Phi'=",Phi," sum|ell'|=",L," Z=",Z," bad=",len(bad))
    for x in bad[:5]: print("   BAD",x)
    return phi
one=P.c(1)
# L1: mu_1 = 1 (Z=1); ell_{1,A+-} = -(a-b), ell_{1,B+-} = +(a-b)  (scaled by D)
lam=P.lin(1,-1)
ellL1={(1,0):-lam,(1,1):-lam,(1,2):lam,(1,3):lam}
for reg,r1,r2,r0 in [('lo',Fr(1),Fr(2),Fr(3,2)),('mid',Fr(2),Fr(3),Fr(5,2)),('hi',Fr(3),None,Fr(4))]:
    report("L1 "+reg,{1:one},ellL1,reg,r1,r2,r0)
# L2: mu=(0,1/8,1/4,1/4,1/4,1/8,0); band lam(#A2-1)-lam(#A6-3), lam=(a-b)/8: ell_{2,A}=+lam', ell_{2,B}=-lam' ...
l8=P.lin(Fr(1,8),Fr(-1,8))
muL2={2:P.c(Fr(1,8)),3:P.c(Fr(1,4)),4:P.c(Fr(1,4)),5:P.c(Fr(1,4)),6:P.c(Fr(1,8))}
ellL2={(2,0):l8,(2,1):l8,(2,2):-l8,(2,3):-l8,(6,0):-l8,(6,1):-l8,(6,2):l8,(6,3):l8}
report("L2' lo",muL2,ellL2,'lo',Fr(1),Fr(2),Fr(3,2))
report("L2 mid [2,7/3]",muL2,ellL2,'mid',Fr(2),Fr(7,3),Fr(11,5))
report("L2 mid [2,3]",muL2,ellL2,'mid',Fr(2),Fr(3),Fr(11,5))
# free certs
report("345 lo",{3:P.c(Fr(1,3)),4:P.c(Fr(1,3)),5:P.c(Fr(1,3))},{},'lo',Fr(1),Fr(2),Fr(3,2))
U={k:P.c(Fr(1,7)) for k in range(1,8)}
report("U mid",U,{},'mid',Fr(2),Fr(3),Fr(5,2))
report("U hi",U,{},'hi',Fr(3),None,Fr(4))
muF1={3:P.lin(0,1),4:P.lin(-1,3),5:P.lin(0,1)}
report("F1 mid",muF1,{},'mid',Fr(2),Fr(3),Fr(11,5),Z=P.lin(-1,5))
q=P.lin(-1,3)
muF2={1:q,2:q,3:P.lin(0,1),4:q,5:P.lin(0,1),6:q,7:q}
report("F2 mid",muF2,{},'mid',Fr(2),Fr(3),Fr(23,10),Z=P.lin(-5,17))
