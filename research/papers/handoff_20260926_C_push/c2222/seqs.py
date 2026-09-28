"""Sequences, states, exact raw costs per region."""
from fractions import Fraction as Fr
from sym import P
TN={'A+':0,'A-':1,'B+':2,'B-':3}
FLIP=[1,0,3,2]
def parse(s): return tuple(TN[t] for t in s.split())
def flip(q): return tuple(FLIP[t] for t in q)
def name(q): return 'q'+''.join(str(t) for t in q)
def st(q,k):
    c=[0,0,0,0]
    for t in q[:k]: c[t]+=1
    return tuple(c)
def sgHi(v):
    v0,v1,v2,v3=v
    if v1<v0: return 1
    if v0<v1: return -1
    if v3<v2: return 1
    if v2<v3: return -1
    return 0
def sgLo(v):
    v0,v1,v2,v3=v
    if v0==v1+1 and v3==v2+2: return -1
    if v1==v0+1 and v2==v3+2: return 1
    return sgHi(v)
def sN(v): return P.lin(v[0]-v[1], v[2]-v[3])
def beta(region,k):
    b3={'lo':P.lin(-1,2),'mid':P.lin(1,-2),'hi':P.lin(0,1)}[region]
    return {0:P(),1:P.lin(0,1),2:P(),3:b3,4:P(),5:b3,6:P(),7:P.lin(0,1),8:P()}[k]
def rc(q,k,region):
    v=st(q,k)
    sg = sgLo(v) if region=='lo' else sgHi(v)
    return sN(v)*sg - beta(region,k)
# region sample check: sign function consistent with true abs at interior points
def check_sign(region):
    import itertools
    pts={'lo':[Fr(11,10),Fr(3,2),Fr(19,10),Fr(2)],'mid':[Fr(2),Fr(5,2),Fr(3)],'hi':[Fr(3),Fr(4),Fr(10)]}[region]
    for v in itertools.product(range(3),repeat=4):
        for r in pts:
            s=sN(v).ev(r,1); sg=(sgLo(v) if region=='lo' else sgHi(v))
            assert abs(s)==sg*s,(v,r)
for rg in ['lo','mid','hi']: check_sign(rg)
