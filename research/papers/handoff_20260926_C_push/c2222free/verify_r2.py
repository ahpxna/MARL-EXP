import itertools
from fractions import Fraction as Fr
from poly import U, R, RF
from certs import REG, cost
TN={'A+':0,'A-':1,'B+':2,'B-':3}
def parse(st):
    toks=[st[i:i+2] for i in range(0,len(st),2)]; return [TN[x] for x in toks]
PATHS=dict(P1="A+A-B+B-B+B-A+A-",Pa="A+A-B+B-B+A-A+B-",Pb="B+A-A+B-B+B-A+A-",Pc="B+A-A+B-B+A-A+B-",
 P3="B-A+B-A-A+B+A-B+",Z="B+B+A-A+A-A+B-B-",Pd="A+A-B+A-A+B-B+B-",Pe="B+B-B+A-A+B-A+A-",
 Pf="B+B-B+A-A+A-A+B-",Pg="B+A-A+A-A+B-B+B-",Pj="A+A-B+B-A+A-B+B-",Pk="B+B-A+A-B+B-A+A-")
def states(s):
    v=[0,0,0,0]; out=[tuple(v)]
    for x in s: v[x]+=1; out.append(tuple(v))
    return out
def costs_r(name):
    # R2 costs as polynomials in r (b=1): s=r-2, t=3-r
    s=parse(PATHS[name]); st=states(s); out=[]
    for k in range(1,8):
        c=cost(REG['R2'],'R2',st[k])
        out.append(U([0])+c.get((1,0),0)*(R-2)+c.get((0,1),0)*(3-R))
    return out
q=R*R-10*R+17
flows={
 'F1':[('P1',RF(Fr(1,2))),('Pc',RF(R-1,2*(5-R))),('P3',RF(3-R,5-R))],
 'F2':[('Pa',RF(11*R*R-46*R+51,2*(R-1)*(17-5*R))),('Pb',RF(11*R*R-46*R+51,2*(R-1)*(17-5*R))),
       ('Pd',RF(-q,2*(R-1)*(17-5*R))),('Pe',RF(-q,2*(R-1)*(17-5*R))),('Pf',RF(-q,2*(R-1)*(17-5*R))),('Pg',RF(-q,2*(R-1)*(17-5*R))),
       ('P3',RF(17-7*R,17-5*R)),('P1',RF(17-7*R,17-5*R))],
 'F47':[('Pa',RF(3-R,2*(R-1))),('Pb',RF(3-R,2*(R-1))),('Pd',RF(3-R,2*(R-1))),('Pe',RF(3-R,2*(R-1))),
        ('Pf',RF(7*R-17,14*(R-1))),('Pg',RF(7*R-17,14*(R-1))),('Pj',RF(7*R-17,7*(R-1))),('Pk',RF(7*R-17,7*(R-1))),('Pc',RF(U([2]),7*(R-1)))]}
W={'F1':RF(2*(3-R),5-R),'F2':RF(2*R*(3-R),17-5*R),'F47':RF(Fr(4,7))}
import math
rA=5-2*math.sqrt(2)
ranges={'F1':(2,rA),'F2':(rA,17/7),'F47':(17/7,3)}
for fn,fl in flows.items():
    tot=RF(0)
    for nm,w in fl: tot=tot+w
    diff=tot-RF(1)
    ok_sum = all(diff.n(Fr(x,7))==0 for x in range(20))
    print(fn,"weights sum to 1:",ok_sum and diff.n.deg()<=20)
    for nm,_ in fl:
        assert sorted(parse(PATHS[nm]))==[0,0,1,1,2,2,3,3]
    C={nm:costs_r(nm) for nm in PATHS}
    lo,hi=ranges[fn]
    for k in range(7):
        s=RF(0)
        for nm,w in fl: s=s+w*RF(C[nm][k])
        slack=W[fn]-s
        # numerator & denominator
        n,d=slack.n,slack.d
        # sample check
        xs=[lo+(hi-lo)*i/50 for i in range(51)]
        mn=min(float(slack(Fr(x).limit_denominator(10**9))) for x in xs)
        qq,rr=n.divmod(q)
        print(f"  k={k+1} min slack on range {mn:.3e}; num={n}; den(2.3)={float(d(Fr(23,10))):.3g}; num mod q = {rr}")
    print("  weights min on range:", min(float(w(Fr(lo+(hi-lo)*i/50).limit_denominator(10**9))) for _,w in fl for i in range(51)))
