#!/usr/bin/env python3
"""Exact Fraction grid for the D6 decision factor with nondegenerate q."""
from itertools import product, combinations
from fractions import Fraction
import json

def acts(m): return list(product((0,1),repeat=m))
def upd(x,i,u): y=list(x);y[i]=u;return tuple(y)
def md(F,i,x,c): return F[x]-F[upd(x,i,c[i])]-F[upd(c,i,x[i])]+F[c]
def osc(v): return max(v)-min(v)
def weight(c,p):
    z=Fraction(1)
    for i,u in enumerate(c): z*=p[i] if u else 1-p[i]
    return z
def exp(G,m,p): return sum(weight(c,p)*G(c) for c in acts(m))
def evaluate(F,m,p):
    aa=acts(m); d=max(abs(md(F,i,x,c)) for i in range(m) for x in aa for c in aa)
    b=exp(lambda c:F[c],m,p)
    Q=[[exp(lambda c,i=i,u=u:F[upd(c,i,u)],m,p) for u in (0,1)] for i in range(m)]
    A={x:sum(Q[i][x[i]] for i in range(m))-(m-1)*b for x in aa}
    sup=max(abs(F[x]-A[x]) for x in aa)
    spans=[osc(q) for q in Q]
    best=None
    for k in range(1,m):
      sets=list(combinations(range(m),k))
      top=max(sets,key=lambda S:(sum(spans[i] for i in S),tuple(-i for i in S)))
      losses={S:Fraction(osc([F[x]-sum(Q[i][x[i]] for i in S) for x in aa]),2) for S in sets}
      reg=losses[top]-min(losses.values())
      ratio=reg/(2*(m-1)*d) if d else Fraction(0)
      if best is None or ratio>best[0]:best=(ratio,k,top,losses,reg)
    return d,sup,best

best=None;tested=0
for m,alphabet in [(2,range(-3,4)),(3,range(-1,2))]:
 aa=acts(m);free=aa[1:]
 for p in product((Fraction(0),Fraction(1,2),Fraction(1)),repeat=m):
  for vals in product(alphabet,repeat=len(free)):
   F={aa[0]:0,**dict(zip(free,vals))};d,sup,b=evaluate(F,m,p)
   if not d:continue
   tested+=1
   if best is None or b[0]>best[0]:best=(b[0],m,p,F,d,sup,b)
r,m,p,F,d,sup,b=best
out={"tested":tested,"best_ratio_to_2_mminus1_delta":str(r),"m":m,
     "q_bernoulli_one_probs":[str(x) for x in p],
     "F":{str(k):v for k,v in F.items()},"delta":d,"sup_residual":str(sup),
     "k":b[1],"selected":list(b[2]),"regret":str(b[4]),
     "losses":{str(k):str(v) for k,v in b[3].items()}}
open("compile_logs/d6_decision_qgrid_results.json","w").write(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
