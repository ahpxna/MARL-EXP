from fractions import Fraction as Q
from itertools import product,combinations
import json
# D6: corner reference, binary cube, k=1.
eps=Q(1,10)
F={(0,0):Q(0),(1,0):-1-eps,(0,1):Q(1),(1,1):1-eps}
c=[F[(1,0)],F[(0,1)]]
w=[]
for i in range(2):
 residual=[v-c[i]*a[i] for a,v in F.items()]
 w.append(max(residual)-min(residual))
spreads=[]
for i in range(2):
 ds=[]
 for x in [0,1]:
  a=[0,0];a[1-i]=x;b=a.copy();b[i]=1
  ds.append(F[tuple(b)]-F[tuple(a)])
 spreads.append(max(ds)-min(ds))
delta=max(spreads)
selected=max(range(2),key=lambda i:abs(c[i]))
# Support: same coordinate response functions, three possible feasible supports.
anchor=(0,0,0)
points=[(1,1,-1),(-1,1,1),(1,-1,1)]
losses=[];good=[]
for p in points:
 radii=[Q(abs(sum(p[j] for j in range(3) if j!=i)),2) for i in range(3)]
 losses.append(radii); good.append(set(i for i,v in enumerate(radii) if v==min(radii)))
assert all(a&b for a,b in combinations(good,2))
assert not set.intersection(*good)
# One membership query for points[0] suffices: yes => world 0; no => worlds 1 or 2.
assert good[1]&good[2]
result={'D6_m2':{'epsilon':str(eps),'world':{str(k):str(v) for k,v in F.items()},'corner_scores':list(map(str,map(abs,c))),'selected':selected,'twice_losses':list(map(str,w)),'delta':str(delta),'2D_over_delta':str((w[selected]-min(w))/delta),'analytic_result':'For m=2,k=1 and any F, 2D <= delta; family approaches 1 as epsilon tends to zero. Thus sup=1, not m=2.'},'Support_three_worlds':{'anchor':anchor,'other_points':points,'radii':[[str(v) for v in row] for row in losses],'good_sets':[sorted(s) for s in good],'pairwise_separation_optimum':0,'decision_sufficient_nonadaptive_query_optimum':1,'scope':'Does not refute Separates iff PartialTestCover; refutes treating that predicate as sufficient for a common good decision on arbitrary multiworld fibres.'}}
open('work/independent_scope_checks.json','w').write(json.dumps(result,indent=2))
print(json.dumps(result,indent=2))
