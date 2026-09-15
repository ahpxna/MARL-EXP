"""Finite exact witnesses for fixed-nuisance swap averages and binary Top-C flips."""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import argparse,json,random
_ap=argparse.ArgumentParser(description=__doc__)
_ap.add_argument('--out',default='research/high_risk_20260910/query_width_functional_flip_exact.json')
_ap.add_argument('--seed',type=int,default=20260911)
_a=_ap.parse_args();_OUT=Path(_a.out)
if _OUT.exists(): raise SystemExit(f'refusing to overwrite existing ledger artifact: {_OUT}')
_OUT.parent.mkdir(parents=True,exist_ok=True)
rng=random.Random(_a.seed)
queries=[]
for k in range(3,9):
    A=set(range(k));B=set(range(k,2*k-1));m=2*k-1
    for r in range(1,k):
        vals=[]
        for G in combinations(range(m),r):
            G=set(G)
            # Actual equal-margin mean difference for threshold off/on queries.
            v=sum(F((int(a in G)-int(b in G))**2,2) for a in A for b in B)/F(k*(k-1))
            vals.append(v)
        assert max(vals)==F(r,2*(k-1))
        queries.append(dict(k=k,r=r,unit_variance_mu0_max=str(max(vals)),candidate=str(F(r,2*(k-1))),queries_checked=len(vals),legal_off_queries=(r>=2),legal_on_queries=True))
# Binary response panel: C_i=|Q_i1-Q_i0|. Query precisions p_i0,p_i1>0.
# The energy is sum p_iu*dQ_iu^2/2. Every rank flip crosses one pair boundary.
# For that pair C_i>=C_j the exact minimum is gap^2/[2(v_i+v_j)].
# Explicit witness moves slopes towards a common nonnegative magnitude.
flips=[]
for trial in range(250):
    n=rng.randrange(3,9);k=rng.randrange(1,n)
    Q=[[F(rng.randrange(-24,25),8) for u in (0,1)] for i in range(n)]
    p=[[F(rng.randrange(1,25),4) for u in (0,1)] for i in range(n)]
    C=[abs(b-a) for a,b in Q];T=set(sorted(range(n),key=lambda i:(-C[i],i))[:k])
    v=[1/a+1/b for a,b in p];pairs=[]
    for i in T:
        for j in set(range(n))-T:
            gap=C[i]-C[j];D=v[i]+v[j];cost=gap**2/(2*D)
            d=[[F(0),F(0)] for _ in range(n)]
            for h,delta in ((i,-gap*v[i]/D),(j,gap*v[j]/D)):
                sign=1 if Q[h][1]>=Q[h][0] else -1
                ds=sign*delta
                d[h]=[-ds/(p[h][0]*v[h]),ds/(p[h][1]*v[h])]
            QQ=[[Q[h][u]+d[h][u] for u in (0,1)] for h in range(n)]
            assert abs(QQ[i][1]-QQ[i][0])==abs(QQ[j][1]-QQ[j][0])
            energy=sum(p[h][u]*d[h][u]**2/2 for h in range(n) for u in (0,1))
            assert energy==cost
            pairs.append((cost,i,j,QQ))
    cost,i,j,QQ=min(pairs,key=lambda t:t[:3])
    flips.append(dict(n=n,k=k,top=sorted(T),pair=[i,j],cost=str(cost),Q=[[str(x) for x in row] for row in Q],precision=[[str(x) for x in row] for row in p],boundary_Q=[[str(x) for x in row] for row in QQ]))
out=dict(query_scope='uniform adjacent-swap average, same nuisance mu=0, sigma^2=1; NOT each-pair KL or optimized nuisance',query_cells=queries,functional_scope='binary response panels with unrestricted response perturbations and independent positive Gaussian precisions; minimum to tie, infimum to strict reversal; shared-F feasibility not imposed',functional_panels=flips)
_OUT.write_text(json.dumps(out,indent=2)+'\n')
print('query cells',len(queries),'enumerated queries',sum(x['queries_checked'] for x in queries),'functional panels',len(flips),'all exact witness checks passed')
