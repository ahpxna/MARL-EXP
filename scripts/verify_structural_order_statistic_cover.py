"""Exact constructive check of the proposed unconditional tolerance cover.
The proof uses ordered component spans, not balanced weights. Arithmetic is
integer/rational. This runner falsifies the construction, not a universal proof.
"""
import argparse, hashlib,json,random
from fractions import Fraction
from pathlib import Path


def verify(points,eps):
    m=len(points[0]);size=1<<m
    widths=[max(p[i] for p in points)-min(p[i] for p in points) for i in range(m)]
    scale=sum(widths)
    if scale==0:return None
    sorted_indices=sorted(range(m),key=lambda i:(widths[i],i))
    ordered=[widths[i] for i in sorted_indices]
    metric=[0]
    for k in range(m):metric.append(metric[-1]+ordered[k]+ordered[m-k-1])
    assert metric[-1]==2*scale
    sums=[[0]*size for _ in points];totals=list(map(sum,points));cost=[0]*size
    optimum=[10**100]*(m+1);witness=[None]*(m+1)
    for s in range(size):
        if s:
            bit=s&-s;i=bit.bit_length()-1;prev=s^bit
            for row,p in zip(sums,points):row[s]=row[prev]+p[i]
        val=[total-row[s] for total,row in zip(totals,sums)]
        cost[s]=max(val)-min(val);k=s.bit_count()
        if cost[s]<optimum[k]:optimum[k]=cost[s];witness[k]=s
    anchors=[0]
    for k in range(1,m+1):
        if (metric[k]-metric[anchors[-1]])*eps.denominator>scale*eps.numerator:anchors.append(k)
    assert (len(anchors)-1)*eps.numerator<2*scale*eps.denominator/scale or len(anchors)==1
    maxex=Fraction(0);all_rankings=[]
    for z,a in enumerate(anchors):
        stop=anchors[z+1] if z+1<len(anchors) else m+1
        S=witness[a]
        ranking=[i for i in sorted_indices if S>>i&1]+[i for i in sorted_indices if not S>>i&1]
        all_rankings.append(ranking);s=0
        for k in range(m+1):
            if k:s|=1<<ranking[k-1]
            if a<=k<stop:
                excess=cost[s]-optimum[k]
                assert excess<=metric[k]-metric[a],(points,eps,a,k,excess,metric[k]-metric[a])
                assert excess*eps.denominator<=scale*eps.numerator
                maxex=max(maxex,Fraction(excess,scale))
    return dict(m=m,support_points=len(points),epsilon=str(eps),anchors=anchors,
                menu_size=len(anchors),dimension_free_bound=2//eps+1,
                maximum_normalized_excess=str(maxex),balance_factor=str(Fraction(m*max(widths),scale)))


def main():
 p=argparse.ArgumentParser();p.add_argument('--seed',type=int,default=91031);p.add_argument('--samples',type=int,default=50);p.add_argument('--out',required=True);args=p.parse_args()
 rng=random.Random(args.seed);rows=[]
 for m in [4,6,8,10,12]:
  for family in ['uniform','geometric','one_heavy']:
   for _ in range(args.samples):
    col=[1]*m if family=='uniform' else [2**rng.randrange(12) for _ in range(m)] if family=='geometric' else [1]*m
    if family=='one_heavy':col[rng.randrange(m)]=10**6
    points=[[0]*m]+[[rng.randint(-3,3)*x for x in col] for _ in range(rng.choice([1,3,5]))]
    for eps in [Fraction(1,20),Fraction(1,10),Fraction(1,4),Fraction(1,2)]:
     r=verify(points,eps)
     if r:rows.append(dict(family=family,**r))
  print(json.dumps(dict(m=m,completed=True)),flush=True)
 out=Path(args.out);out.parent.mkdir(parents=True,exist_ok=True)
 out.write_text(json.dumps(dict(evidence_class='EXACT_FINITE_CONSTRUCTIVE_FALSIFICATION_CHECK',universal_proof=False,
   seed=args.seed,script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),rows=rows),indent=2)+'\n')
 print(json.dumps(dict(checked=len(rows),violations=0)))
if __name__=='__main__':main()
