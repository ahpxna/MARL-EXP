"""Exact finite audit of short A-free D6 blocks, including arbitrary hidden B.
Integer incidence identities imply the mean for every B; Gaussian variance is
rational arithmetic. No asymptotic or global-adaptive optimality is asserted.
"""
from fractions import Fraction
from itertools import combinations
from pathlib import Path
import hashlib,json
import numpy as np


def block(q,d):
    n=2*q+1;b=2*d+1;M=np.zeros((b,n),int)
    for i in range(n):
        for s in range(d):M[(i*d+s)%b,i]+=1
    assert np.max(M)<=1
    assert np.all(M.sum(0)==d)
    assert np.all((M.sum(1)>=2)&(M.sum(1)<=q))
    # j is absent from all rows; all queried rows have >=2 coordinates.
    return M


def main():
    rows=[];budget=[];weighted_four=[]
    for q in list(range(3,33))+[64,128,256]:
        n=2*q+1
        four=np.zeros((4,n),int)
        for i in range(q+1):
            pair=[(0,1),(1,2),(2,0)][i%3];four[list(pair),i]=1
        four[3,q+1:]=1
        twice_weights=np.array([1,1,1,2])
        assert np.all(twice_weights@four==2)
        assert np.all((four.sum(1)>=2)&(four.sum(1)<=q))
        weighted_four.append(dict(q=q,raw_queries=4,twice_weights=twice_weights.tolist(),
            row_sizes=four.sum(1).tolist(),variance=str(Fraction(7,4*q*q)),oracle_penalty='7',
            scope='Feasible unequal-weight design; global four-query optimality not proved'))
        for d in range(1,q+1):
            M=block(q,d);b=len(M)
            labels_checked=0
            if q<=5:
                for B in combinations(range(n),q):
                    counts=M[:,B].sum(1)
                    A=[i for i in range(n) if i not in B]
                    gates=((M[:,A].sum(1)>0)|(counts>=2)).astype(int)
                    assert np.all(gates==1) and int(counts.sum())==d*q
                    labels_checked+=1
            penalty=Fraction(b*b,d*d)
            rows.append(dict(q=q,d=d,raw_queries=b,row_sizes=M.sum(1).tolist(),
                hidden_coordinate_degree=d,mean_slope=d*q,
                one_block_variance=str(Fraction(b,d*d*q*q)),oracle_variance_penalty=str(penalty),
                exhaustive_labels_checked=labels_checked,all_label_mean_identity='sum counts = d*|B|'))
        for N in sorted(set([3,4,5,6,7,8,9,q,2*q,2*q+1,4*q,8*q])):
            if N<3:continue
            choices=[]
            for d in range(1,min(q,(N-1)//2)+1):
                b=2*d+1;L=N//b;v=Fraction(b,L*d*d*q*q)
                choices.append((v,d,L,b*L))
            v,d,L,used=min(choices)
            budget.append(dict(q=q,budget=N,best_d=d,blocks=L,used_queries=used,
                best_variance=str(v),charged_budget_penalty=str(v*q*q*N),
                optimization_scope='Only the tested equal-degree odd block family'))
    p=Path('research/high_risk_20260910/d6_short_balanced_blocks.json')
    p.write_text(json.dumps(dict(evidence_class='EXACT_INTEGER_INCIDENCE_AND_RATIONAL_VARIANCE',
        scope='Audited finite q range; all-q construction theorem not yet in Lean',
        tested_q=list(range(3,33))+[64,128,256],rows=rows,budget=budget,weighted_four=weighted_four,
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()),indent=2)+'\n')
    print('Passed',len(rows),'designs;',sum(r['exhaustive_labels_checked'] for r in rows),'explicit hidden labels')
    print('At q=64:',[r for r in budget if r['q']==64])
if __name__=='__main__':main()
