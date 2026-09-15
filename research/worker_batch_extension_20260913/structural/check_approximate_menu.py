"""Finite exhaustive stress checks for approximate anchors and cheap extension.
Uses an actual finite support-radius objective; not a replacement for Lean.
"""
from fractions import Fraction as F
from itertools import combinations
from random import Random
from pathlib import Path
import json,hashlib
from approximate_menu import build_menu

def all_sets(m,k):return [frozenset(s) for s in combinations(range(m),k)]
def radius(f,S):
    residual=[sum((row[w] for i,row in enumerate(f) if i not in S),F(0)) for w in range(len(f[0]))]
    return (max(residual)-min(residual))/2

def run(f,eps,eta):
    assert 0<=eta<eps
    c=[(max(row)-min(row))/2 for row in f];assert c==sorted(c)
    B=sum(c,F(0));assert B>0
    m=len(c);phi=[F(0)]
    for k in range(m):phi.append(phi[-1]+c[k]+c[m-1-k])
    width=(eps-eta)*B;buckets={}
    for k,p in enumerate(phi):buckets.setdefault(p//width,[]).append(k)
    objectives=[[(S,radius(f,S)) for S in all_sets(m,k)] for k in range(m+1)]
    opt=[min(v for _,v in cells) for cells in objectives]
    positive=0;called=[]
    def oracle(a,slack):
        nonlocal positive
        assert a not in called;called.append(a)
        eligible=[(S,v) for S,v in objectives[a] if v<=opt[a]+slack]
        S,v=max(eligible,key=lambda sv:(sv[1],tuple(sorted(sv[0]))))
        positive+=v>opt[a]
        return sorted(S)
    menu=build_menu(c,eps,eta,oracle)
    rankings=menu.rankings;calls=menu.anchor_budgets
    assert list(calls)==called
    for k,idx in enumerate(menu.budget_ranking):
        assert radius(f,frozenset(rankings[idx][:k]))<=opt[k]+eps*B
    bound=F(2)/(eps-eta)//1+1
    assert len(set(calls))==len(calls)<=bound and len(rankings)==len(calls)
    for k in range(m+1):assert min(radius(f,frozenset(r[:k])) for r in rankings)<=opt[k]+eps*B
    return dict(m=m,points=len(f[0]),eps=str(eps),eta=str(eta),normalizer=str(B),oracle_calls=len(calls),call_budgets=calls,bound=bound,strictly_suboptimal_anchors=positive)

if __name__=='__main__':
    rng=Random(20260913);rows=[];unsorted_rejected=False
    for m in [4,6,8]:
        for points in [3,5]:
            for trial in range(4):
                f=[[F(rng.randrange(-8,9),4) for _ in range(points)] for _ in range(m)]
                f.sort(key=lambda row:(max(row)-min(row))/2)
                for eps in [F(1,5),F(2,5),F(4,5)]:
                    for eta in [F(0),eps/3]:rows.append(run(f,eps,eta))
    for eps,eta in [(F(1,5),F(1,5)),(F(1,5),F(2,5))]:
        try:run([[F(0),F(1)]],eps,eta)
        except AssertionError:pass
        else:raise AssertionError('Invalid tolerance accepted')
    try:run([[F(0),F(4)],[F(0),F(1)]],F(1,5),F(0))
    except AssertionError:unsorted_rejected=True
    assert unsorted_rejected
    positive=sum(r['strictly_suboptimal_anchors'] for r in rows);assert positive>0
    p=Path(__file__);out=dict(scope='Finite actual-radius checks only; solver oracle calls counted separately',source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),cases=len(rows),strictly_suboptimal_anchors=positive,negative_controls_rejected=3,rows=rows)
    p.with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='rows'}))
