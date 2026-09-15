"""Exact cyclic-window experiments for N3; actual point membership queries.
Lower witnesses explicitly construct a size-s world defeating EACH candidate.
The sequential batch DP chooses all queries before seeing replies within a batch.
"""
from pathlib import Path
from itertools import combinations
from functools import lru_cache
import json,time

def masks(m,r):
    for a in combinations(range(m),r):yield sum(1<<x for x in a)
def windows(m,L):return [sum(1<<((a+i)%m) for i in range(L)) for a in range(m)]
def lower_certificate(m,s,L,Q):
    assert m>s*L and 1<=s and 1<=L and Q.bit_count()<s*L
    full=(1<<m)-1;win=windows(m,L);cut=next(i for i in range(m) if not Q>>i&1)
    order=[(cut+1+i)%m for i in range(m-1)];rank={x:i for i,x in enumerate(order)}
    contained=[w for w in win if w&Q==w]
    contained.sort(key=lambda w:max(rank[i] for i in range(m) if w>>i&1))
    Y=0;packing=[]
    for w in contained:
        if w&Y:continue
        point=max((i for i in range(m) if w>>i&1),key=lambda x:rank[x])
        Y|=1<<point;packing.append(w)
    assert Y&~Q==0 and Y.bit_count()<=s-1
    assert all(not a&b for i,a in enumerate(packing) for b in packing[i+1:])
    assert all(w&Y for w in contained)
    available=Y|(full^Q)
    assert all(w&available for w in win)
    assert available.bit_count()*L>=m and available.bit_count()>=s+1
    counter=[]
    for w in win:
        W=Y
        if not W&w:W |= 1<<next(i for i in range(m) if (w&~Q)>>i&1)
        for i in range(m):
            if W.bit_count()==s:break
            if (available&~W)>>i&1:W|=1<<i
        assert W.bit_count()==s and W&Q==Y and W&w
        counter.append(W)
    return {'Q':Q,'YES':Y,'disjoint_witnesses':packing,'counterworld_per_window':counter}

def upper_check(m,s,L):
    Q=(1<<(s*L))-1;win=windows(m,L);blocks=[((1<<L)-1)<<(i*L) for i in range(s)]
    groups={}
    for W in masks(m,s):groups.setdefault(W&Q,[]).append(W)
    for reply,C in groups.items():
        zeros=[b for b in blocks if not b&reply]
        if zeros:output=zeros[0]
        else:
            assert reply.bit_count()==s and all(w==reply for w in C)
            output=next(w for w in win if not w&reply)
        assert all(not output&w for w in C)
    return len(groups)

def rounds_dp(m,s,L,maxrounds=3):
    worlds=list(masks(m,s));wins=windows(m,L);full=(1<<m)-1
    safe=[sum(1<<i for i,W in enumerate(worlds) if not w&W) for w in wins]
    queries=sorted(range(1,1<<m),key=int.bit_count)
    projections=[[W&Q for W in worlds] for Q in queries]
    @lru_cache(None)
    def solve(C,b):
        if any(C&~safeC==0 for safeC in safe):return (0,0)
        if b==0:return (m+1,0)
        active=[i for i in range(len(worlds)) if C>>i&1]
        best=m+1;bestQ=0
        for Q,proj in zip(queries,projections):
            cost=Q.bit_count()
            if cost>=best:break
            partition={}
            for i in active:partition[proj[i]]=partition.get(proj[i],0)|(1<<i)
            if len(partition)==1:continue
            worst=0
            for child in sorted(partition.values(),key=int.bit_count,reverse=True):
                worst=max(worst,solve(child,b-1)[0])
                if cost+worst>=best:break
            if cost+worst<best:best=cost+worst;bestQ=Q
        return best,bestQ
    C=(1<<len(worlds))-1
    result=[{'batches':b,'depth':solve(C,b)[0],'first_query_mask':solve(C,b)[1]} for b in range(1,maxrounds+1)]
    assert result[0]['depth']==s*L
    return {'m':m,'s':s,'L':L,'results':result,'cached_states':solve.cache_info().currsize}

def main():
    r=[];examples=[];start=time.time()
    for m in range(3,11):
        for s in range(1,4):
            for L in range(1,4):
                if m<=s*L:continue
                count=0
                for k in range(s*L):
                    for Q in masks(m,k):
                        c=lower_certificate(m,s,L,Q);count+=1
                        if (m,s,L,Q)==(9,2,3,31):examples.append(c)
                r.append({'m':m,'s':s,'L':L,'exact_nonadaptive_depth':s*L,
                          'lower_transcripts_checked':count,'upper_replies_checked':upper_check(m,s,L)})
    dp=[]
    for args in [(5,2,2),(6,2,2),(7,2,2),(7,2,3),(8,2,3),(8,3,2)]:
        ans=rounds_dp(*args);dp.append(ans);print(ans,flush=True)
    Path(__file__).with_suffix('.json').write_text(json.dumps({'status':'complete','seconds':time.time()-start,
      'nonadaptive_cells':r,'lower_examples':examples,'rounds_dp':dp},indent=2)+'\n')
    print(len(r),'nonadaptive configurations; all consistent completions passed',flush=True)
if __name__=='__main__':main()
