"""Read-only exact finite-sum witness: E1b paired rewards != the Gaussian pair channel.
Run with Python's standard library; no simulation or training.
"""
import itertools, math, json

def main():
    g2=[1-.1*i for i in range(10)];g=[math.sqrt(v) for v in g2]
    P={0,1,2,3};S={0,1,2,4};E={0,8};sigma=.5;rows=[]
    for beta2 in (0.,1.6):
        beta=math.sqrt(beta2);means=[];seconds=[]
        for x in itertools.product((-1,1),repeat=10):
            z=x[0]*x[8]
            u=sum(g[j]*x[j] for j in range(10) if j not in P)+beta*z
            v=sum(g[j]*x[j] for j in range(10) if j not in S)+beta*z
            mu=u*u-v*v
            means.append(mu);seconds.append(mu*mu+4*sigma*sigma*(u-v)**2)
        mean=sum(means)/len(means);variance=sum(seconds)/len(seconds)-mean**2
        rows.append(dict(beta2=beta2,mean=mean,variance=variance))
    assert not E<=P and not E<=S
    assert abs(rows[0]['mean']-rows[1]['mean'])<1e-12
    assert abs(rows[1]['variance']-rows[0]['variance']-8.32)<1e-10
    pools=[]
    for R in (1,2):
        cand=[]
        for r in range(1,R+1):
            for removed in itertools.combinations(P,r):
                for added in itertools.combinations(set(range(10))-P,r):
                    cand.append((P-set(removed))|set(added))
        deficit=[sum(g2[j] for j in P)-sum(g2[j] for j in c) for c in cand]
        targeted=sum(v<1.95 for v in deficit)
        assert targeted==len(cand)
        pools.append(dict(R=R,uniform=len(cand),targeted=targeted,max_deficit=max(deficit),minimum_N_for_uniform_or_targeted=5*len(cand)))
    print(json.dumps(dict(P=sorted(P),S=sorted(S),pair=sorted(E),moments=rows,pools=pools,
        interpretation='Different variance implies different observation laws despite equal means. This rejects the off-pair zero-KL identification with Lean rChan; it does not reject the Lean theorem on rChan.'),indent=2))
if __name__=='__main__':main()
