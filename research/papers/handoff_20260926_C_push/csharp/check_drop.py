from fractions import Fraction as F
def fam(m):
    p=(m-1)//2; q=m-2-p; return p,q
def drop_check(m,eta,u,target):
    # u: dict weight->pi value
    p,q=fam(m); D=m+4
    cnt={-3:1,-1:p,1:q,3:1}
    assert sum(cnt[w]*u[w] for w in cnt)==1
    for w in cnt:
        if cnt[w]==0: continue
        assert u[w]>=0 and abs(u[w]-F(1,m))<=eta/m,(m,eta,w,u[w])
    tot=0 if m%2==0 else -1
    c1=sum(cnt[w]*u[w]*(abs(w)-1) for w in cnt)
    cm=sum(cnt[w]*u[w]*(abs(tot-w)-((m-1)%2)) for w in cnt)
    assert c1<=target and cm==target,(m,eta,c1,cm,target)
etas=[F(i,40) for i in range(0,121)]
for m in range(4,30,2):
    for eta in etas:
        x=max(1-eta,0)/m; y=(1-2*x)/(m-2)
        drop_check(m,eta,{-3:x,3:x,-1:y,1:y},4*max(1-eta,0)/m)
for m in range(3,31,2):
    h=(m-3)//2
    for eta in etas:
        tgt=max(m+3-(m+1)*eta, m+1-(m-1)*eta,0)/m
        if eta<=1:
            u={-1:(1+eta)/m,3:(1-eta)/m,-3:(1-h*eta/(h+1))/m,1:(1-h*eta/(h+1))/m}
        elif eta<=F(m+1,m-1):
            u={-1:(1+eta)/m,3:F(0),-3:(h+2-(h+1)*eta)/(m*(h+1)),1:(h+2-(h+1)*eta)/(m*(h+1))}
        else:
            u={-1:F(1,h+1),3:F(0),-3:F(0),1:F(0)}
        drop_check(m,eta,u,tgt)
print('drop ok')
