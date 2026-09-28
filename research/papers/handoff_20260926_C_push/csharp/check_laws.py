from fractions import Fraction as F
def fam(m):
    p=(m-1)//2; q=m-2-p; return p,q
def check(m,k,eta,vecs,label,maxcost=None):
    # vecs: list of ((a,b,c,d),weight)
    p,q=fam(m); D=m+4; bk=k%2
    tot=sum(w for _,w in vecs); assert tot==1,(label,tot)
    for (a,b,c,d),w in vecs:
        assert w>=0,(label,w); assert a in(0,1) and d in (0,1) and 0<=b<=p and 0<=c<=q,(label,(a,b,c,d),m,k)
        assert a+b+c+d==k,(label,(a,b,c,d),k)
    margs=[sum(w*a for (a,b,c,d),w in vecs), sum(w*d for (a,b,c,d),w in vecs)]
    if p>0: margs.append(sum(w*b for (a,b,c,d),w in vecs)/p)
    if q>0: margs.append(sum(w*c for (a,b,c,d),w in vecs)/q)
    for x in margs: assert abs(x-F(k,m))<=eta/m,(label,m,k,eta,x,F(k,m))
    cost=sum(w*(abs(-3*a-b+c+3*d)-bk) for (a,b,c,d),w in vecs)/D
    return cost
ok=0
for m in range(4,40,2):
    for k in range(2,m-1):
        vecs=[((1,(k-2)//2,(k-1)//2,1),F(k,2*m)),((1,(k-1)//2,(k-2)//2,1),F(k,2*m)),((0,k//2,(k+1)//2,0),(1-F(k,m))/2),((0,(k+1)//2,k//2,0),(1-F(k,m))/2)]
        c=check(m,k,F(0),vecs,'evenmid'); assert c==0; ok+=1
for m in range(5,41,2):
    h=(m-3)//2
    for k in range(3,m-1,2):
        j=(k-1)//2
        if k<=m-4:
            vecs=[((1,j,j-1,1),F(k,m)),((0,j+1,j,0),(1-F(k,m))/2),((0,j,j+1,0),(1-F(k,m))/2)]
        else:
            vecs=[((1,j,j-1,1),(3*F(k,m)-1)/2),((1,j-1,j,1),(1-F(k,m))/2),((0,j+1,j,0),1-F(k,m))]
        c=check(m,k,F(0),vecs,'oddmidodd'); assert c==0; ok+=1
    for k in range(2,m-2,2):
        j=k//2
        L1=[((0,j,j,0),1-F(k,m)),((1,j-1,j-1,1),F(k,m))]
        c=check(m,k,F(1),L1,'oddL1'); assert c==0
        if j==1:
            L0=[((0,1,1,0),F(2*h,m)),((1,0,0,1),F(2,m)),((0,2,0,0),F(1,m))]
        else:
            L0=[((0,j,j,0),1-F(2*j,m)),((1,j-1,j-1,1),F(j,m)),((1,j,j-2,1),F(j,m))]
        c=check(m,k,F(0),L0,'oddL0'); assert c==F(2*j,m*(m+4)),(c,m,k); ok+=1
print('ok',ok)
