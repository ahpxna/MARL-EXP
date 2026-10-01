from fractions import Fraction as Fr
def solve(A, b):
    n=len(A); m=len(A[0])
    M=[row[:]+[bb] for row,bb in zip(A,b)]
    piv=[]; r=0
    for c in range(m):
        p=None
        for i in range(r,n):
            if M[i][c]!=0: p=i;break
        if p is None: continue
        M[r],M[p]=M[p],M[r]
        pv=M[r][c]; M[r]=[x/pv for x in M[r]]
        for i in range(n):
            if i!=r and M[i][c]!=0:
                f=M[i][c]; M[i]=[x-f*y for x,y in zip(M[i],M[r])]
        piv.append(c); r+=1
    # check consistency
    for i in range(r,n):
        if M[i][-1]!=0: return None
    x=[Fr(0)]*m
    for i,c in enumerate(piv): x[c]=M[i][-1]
    return x
def ratfit(pts, dp, dq):
    # F = P/Q, Q monic leading? normalize q0 = 1
    A=[];b=[]
    for r,F in pts:
        row=[r**i for i in range(dp+1)]+[-F*r**j for j in range(1,dq+1)]
        A.append(row); b.append(F)
    x=solve(A,b)
    if x is None: return None
    return x[:dp+1],[Fr(1)]+x[dp+1:]
