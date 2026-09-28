from fractions import Fraction as Fr
class U:
    """univariate polynomial in r, coeff list low->high"""
    def __init__(s,c): 
        c=[Fr(x) for x in c]
        while len(c)>1 and c[-1]==0: c.pop()
        s.c=c
    def __add__(s,o):
        o=o if isinstance(o,U) else U([o]); n=max(len(s.c),len(o.c))
        return U([(s.c[i] if i<len(s.c) else 0)+(o.c[i] if i<len(o.c) else 0) for i in range(n)])
    __radd__=__add__
    def __neg__(s): return U([-x for x in s.c])
    def __sub__(s,o): return s+(-(o if isinstance(o,U) else U([o])))
    def __rsub__(s,o): return (o if isinstance(o,U) else U([o]))-s
    def __mul__(s,o):
        o=o if isinstance(o,U) else U([o]); r=[Fr(0)]*(len(s.c)+len(o.c)-1)
        for i,x in enumerate(s.c):
            for j,y in enumerate(o.c): r[i+j]+=x*y
        return U(r)
    __rmul__=__mul__
    def __call__(s,x): return sum(c*Fr(x)**i for i,c in enumerate(s.c))
    def deg(s): return len(s.c)-1
    def divmod(s,d):
        r=list(s.c); q=[Fr(0)]*max(1,len(r)-len(d.c)+1)
        while len(r)>=len(d.c) and any(r):
            k=len(r)-len(d.c); f=r[-1]/d.c[-1]; q[k]=f
            for i,x in enumerate(d.c): r[i+k]-=f*x
            r.pop()
        return U(q),U(r if r else [0])
    def __repr__(s): return " + ".join(f"{c}*r^{i}" for i,c in enumerate(s.c) if c)
R=U([0,1])
class RF:
    def __init__(s,n,d=None): s.n=n if isinstance(n,U) else U([n]); s.d=d if d is not None else U([1])
    def __add__(s,o):
        o=o if isinstance(o,RF) else RF(o); return RF(s.n*o.d+o.n*s.d, s.d*o.d)
    __radd__=__add__
    def __mul__(s,o):
        o=o if isinstance(o,RF) else RF(o); return RF(s.n*o.n, s.d*o.d)
    __rmul__=__mul__
    def __neg__(s): return RF(-s.n,s.d)
    def __sub__(s,o): return s+(-(o if isinstance(o,RF) else RF(o)))
    def __call__(s,x): return s.n(x)/s.d(x)
