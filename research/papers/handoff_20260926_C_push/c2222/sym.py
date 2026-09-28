"""Symbolic homogeneous polynomials in (a,b) with Fraction coefficients: dict {(i,j):c} meaning c a^i b^j."""
from fractions import Fraction as Fr
class P:
    __slots__=('t',)
    def __init__(self,t=None):
        self.t={k:v for k,v in (t or {}).items() if v!=0}
    @staticmethod
    def c(x): return P({(0,0):Fr(x)})
    @staticmethod
    def lin(ca,cb): return P({(1,0):Fr(ca),(0,1):Fr(cb)})
    def __add__(s,o):
        o=o if isinstance(o,P) else P.c(o)
        t=dict(s.t)
        for k,v in o.t.items(): t[k]=t.get(k,0)+v
        return P(t)
    __radd__=__add__
    def __neg__(s): return P({k:-v for k,v in s.t.items()})
    def __sub__(s,o): return s+(-(o if isinstance(o,P) else P.c(o)))
    def __rsub__(s,o): return (o if isinstance(o,P) else P.c(o))-s
    def __mul__(s,o):
        if not isinstance(o,P): return P({k:v*Fr(o) for k,v in s.t.items()})
        t={}
        for k1,v1 in s.t.items():
            for k2,v2 in o.t.items():
                k=(k1[0]+k2[0],k1[1]+k2[1]); t[k]=t.get(k,0)+v1*v2
        return P(t)
    __rmul__=__mul__
    def ev(s,a,b):
        return sum(v*Fr(a)**i*Fr(b)**j for (i,j),v in s.t.items())
    def deg(s): return max((i+j for i,j in s.t),default=0)
    def iszero(s): return not s.t
    def __repr__(s):
        if not s.t: return "0"
        parts=[]
        for (i,j),v in sorted(s.t.items(),reverse=True):
            mon='*'.join(['a']*i+['b']*j)
            parts.append("%s%s"%(v, ('*'+mon) if mon else ''))
        return ' + '.join(parts)
    def lean(s):
        """Lean expression string."""
        if not s.t: return "0"
        parts=[]
        for (i,j),v in sorted(s.t.items(),reverse=True):
            mon=[]
            if i==1: mon.append('a')
            elif i>1: mon.append('a^%d'%i)
            if j==1: mon.append('b')
            elif j>1: mon.append('b^%d'%j)
            num,den=v.numerator,v.denominator
            coef = ("%d"%abs(num)) if den==1 else ("(%d/%d)"%(abs(num),den))
            term = coef if not mon else (('' if (abs(num)==1 and den==1) else coef+' * ')+' * '.join(mon))
            parts.append(('-' if num<0 else '+', term))
        out=''
        for idx,(sg,term) in enumerate(parts):
            if idx==0: out += ('-' if sg=='-' else '')+term
            else: out += ' %s %s'%(sg,term)
        return out
