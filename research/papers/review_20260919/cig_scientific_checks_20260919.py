import json, math, itertools, sys, pathlib, time
import numpy as np
from scipy.optimize import linprog
from fractions import Fraction
root=pathlib.Path('/Users/phanan/cig-amf-main')
out={'scope':'Independent review diagnostics, not a replacement for existing experiment artifacts','structural':[]}

def words(counts,prefix=()):
    if not sum(counts):
        yield prefix; return
    for i,n in enumerate(counts):
        if n:
            nxt=list(counts);nxt[i]-=1
            yield from words(tuple(nxt),prefix+(i,))
for m in range(5,11):
    counts=(1,(m-1)//2,(m-2)//2,1)
    pats=np.array(list(words(counts)),dtype=np.int8); vals=np.array([-3,-1,1,3])[pats]
    defects=np.abs(np.cumsum(vals,axis=1)[:,:-1])-np.arange(1,m)%2
    Ae=np.array([(pats[:,k]==c).astype(float) for c in range(4) for k in range(m)])
    be=np.array([counts[c]/m for c in range(4) for k in range(m)])
    aa=np.column_stack((defects.T,-np.ones(m-1)))
    av=linprog(np.r_[np.zeros(len(pats)),1.],A_ub=aa,b_ub=np.zeros(m-1),A_eq=np.column_stack((Ae,np.zeros(len(Ae)))),b_eq=be,bounds=(0,None),method='highs')
    pv=linprog(defects.max(axis=1).astype(float),A_eq=Ae,b_eq=be,bounds=(0,None),method='highs')
    if not (av.success and pv.success): raise RuntimeError((m,av.message,pv.message))
    row={'m':m,'patterns':len(pats),'uniform_Vavg_numerical':av.fun/(m+4),'uniform_Vpath_numerical':pv.fun/(m+4),'uniform_Vavg_rational_candidate':str(Fraction(float(av.fun)).limit_denominator(100000)/(m+4)),'uniform_Vpath_rational_candidate':str(Fraction(float(pv.fun)).limit_denominator(100000)/(m+4)),'free_Vavg_exact':str(Fraction(2,(m+4)*(m-1))),'free_Vpath_exact':str(Fraction(2,m+4)),'uniform_budget1_lower_exact':str(Fraction(4,m*(m+4))),'max_eq_residual':float(np.max(np.abs(Ae@av.x[:-1]-be)))}
    certs={}
    for label,res in [('avg',av),('path',pv)]:
        pp=[Fraction(float(x)).limit_denominator(1000000) for x in res.x[:len(pats)]]
        zz=[Fraction(float(x)).limit_denominator(1000000) for x in res.eqlin.marginals]
        ub=[Fraction(float(x)).limit_denominator(1000000) for x in res.ineqlin.marginals] if label=='avg' else []
        val=Fraction(float(res.fun)).limit_denominator(1000000)
        support=[i for i,x in enumerate(pp) if x]
        primal=all(x>=0 for x in pp) and sum(pp)==1
        primal=primal and all(sum(pp[i] for i in support if pats[i,k]==c)==Fraction(counts[c],m) for c in range(4) for k in range(m))
        if label=='avg':
            primal=primal and all(sum(pp[i]*int(defects[i,k]) for i in support)<=val for k in range(m-1))
        else: primal=primal and sum(pp[i]*int(defects[i].max()) for i in support)==val
        dual=(all(x<=0 for x in ub) and -sum(ub)<=1) if label=='avg' else True
        for i,pat in enumerate(pats):
            lhs=sum(zz[int(pat[k])*m+k] for k in range(m))
            if label=='avg': lhs+=sum(ub[k]*int(defects[i,k]) for k in range(m-1));rhs=0
            else: rhs=int(defects[i].max())
            dual=dual and lhs<=rhs
        lower=sum(Fraction(counts[c],m)*zz[c*m+k] for c in range(4) for k in range(m))
        assert primal and dual and lower==val,(m,label,primal,dual,lower,val)
        certs[label]={'primal_feasible_exact':primal,'dual_feasible_exact':dual,'value_exact':str(val/(m+4)),'dual_eq':[str(x) for x in zz],'dual_ub':[str(x) for x in ub],'primal_support':[{'word':[int(x) for x in vals[i]],'weight':str(pp[i])} for i in support]}
    row['exact_certificates']=certs
    out['structural'].append(row); print({k:v for k,v in row.items() if k!='exact_certificates'},'CERTIFIED',flush=True)
p=pathlib.Path('/tmp/cig_scientific_checks_20260919.json');p.write_text(json.dumps(out,indent=2));print('WROTE',p)
