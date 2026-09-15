"""High-precision N1 primal/dual constructions; no padded incumbent actions.
Perturbation bounds are proved in LeanFunctionalOutsiderPerturbationV1.
"""
from decimal import Decimal as D,localcontext
from itertools import combinations
from pathlib import Path
import json
with localcontext() as ctx:
    ctx.prec=70;out=[]
    for K in [2,4,8,16,32]:
        s=D(2*K).sqrt();H=2+s;p=1/H;w=2/(s*H);target=1/(2*H*H)
        x=1/H;y=1-x
        worst=D(0)
        for a,b in combinations(range(K),2):
            z=[D(0)]*K;z[a]=s/(2*H);z[b]=-z[a]
            assert abs((max(z)-min(z))-(y-x))<D('1e-65')
            E=(p*x*x+p*(y-1)**2+w*sum(v*v for v in z))/2
            worst=max(worst,abs(E-target))
        assert abs(2*p+K*w-1)<D('1e-65') and worst<D('1e-65')
        out.append({'K':K,'Gamma':str(target),'K_Gamma':str(K*target),
          'incumbent_mass':str(2*p),'outsider_cell_mass':str(w),'incumbent_alternative':[str(x),str(y)],
          'outsider_two_endpoint_potential':[str(s/(2*H)),str(-s/(2*H))],
          'maximum_primal_dual_difference':str(worst),
          'uniform_perturbation_ratio_lower_for_sup_error_0.01':str((1-D('.02'))**2)})
Path(__file__).with_suffix('.json').write_text(json.dumps({'cases':out,'precision':70},indent=2)+'\n')
print([(x['K'],x['Gamma'][:14],x['K_Gamma'][:12]) for x in out])
