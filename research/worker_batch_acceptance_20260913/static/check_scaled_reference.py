"""Reproducible high-precision checks; the boundary limit remains a conjecture."""
from decimal import Decimal as D,localcontext
from pathlib import Path
import json,hashlib

def coefficients(tau,k):
    n=D(k);c=(1-tau/n)**(2*k-2);a=(1+(n-2)*tau/n)*c;b=(n-2)*tau/n*c
    return a,b,c,min(a,2*b)
def value(tau,rho,k):
    a,b,c,e=coefficients(tau,k);n=D(k);r=2*a-rho;p=rho-2*b
    return max(D(0),n*r-e)*(p*(n-1)+max(D(0),e-r))/(4*c*(n-1))
with localcontext() as ctx:
    ctx.prec=65;rows=[];finite=[];negative=[]
    for tau in map(D,['0.1','0.2','0.4']):
        C=(-2*tau).exp();threshold=2*(1+tau)*C;shift=C*(2*tau*tau*(1-tau)-min(1+tau,2*tau))
        for s in map(D,['-1','-0.25','0','1']):
            target=max(D(0),shift-s)/2;vals=[]
            for k in [100,1000,10000]:
                rho=threshold+s/D(k);a,b,c,e=coefficients(tau,k);v=value(tau,rho,k)
                vals.append(dict(k=k,value=str(v),abs_error=str(abs(v-target)),physical_rho=1<=rho<=2,strong=(D(k)-2)*b>=1))
            rows.append(dict(tau=str(tau),s=str(s),limit_threshold=str(threshold),D=str(shift),target=str(target),values=vals))
    for tau in map(D,['0','0.1','0.2','0.4','1','2']):
        C=(-2*tau).exp();dc=2*tau+4*tau*tau;da=(1+tau)*dc+2*tau;db=tau*dc+2*tau;dt=2*da+1+tau
        nv=2*(1+tau)*(2*db+4)+(2+2*tau)*dt;cv=nv/(2*C)+2*(1+tau)**2*dc/(C*C)
        for k in [20,100,1000,10000]:
            if D(k)<2*tau or 2*dc/D(k)>C:continue
            for rho in map(D,['1','1.5','2']):
                G=max(D(0),2*(1+tau)*C-rho)*(rho-2*tau*C)/(4*C)
                error=abs(value(tau,rho,k)/D(k)-G);bound=cv/D(k)
                assert error<=bound
                finite.append(dict(tau=str(tau),rho=str(rho),k=k,error=str(error),bound=str(bound)))
        raw=(2*(1+tau)*C-2)*(2-2*tau*C)/(4*C)
        if tau>0:
            assert raw<0
            negative.append(dict(tau=str(tau),rho='2',unclamped=str(raw),clamped='0'))
    root=Path(__file__).parent
    (root/'boundary_checks.json').write_text(json.dumps(dict(scope='High-precision numerical checks of proposed boundary formula, not a proof',precision_digits=65,rows=rows),indent=2)+'\n')
    (root/'finite_value_checks.json').write_text(json.dumps(dict(scope='Numerical controls supplement Lean proofs; boundary law not promoted',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),finite_error_checks=finite,refuted_unclamped_controls=negative),indent=2)+'\n')
    print(json.dumps(dict(boundary_cells=len(rows),boundary_values=sum(len(r['values']) for r in rows),finite_checks=len(finite),negative_controls=len(negative))))
