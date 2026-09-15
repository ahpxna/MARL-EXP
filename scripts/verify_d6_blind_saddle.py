#!/usr/bin/env python3
"""80-digit candidate saddle for completely unknown A at the allocation boundary.
Analytic two-query weights and one nuisance dual; every legal query size/switch
and every alternative distance checked. Symmetric moment identities were
independently checked against actual worlds by experiment_d6_blind_allocation.
This is numerical evidence, not a Lean proof of symmetrization or optimality.
"""
from decimal import Decimal as D,getcontext
from hashlib import sha256
from pathlib import Path
import json
getcontext().prec=80


def run(qi):
    q=D(qi);n=2*q+1;scale=(q/(q+1)).sqrt();z=(1-scale)/(q-2+scale)
    rad=((q*q+2*q*q*z+z*z)/(q+1)).sqrt();mu=rad/(1+rad);lam=1-mu
    k=(q+1)/(2*n);t=q*(q*q+1)/(2*n)
    v0=q/n;b0=mu/n;c0=mu*mu/n
    dv=t-v0;db=-lam*k-b0;dc=lam*lam*k-c0
    assert dv>0 and db<0 and dc<0
    # Stable negative root of dv*x^2+2*db*x+2*dc=0.
    shift=2*dc/((db*db-2*dv*dc).sqrt()-db)
    weight=-(v0*shift+b0)/(dv*shift+db)
    V=v0+weight*dv;B=b0+weight*db;C=c0+weight*dc
    value=v0*shift*shift/2+b0*shift+c0
    assert 0<weight<1 and 0<mu+shift<1
    primal=[]
    for di in range(1,qi+1):
        d=D(di);x=max(-mu,min(lam,-d*B/V))
        primal.append((V*x*x/2+d*B*x+d*C,di))
    lo,worst_d=min(primal)
    dual=[(value,'scalar_non_j'),(shift*shift/2,'scalar_j')]
    for ui in range(qi+1):
        u=D(ui);ku=u*(n-u)/(n*(n-1))
        var=u*(n-u)/(n-1)*(q/n)*(1-q/n)
        for h in [0,1]:
            if not h and ui<2:continue
            T=var+(u*q/n-h)**2
            loss=T*shift*shift/2-lam*ku*shift+lam*lam*ku
            dual.append((loss,f'joint_{ui}_{h}'))
    hi,worst_query=max(dual)
    tol=D('1e-60')
    assert abs(lo-value)<tol and abs(hi-value)<tol and worst_d==1
    K=q*(q-2)**2-q+1;dd=(q*(q-1)*lam*lam+K*mu*mu).sqrt()
    delta=(q*lam*lam-mu*mu)/(q*(q-2)*lam+dd)
    gamma=(mu*mu+(q-1)*delta*delta)/(2*q)
    return dict(q=qi,mu=str(mu),joint_off_weight=str(weight),dual_nuisance=str(mu+shift),
        blind_value=str(value),oracle=str(gamma),regret=str(gamma-value),
        q_squared_regret=float(q*q*(gamma-value)),q_3_over_2_joint_weight=float(q*q.sqrt()*weight),
        primal_dual_gap=str(hi-lo),nearest_alternative=worst_d,maximizing_query=worst_query,
        query_orbits_checked=len(dual),alternative_distances_checked=qi)


def main():
    rows=[run(q) for q in [3,4,8,16,32,64,128,256,1024,4096]]
    lp=json.loads(Path('research/d6_phase_boundary_20260908/blind_allocation.json').read_text())
    for row in rows:
        matches=[r for r in lp['rows'] if r['side']==0 and r['q']==row['q']]
        if matches:
            ref=matches[0];value=float(row['blind_value'])
            assert ref['value_lower']-1e-9<=value<=ref['value_upper']+1e-9
    p=Path('research/d6_phase_boundary_20260908/blind_saddle.json')
    p.write_text(json.dumps(dict(evidence_class='HIGH_PRECISION_BLIND_SADDLE_CANDIDATE',
        script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),rows=rows,
        scope=['Completely unknown A, known interaction coordinate j; static common allocation.',
               'Uniform non-j scalars plus uniform q-subset off queries; weights derived analytically.',
               'Candidate dual averages nearest labels at one nuisance; all query orbits checked.',
               '80-digit checks and LP crosschecks, not formal symbolic certification.',
               'Does not bound an adaptive procedure that acquires label information.']),indent=2)+'\n')
    for r in rows:print(r['q'],r['q_squared_regret'],r['q_3_over_2_joint_weight'],r['primal_dual_gap'],flush=True)
if __name__=='__main__':main()
