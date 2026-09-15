"""Rational primal/dual verification of the derived reference orbit game.
Independent of floating LP optimization. General-k cube-to-orbit bridge remains
paper mathematics, not Lean audited; small cubes are verified separately.
"""
import argparse, hashlib, json, math
from fractions import Fraction as F
from pathlib import Path
from scripts.run_d6_reference_phase_reduction import orbit_loss, slopes


def certificate(k,rho,t):
    a,b=slopes(k,t);c=a-b;e=min(a,2*b);p=rho-2*b;r=2*a-rho
    assert (k-2)*b>=1 and p>0 and c>0
    costs={(d,u):orbit_loss(k,rho,t,d,u) for d in range(k+1)
           for u in range(max(0,d-(k-1)),d+1)}
    best={h:min(costs[d,u] for d in range(k+1)
                for u in range(max(0,d-(k-h)),min(h,d)+1)) for h in range(1,k+1)}
    risk=lambda h,d,u:costs[d,u]-best[h]
    if k*r<=e:
        mix0=F(1);prior_k=F(1);predicted=F(0)
    else:
        U=(k*r-e)/2;u=max(F(0),r-e)/2;v=(p*(k-1)+max(F(0),e-r))/2
        den=U-u+v
        mix0=v/den;prior_k=(v-u)/den
        predicted=(k*r-e)*(p*(k-1)+max(F(0),e-r))/(4*c*(k-1))
    assert 0<=mix0<=1 and 0<=prior_k<=1
    upper=max(mix0*risk(h,0,0)+(1-mix0)*risk(h,k,h) for h in range(1,k+1))
    dual=[]
    for d in range(k+1):
        singleton=F(0)
        if d<k:singleton+=F(k-d,k)*risk(1,d,0)
        if d>0:singleton+=F(d,k)*risk(1,d,1)
        dual.append(prior_k*risk(k,d,d)+(1-prior_k)*singleton)
    lower=min(dual)
    assert lower==upper==predicted,(k,rho,t,lower,upper,predicted)
    return dict(k=k,rho=str(rho),t=str(t),a=str(a),b=str(b),
        value_exact=str(predicted),value_float=float(predicted),
        probability_decision_d0=str(mix0),probability_world_hk=str(prior_k),
        lower_exact=str(lower),upper_exact=str(upper),decisions_checked=k+1,world_orbits_checked=k,
        scope='Exact certificate for orbit loss; general-k cube reduction not yet Lean-audited.')


def main():
    p=argparse.ArgumentParser();p.add_argument('--out',required=True);args=p.parse_args();out=Path(args.out)
    if out.exists():raise SystemExit(f'refusing to overwrite {out}')
    rows=[]
    for k in (8,16,32,64):
        for rho in map(F,('1','3/2','15/8')):
            for tau in map(F,('1/40','1/20','1/10','1/5','2/5')):
                t=tau/k;a,b=slopes(k,t)
                if (k-2)*b<1:continue
                rows.append(certificate(k,rho,t))
        print(json.dumps(dict(k=k,certificates=len(rows))),flush=True)
    result=dict(evidence_class='EXACT_RATIONAL_PRIMAL_DUAL_CERTIFICATES_FOR_DERIVED_ORBIT_GAME',
        rows=rows,script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        orbit_script_sha256=hashlib.sha256(Path('scripts/run_d6_reference_phase_reduction.py').read_bytes()).hexdigest())
    out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__':main()
