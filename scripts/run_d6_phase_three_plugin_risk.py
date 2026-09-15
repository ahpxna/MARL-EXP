"""One-epoch phase-III risk from the proved cyclic Gaussian sufficient statistic.
Uses the actual frozen-allocation oracle-gap identity, as a nonnegative square,
to avoid catastrophic cancellation of two nearly equal information values.
Known phase interval and correct-label branch only: no full adaptive claim.
"""
import argparse,hashlib,json,math
from pathlib import Path
import numpy as np


def parameters(q,mu):
    q=np.longdouble(q);mu=np.asarray(mu,dtype=np.longdouble)
    K=q*(q-2)**2-q+1;D=np.sqrt(q*(q-1)*(1-mu)**2+K*mu**2)
    shift=(q*(1-mu)**2-mu**2)/(q*(q-2)*(1-mu)+D)
    w=(q-1)*shift/D
    return shift,w


def main():
    p=argparse.ArgumentParser();p.add_argument('--trials',type=int,default=20000)
    p.add_argument('--seed',type=int,default=91055);p.add_argument('--out',required=True);a=p.parse_args()
    out=Path(a.out)
    if out.exists():raise SystemExit(f'refusing to overwrite {out}')
    rng=np.random.default_rng(a.seed);rows=[]
    for qi in [3,4,8,16,64,256,1024]:
        q=np.longdouble(qi);c=np.sqrt(q/(q+1));z=(1-c)/(q-2+c)
        radius=np.sqrt((q*q+2*q*q*z+z*z)/(q+1));lo=radius/(1+radius);hi=np.sqrt(q)/(1+np.sqrt(q))
        for position in [.01,.5,.99]:
            mu=lo+position*(hi-lo);shift,_=parameters(q,mu)
            for L in [1,4,16,64,256]:
                var=(2*q+1)/(L*q**4)
                raw=mu+np.sqrt(var)*rng.standard_normal(a.trials).astype(np.longdouble)
                est=np.clip(raw,lo,hi);_,w=parameters(q,est)
                coeff=(1-w)*(q-1)/q+w*(q-2)**2
                nuisance=w*(q-2)*(1-mu)/coeff
                regret=coeff*(shift-nuisance)**2/2
                err=(est-mu)**2
                assert np.all(regret>=0) and np.all(np.isfinite(regret))
                bound=64*(2*q+1)/(L*q**6) if qi>=8 else None
                rows.append(dict(q=qi,position=position,mu=float(mu),phase_lo=float(lo),phase_hi=float(hi),
                    blocks=L,raw_queries=L*(2*qi+1),trials=a.trials,raw_variance=float(var),
                    clipped_mse=float(err.mean()),raw_mse=float(((raw-mu)**2).mean()),
                    empirical_regret=float(regret.mean()),regret_standard_error=float(regret.std(ddof=1)/np.sqrt(a.trials)),
                    growing_q_bound=float(bound) if bound is not None else None,
                    mean_over_bound=float(regret.mean()/bound) if bound is not None else None,
                    max_pointwise_scaled_curvature=float(np.max(np.divide(q*q*regret,err,out=np.zeros_like(regret),where=err>0))),
                    projection_fraction=float(np.mean((raw<lo)|(raw>hi)))))
    result=dict(evidence_class='DEVELOPMENT_LAW_SIMULATION_WITH_PROVED_ACTUAL_ORACLE_GAP',
        scope='Actual cyclic sufficient-statistic law; phase-III projection with correct label. Excludes discovery failure, phase selection and tracking.',
        exact_identity_source='LeanD6FrozenOracleGapV1.actual_frozen_oracle_gap',
        estimator_source='LeanD6CyclicPhaseLawV1.estimate_law',
        arithmetic='numpy.longdouble; regret computed as a nonnegative square',
        seed=a.seed,script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),rows=rows)
    out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(cells=len(rows),trials=sum(r['trials'] for r in rows),max_ratio_to_bound=max(r['mean_over_bound'] for r in rows if r['mean_over_bound'] is not None))))
if __name__=='__main__':main()
