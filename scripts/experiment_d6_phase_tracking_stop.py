#!/usr/bin/env python3
"""Unknown-label, unknown-margin D6 tracking with continuous-nuisance stopping.

Uses actual world tables and the existing proper-mixture confidence set.
Learner selection uses estimated A and estimated mu only. All scalar forced
exploration is charged. This is sequential algorithm evidence, not a Lean
proof of the martingale, expected stopping rate, or a growing-q theorem.
"""
import argparse,json,time
from pathlib import Path
from hashlib import sha256
import numpy as np
from scipy.special import logsumexp
from experiment_d6_unknown_margin_anytime import model,integrated_log_likelihood
from experiment_d6_phase_boundary_cost import phase_parameters,oracle,information,binomial_interval


def trial(data,mode,mu,delta,seed,max_steps):
    k,q,j,U,labels,queries,index,a,b=data
    m=2*k; parameters=phase_parameters(q)
    truth_rng=np.random.default_rng(np.random.SeedSequence([seed,1]))
    policy_rng=np.random.default_rng(np.random.SeedSequence([seed,2]))
    noise_rng=np.random.default_rng(np.random.SeedSequence([seed,3]))
    true_idx=int(truth_rng.integers(len(labels))); true_A=labels[true_idx]
    truth=a[true_idx]+(1-mu)*b[true_idx]
    energy=np.zeros(len(labels)); score=energy.copy(); sse=energy.copy()
    lam=np.full(len(labels),.5); selected=0; forced=0; count_types={}
    label_errors=0; switches=0; last_phase=None; oracle_mass=np.zeros(3)
    gamma=information(q,mu,oracle(q,mu,parameters))[0]
    answer=None
    for t in range(1,max_steps+1):
        # Every coordinate is sampled infinitely often at fixed q; this quota
        # depends on t, not on true A, true mu, or confidence delta.
        if forced<int(np.sqrt(t)):
            e=forced%m; forced+=1
        else:
            A=labels[selected]; B=U^A
            estimate=float(1-lam[selected])
            if mode=='plugin_four_phase':
                weights=oracle(q,estimate,parameters)
            elif mode=='frozen_phase_II':
                weights=(1-parameters['left_Bon_weight'],0.,parameters['left_Bon_weight'])
            else: raise ValueError(mode)
            oracle_mass+=weights
            phase=int(np.argmax(weights)); switches+=int(last_phase is not None and phase!=last_phase)
            last_phase=phase
            orbit=int(policy_rng.choice(3,p=weights))
            if orbit==0:
                positions=[i for i in range(m) if A&(1<<i)]
                omitted=int(policy_rng.choice(positions))
                e=index[('J0',A^(1<<omitted))]
            elif orbit==1:
                positions=[i for i in range(m) if B&(1<<i)]
                e=index[('Q',int(policy_rng.choice(positions))) ]
            else:
                e=index[('J',B)]
        count_types[queries[e][0]]=count_types.get(queries[e][0],0)+1
        y=truth[e]+noise_rng.normal()
        residual=y-a[:,e]
        sse+=residual*residual; score+=b[:,e]*residual; energy+=b[:,e]**2
        lam=np.clip(np.divide(score,energy,out=np.zeros_like(score),where=energy>0),0,1)
        mle=-sse/2+lam*score-lam*lam*energy/2
        selected=int(np.argmax(mle)); label_errors+=int(selected!=true_idx)
        logZ=float(logsumexp(integrated_log_likelihood(sse,score,energy))-np.log(len(labels)))
        survivors=mle>=logZ+np.log(delta)
        if int(survivors.sum())==1:
            answer=int(np.flatnonzero(survivors)[0]); break
    stopped=answer is not None
    answer_A=labels[answer] if stopped else None
    selection=(((1<<m)-1)^answer_A) if stopped else None
    missed=(true_A&selection).bit_count() if stopped else None
    return dict(mode=mode,seed=seed,q=q,mu=mu,delta=delta,steps=t,stopped=stopped,
        correct=(answer==true_idx) if stopped else None,true_A=true_A,answer_A=answer_A,
        geometric_selection=selection,geometric_excess_radius=(2-mu)*missed/2 if stopped else None,
        estimated_mu=float(1-lam[answer if stopped else selected]),forced_samples=forced,
        query_counts=count_types,wrong_label_estimate_steps=label_errors,dominant_orbit_switches=switches,
        cumulative_proposed_orbit_mass=oracle_mass.tolist(),gamma=gamma,
        normalized_samples=t*gamma/np.log(1/delta),
        censored_at=max_steps if not stopped else None)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--q',type=int,nargs='+',default=[3,4])
    p.add_argument('--deltas',type=float,nargs='+',default=[.01,.0001,1e-8])
    p.add_argument('--seeds',type=int,default=30)
    p.add_argument('--seed-start',type=int,default=20260910)
    p.add_argument('--max-steps',type=int,default=12000)
    p.add_argument('--out',type=Path,default=Path('research/d6_phase_boundary_20260908/phase_tracking_stop.json'))
    args=p.parse_args(); assert all(0<d<1 for d in args.deltas)
    rows=[]; summary=[]; start=time.monotonic()
    for q in args.q:
        data=model(2*(q+1)); par=phase_parameters(q); width=par['mu_H']-par['mu_U']
        cases={'left':par['mu_U']-.25*width,'phaseIII':par['mu_U']+.5*width,
               'phaseIV':min(.98,par['mu_H']+.08)}
        for case,mu in cases.items():
            for delta in args.deltas:
                for mode in ('plugin_four_phase','frozen_phase_II'):
                    batch=[trial(data,mode,mu,delta,seed,args.max_steps)
                           for seed in range(args.seed_start,args.seed_start+args.seeds)]
                    for row in batch: row['case']=case
                    rows.extend(batch); errors=sum(r['correct'] is False for r in batch)
                    s=dict(q=q,case=case,mu=mu,delta=delta,mode=mode,seeds=args.seeds,
                        stopped=sum(r['stopped'] for r in batch),errors=errors,
                        error_interval_95=binomial_interval(errors,args.seeds),
                        mean_steps_including_censored=float(np.mean([r['steps'] for r in batch])),
                        mean_normalized_samples=float(np.mean([r['normalized_samples'] for r in batch])),
                        mean_forced_samples=float(np.mean([r['forced_samples'] for r in batch])),
                        max_geometric_excess_radius=max((r['geometric_excess_radius'] or 0) for r in batch))
                    summary.append(s); print(json.dumps(s),flush=True)
    deps=['experiment_d6_unknown_margin_anytime.py','experiment_d6_phase_boundary_cost.py',
          'verify_d6_information_limit_bridge.py']
    result=dict(evidence_class='ACTUAL_QUERY_UNKNOWN_A_MU_ADAPTIVE_GEOMETRIC_STOPPING',
        script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        dependencies_sha256={d:sha256(Path(__file__).with_name(d).read_bytes()).hexdigest() for d in deps},
        configuration=vars(args)|{'out':str(args.out)},elapsed_seconds=time.monotonic()-start,
        summary=summary,trials=rows,scope=[
            'Each actual noisy query is generated individually, with adaptive query selection.',
            'Neither A nor mu is provided to the learner policy or stopping rule.',
            'Nuisance maximization and integration use the continuous interval [0,1].',
            'Proper mixture confidence-set validity is an analytic argument, not yet proved in Lean.',
            'Geometry excess uses the previously formalized exact radius identity.',
            'Phase I and IV allocation formulas are numerical candidates unless separately audited.',
            'Monte Carlo does not establish expected-time optimality or asymptotic matching.',
            'Censored runs remain censored and are never counted as correct stops.'])
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,indent=2)+'\n'); print(args.out,flush=True)

if __name__=='__main__':main()
