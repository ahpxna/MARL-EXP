#!/usr/bin/env python3
"""Actual Gaussian queries -> unknown-label likelihood -> stopping -> support radius.

Finite candidate hidden sets, continuous nuisance in [0,1], batched predictable
queries. A Gaussian-prior mixture motivates the data-dependent threshold. Its
martingale validity and asymptotic optimality are NOT yet Lean-certified.
All observations, including forced scalar exploration, are charged to time.
The experiment does not claim a growing-q efficient implementation: candidate
labels are exhaustively enumerated.
"""
import argparse,itertools,json
from fractions import Fraction
from functools import lru_cache
from hashlib import sha256
from pathlib import Path
import numpy as np
from experiment_d6_phase_boundary_cost import phase_parameters,oracle,information,binomial_interval
from verify_d6_information_limit_bridge import family_world,all_losses,masks


class Model:
    def __init__(self,q):
        self.q=q; self.k=q+1; self.m=2*q+2; self.j=1<<self.k; self.full=(1<<self.m)-1
        ground=[i for i in range(self.m) if (1<<i)!=self.j]
        self.labels=np.array([sum(1<<i for i in c) for c in itertools.combinations(ground,self.k)],dtype=np.int64)
        self.p=phase_parameters(q)

    @lru_cache(maxsize=None)
    def features(self,query):
        kind,g,h=query
        if kind=='scalar':
            if (1<<g)==self.j: return -np.ones(len(self.labels)),np.ones(len(self.labels))
            return np.ones(len(self.labels)),-((self.labels&(1<<g))==0).astype(float)
        assert not(g&self.j) and g.bit_count()<=self.q
        assert h or g.bit_count()>=2
        counts=np.array([(int(g)&(self.full^int(a)^self.j)).bit_count() for a in self.labels],float)
        b=-(counts-int(h)); a=(0 if h else 1)-b
        return a,b

    def design(self,label,mu):
        A=int(self.labels[label]); B=self.full^A^self.j
        x,y,w=oracle(self.q,mu,self.p)
        choices=[]; weights=[]
        if x:
            choices += [('joint',A^(1<<i),False) for i in range(self.m) if A&(1<<i)]
            weights += [x/self.k]*self.k
        if y:
            choices += [('scalar',i,False) for i in range(self.m) if B&(1<<i)]
            weights += [y/self.q]*self.q
        if w: choices.append(('joint',B,True)); weights.append(w)
        weights=np.array(weights); assert abs(weights.sum()-1)<1e-12
        return choices,weights/weights.sum()

    def check_features(self):
        # Independent exact world evaluations at rational margin, all candidate
        # labels and every query used by every candidate's phase-II/III design.
        used=set(('scalar',i,False) for i in range(self.m))
        for ix in range(len(self.labels)):
            for mu in (self.p['mu_U']-.01,(self.p['mu_U']+self.p['mu_H'])/2):
                used.update(self.design(ix,mu)[0])
        mu=Fraction(13,20)
        tables=np.array([family_world(self.m,mu,int(a)) for a in self.labels],float)/mu.denominator
        worst=0.
        for e in used:
            a,b=self.features(e); kind,g,h=e
            corner=(1<<g) if kind=='scalar' else g|(self.j if h else 0)
            error=np.max(np.abs(a+float(mu)*b-tables[:,corner])); worst=max(worst,float(error))
        assert worst<1e-12
        return dict(actual_query_world_pairs=len(used)*len(self.labels),max_abs_error=worst)

    def geometry(self,true_ix,reported_ix,mu):
        A=int(self.labels[true_ix]); Ahat=int(self.labels[reported_ix]); S=self.full^Ahat
        mu=Fraction(str(mu)); table=family_world(self.m,mu,A)
        losses=all_losses(table,self.m,masks(self.m,self.k))
        radius=losses[S]/(2*mu.denominator)
        optimum=min(losses.values())/(2*mu.denominator)
        regret=radius-optimum
        expected=(2-float(mu))*(S&A).bit_count()/2
        assert abs(regret-expected)<1e-11
        assert (reported_ix==true_ix)==(losses[S]==min(losses.values()))
        return dict(radius=radius,optimum=optimum,regret=regret,
                    support_points=1<<self.m,feasible_selections=len(losses))


def trial(model,mu,delta,rng,batch,max_n):
    K=len(model.labels); truth=int(rng.integers(K)); V=np.zeros(K); Z=np.zeros(K); C=np.zeros(K)
    N=0; forced=0; scalar_counts=np.zeros(model.m,dtype=int); history=[]
    counts={}; stopped=False; estimate=int(rng.integers(K)); mhat=.5
    def observe(e,n,force=False):
        nonlocal N,forced,C,Z,V
        if n==0:return
        a,b=model.features(e); mean=a[truth]+mu*b[truth]
        total=n*mean+np.sqrt(n)*rng.normal()
        # Common sum(Y^2) cancels from every profile likelihood and gap.
        C += n*a*a-2*a*total; Z += b*(total-n*a); V += n*b*b
        N+=n; forced+=n*force; counts[e]=counts.get(e,0)+n
        if e[0]=='scalar': scalar_counts[e[1]]+=n
    while N<max_n:
        # Every scalar is sampled at least sqrt(N)/m times. The total forced
        # count is O(sqrt(N)+m), sufficient for consistency at each fixed q.
        target=max(2,int(np.ceil(np.sqrt(max(1,N))/model.m)))
        for i in range(model.m):
            need=max(0,target-int(scalar_counts[i])); need=min(need,max_n-N)
            observe(('scalar',i,False),need,True)
        raw=np.divide(Z,V,out=np.zeros_like(Z),where=V>0)
        mus=np.clip(raw,0,1)
        scores=-.5*(C-2*mus*Z+mus*mus*V)
        estimate=int(np.argmax(scores)); mhat=float(mus[estimate])
        runner=float(np.max(np.delete(scores,estimate))); gap=float(scores[estimate]-runner)
        # Exact penalty from unconstrained maximum to N(0,1) mixture.
        penalty=.5*np.log1p(V[estimate])+(.5*Z[estimate]**2/(V[estimate]*(1+V[estimate])) if V[estimate]>0 else 0.)
        threshold=float(np.log(K/delta)+penalty)
        if gap>=threshold:
            stopped=True; break
        choices,weights=model.design(estimate,mhat)
        ns=rng.multinomial(min(batch,max_n-N),weights)
        for e,n in zip(choices,ns): observe(e,int(n))
    # Realized allocation information against every other label and continuous nu.
    ia=np.zeros(K); iz=np.zeros(K); iv=np.zeros(K)
    for e,n in counts.items():
        a,b=model.features(e); d=a-(a[truth]+mu*b[truth])
        ia+=n*d*d; iz+=n*d*b; iv+=n*b*b
    nus=np.clip(np.divide(-iz,iv,out=np.zeros_like(iz),where=iv>0),0,1)
    values=.5*(ia+2*nus*iz+nus*nus*iv)/N; values[truth]=np.inf
    empirical_info=float(np.min(values)); gamma=information(model.q,mu,oracle(model.q,mu,model.p))[0]
    return dict(samples=N,stopped=stopped,correct=(truth==estimate),forced_samples=forced,
        forced_fraction=forced/N,mu_hat=mhat,glr_gap=gap,threshold=threshold,
        gamma=gamma,empirical_allocation_information=empirical_info,
        empirical_information_over_gamma=empirical_info/gamma,
        samples_times_gamma_over_log_delta=N*gamma/np.log(1/delta),
        geometry=model.geometry(truth,estimate,mu))


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--q',nargs='+',type=int,default=[3,4]); ap.add_argument('--seeds',type=int,default=40)
    ap.add_argument('--delta',nargs='+',type=float,default=[.1,.01,.001])
    ap.add_argument('--batch',type=int,default=16); ap.add_argument('--max-samples',type=int,default=50000)
    ap.add_argument('--out',type=Path,default=Path('research/d6_phase_boundary_20260908/adaptive_geometry.json'))
    args=ap.parse_args(); rows=[]; checks=[]
    for q in args.q:
        model=Model(q); checks.append(dict(q=q,**model.check_features()))
        width=model.p['mu_H']-model.p['mu_U']
        for side in [-1,1]:
            mu=model.p['mu_U']+side*width/3
            for delta in args.delta:
                trials=[trial(model,mu,delta,np.random.default_rng(np.random.SeedSequence([20260909,q,side+1,i,int(1/delta)])),args.batch,args.max_samples) for i in range(args.seeds)]
                stopped=[r for r in trials if r['stopped']]; failures=sum(r['stopped'] and not r['correct'] for r in trials)
                row=dict(q=q,side=side,mu=mu,delta=delta,seeds=args.seeds,stopped=len(stopped),wrong_stops=failures,
                    wrong_stop_probability_interval95=binomial_interval(failures,args.seeds),
                    median_samples=float(np.median([r['samples'] for r in trials])),
                    median_info_over_gamma=float(np.median([r['empirical_information_over_gamma'] for r in trials])),
                    median_forced_fraction=float(np.median([r['forced_fraction'] for r in trials])),
                    max_geometry_regret=max(r['geometry']['regret'] for r in stopped) if stopped else None,
                    trials=trials)
                rows.append(row);print(q,side,delta,'stopped',len(stopped),'wrong',failures,'median N',row['median_samples'],flush=True)
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(dict(evidence_class='UNKNOWN_A_ADAPTIVE_PROFILE_STOPPING_ACTUAL_GEOMETRY',configuration=vars(args)|{'out':str(args.out)},
        script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),checks=checks,rows=rows,
        limitations=['Small-q exhaustive label enumeration; not computationally scalable in q.',
        'Experiment does not prove uniform delta-correctness or asymptotic Gamma-optimal stopping.',
        'Mixture penalty is derived analytically; adaptive martingale and rate bridges remain to be Lean-proved.',
        'All Gaussian batch sufficient statistics are sampled exactly; no continuous-time approximation.',
        'Censored runs are included and are not counted as successful stops.']),indent=2)+'\n')
    print(args.out,flush=True)
if __name__=='__main__':main()
