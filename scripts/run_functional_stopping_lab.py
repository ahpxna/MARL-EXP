"""Sequential fixed-confidence screening for C-extrema/Top-K and D-sign targets."""
from __future__ import annotations
import sys,argparse,json,math
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))
import numpy as np
from scipy.stats import norm
from research_chains.provenance import atomic_json

PROTOCOL_VERSION='functional_stopping_geometry_lab_v1'

def _sample_means(rng,truth,sigmas,counts):
    return truth+rng.normal(scale=sigmas/np.sqrt(np.maximum(counts,1)))

def run(instances=200,seed=0,K=6,R=5,delta=.05,max_n=4096,batch=16,noise_scale=.35):
    rng=np.random.default_rng(seed); weights=np.linspace(-1,1,K); weights-=weights.mean(); weights/=np.sum(np.abs(weights)); sigmas=float(noise_scale)*np.linspace(.7,1.3,K)
    # Finite-look Bonferroni envelope: valid across every relation/action cell and
    # every sequential inspection under the known-Gaussian synthetic model.
    initial_n=R*K; n_looks=1+int(np.ceil(max(0,int(max_n)-initial_n)/max(1,int(batch))))
    z=float(norm.ppf(1-float(delta)/(2*K*R*n_looks)))
    rows=[]
    for idx in range(int(instances)):
        # Relation-specific surfaces with *actual* geometry control.  A previous
        # version encoded the global gap as a relation-wise additive offset, which
        # cancels from C=max(Q)-min(Q) and therefore did not control Top-K geometry.
        top_capacity=float(rng.uniform(1.4,2.2))
        topk_regime=('small','mid','large')[idx%3]
        local_regime=('small','mid','large')[(idx//3)%3]
        topk_frac={'small':(.01,.04),'mid':(.12,.22),'large':(.35,.50)}[topk_regime]
        global_gap=float(rng.uniform(*topk_frac)*top_capacity)
        capacities=np.sort(rng.uniform(0.35,max(0.36,top_capacity-global_gap-.05),size=R))[::-1]
        capacities[0]=top_capacity
        if R>1: capacities[1]=top_capacity-global_gap
        truths=[]
        for r in range(R):
            cap=float(capacities[r]); center=float(rng.normal(scale=.35))
            # Keep the designed local extremum margin feasible for every
            # relation capacity.  Interior actions stay strictly inside the two
            # extremal competitors; the global Top-K geometry is controlled only
            # by `cap`, not by a relation-wise additive shift.
            local_frac={'small':(.01,.03),'mid':(.08,.14),'large':(.20,.25)}[local_regime]
            local_gap=float(rng.uniform(*local_frac)*cap)
            low=center-cap/2; high=center+cap/2
            inner_low=low+local_gap; inner_high=high-local_gap
            if inner_low > inner_high + 1e-15:
                raise AssertionError('infeasible synthetic local-gap geometry')
            q=rng.uniform(inner_low,inner_high,size=K)
            if K>=4:
                q[0]=low; q[1]=low+local_gap
                q[-1]=high; q[-2]=high-local_gap
            else:
                q[0]=center-cap/2; q[-1]=center+cap/2
            truths.append(q)
        truths=np.asarray(truths); true_C=np.ptp(truths,axis=1); true_D=truths@weights; true_top=int(np.argmax(true_C))
        for mode in ('uniform','D_targeted','C_extremal','C_topk_targeted'):
            counts=np.ones((R,K),dtype=int)
            # Actual cumulative Gaussian observations; adaptive decisions reuse the
            # same data rather than resampling an independent sample mean each look.
            sums=truths+rng.normal(scale=np.tile(sigmas,(R,1)),size=(R,K))
            stopped_C_ext_rel=[None]*R; stopped_top=None; stopped_D_rel=[None]*R; looks_used=0
            false_C_ext_rel=[None]*R; false_top=None; false_D_rel=[None]*R
            while True:
                total=int(np.sum(counts)); looks_used+=1
                means=sums/np.maximum(counts,1); rad=z*sigmas[None,:]/np.sqrt(np.maximum(counts,1))
                local_ok=[]; C_lo=[]; C_hi=[]; D_lo=[]; D_hi=[]
                for r in range(R):
                    hi=int(np.argmax(means[r])); lo=int(np.argmin(means[r]))
                    if K>1:
                        competitors_hi=np.max(np.delete(means[r]+rad[r],hi))
                        competitors_lo=np.min(np.delete(means[r]-rad[r],lo))
                    else:
                        competitors_hi=-np.inf; competitors_lo=np.inf
                    # Unique-extrema certificate: chosen max lower bound exceeds all
                    # competitor upper bounds; chosen min upper bound is below all
                    # competitor lower bounds.
                    local_ok.append(bool(means[r,hi]-rad[r,hi] > competitors_hi and means[r,lo]+rad[r,lo] < competitors_lo))
                    lower=means[r]-rad[r]; upper=means[r]+rad[r]
                    low=max(0.0,float(np.max(lower)-np.min(upper)))
                    high=float(np.max(upper)-np.min(lower)); C_lo.append(low); C_hi.append(high)
                    d=float(means[r]@weights); dr=float(np.sum(np.abs(weights)*rad[r])); D_lo.append(d-dr); D_hi.append(d+dr)
                for rr in range(R):
                    if stopped_C_ext_rel[rr] is None and local_ok[rr]:
                        stopped_C_ext_rel[rr]=total
                        false_C_ext_rel[rr]=bool(int(np.argmax(means[rr])) != int(np.argmax(truths[rr])) or int(np.argmin(means[rr])) != int(np.argmin(truths[rr])))
                order=np.argsort(-np.asarray(C_lo)); chosen=int(order[0]); others=[j for j in range(R) if j!=chosen]
                if stopped_top is None and all(C_lo[chosen]>C_hi[j] for j in others):
                    stopped_top=total
                    false_top=bool(chosen != true_top)
                nonzero=[r for r in range(R) if abs(true_D[r])>1e-9]
                for rr in nonzero:
                    if stopped_D_rel[rr] is None and ((D_lo[rr]>0) or (D_hi[rr]<0)):
                        stopped_D_rel[rr]=total
                        false_D_rel[rr]=bool((D_lo[rr]>0 and true_D[rr] <= 0) or (D_hi[rr]<0 and true_D[rr] >= 0))
                ext_done=all(x is not None for x in stopped_C_ext_rel)
                d_done=all(stopped_D_rel[r] is not None for r in nonzero)
                if (ext_done and stopped_top is not None and d_done) or total>=int(max_n): break
                n_add=min(int(batch),int(max_n)-total)
                if n_add<=0: break
                if mode=='uniform':
                    draw=rng.multinomial(n_add,np.full(R*K,1.0/(R*K))).reshape(R,K)
                elif mode=='D_targeted':
                    cell=np.tile(np.abs(weights)*sigmas,R); p=cell/cell.sum(); draw=rng.multinomial(n_add,p).reshape(R,K)
                elif mode=='C_extremal':
                    # Local-extrema allocation.  To certify max/min we must shrink
                    # the current extremum and its strongest competing confidence
                    # bound for every relation.
                    choices=[]
                    for rr in range(R):
                        hi=int(np.argmax(means[rr])); lo=int(np.argmin(means[rr]))
                        if K>1:
                            up=means[rr]+rad[rr]; lowb=means[rr]-rad[rr]
                            hi_candidates=[aa for aa in range(K) if aa != hi]
                            lo_candidates=[aa for aa in range(K) if aa != lo]
                            hi_comp=max(hi_candidates,key=lambda aa:up[aa])
                            lo_comp=min(lo_candidates,key=lambda aa:lowb[aa])
                            choices.extend([(rr,hi),(rr,hi_comp),(rr,lo),(rr,lo_comp)])
                        else:
                            choices.append((rr,0))
                    choices=list(dict.fromkeys(choices)) or [(0,0)]
                    draw=np.zeros((R,K),dtype=int)
                    for t in range(n_add): rr,aa=choices[t%len(choices)]; draw[rr,aa]+=1
                else:
                    # Global Top-K successive elimination.  A relation remains a
                    # candidate while its capacity upper bound can beat the largest
                    # lower bound.  Sample exactly the cells that drive C_hi/C_lo.
                    c_lo_arr=np.asarray(C_lo); c_hi_arr=np.asarray(C_hi)
                    best_lower=float(np.max(c_lo_arr))
                    candidate=[rr for rr in range(R) if c_hi_arr[rr] >= best_lower-1e-15]
                    if not candidate: candidate=[int(np.argmax(c_hi_arr))]
                    choices=[]
                    for rr in candidate:
                        up=means[rr]+rad[rr]; lowb=means[rr]-rad[rr]
                        choices.extend([(rr,int(np.argmax(up))),(rr,int(np.argmin(lowb))),(rr,int(np.argmax(lowb))),(rr,int(np.argmin(up)))])
                    choices=list(dict.fromkeys(choices)) or [(0,0)]
                    draw=np.zeros((R,K),dtype=int)
                    for t in range(n_add): rr,aa=choices[t%len(choices)]; draw[rr,aa]+=1
                # Draw the newly allocated observations and update cumulative sums.
                for rr in range(R):
                    for aa in range(K):
                        n=int(draw[rr,aa])
                        if n<=0: continue
                        sums[rr,aa]+=float(np.sum(rng.normal(loc=truths[rr,aa],scale=sigmas[aa],size=n)))
                        counts[rr,aa]+=n
            local_gaps=[]
            for q in truths:
                srt=np.sort(q); local_gaps.append(min(srt[-1]-srt[-2],srt[1]-srt[0]))
            csort=np.sort(true_C); topgap=float(csort[-1]-csort[-2]) if R>1 else float('inf')
            ext_times=[x if x is not None else max_n+1 for x in stopped_C_ext_rel]
            d_times=[stopped_D_rel[r] if stopped_D_rel[r] is not None else max_n+1 for r in nonzero]
            rows.append({'mode':mode,'local_regime':local_regime,'topk_regime':topk_regime,'local_gap_min':float(min(local_gaps)),'topk_gap':topgap,'designed_topk_gap':global_gap,'topk_gap_design_abs_error':abs(topgap-global_gap),'min_abs_D':float(np.min(np.abs(true_D[np.abs(true_D)>1e-9]))) if np.any(np.abs(true_D)>1e-9) else 0.0,'N_extrema':float(np.median(ext_times)),'N_topk':stopped_top or max_n+1,'N_Dsign':float(np.median(d_times)) if d_times else max_n+1,'extrema_relation_stop_times':ext_times,'Dsign_relation_stop_times':d_times,'top_truth_relation':true_top,'looks_used':looks_used,'final_total_samples':int(np.sum(counts)),'false_extrema_certificates':[x for x in false_C_ext_rel if x is not None],'false_topk_certificate':false_top,'false_Dsign_certificates':[false_D_rel[r] for r in nonzero if false_D_rel[r] is not None]})
    out={}
    for mode in ('uniform','D_targeted','C_extremal','C_topk_targeted'):
        rr=[r for r in rows if r['mode']==mode]; out[mode]={key:float(np.median([r[key] for r in rr])) for key in ('N_extrema','N_topk','N_Dsign')}
        out[mode]['topk_stopped_fraction']=float(np.mean([r['N_topk']<=max_n for r in rr]));
        ext_times=[x for r in rr for x in r['extrema_relation_stop_times']]; d_times=[x for r in rr for x in r['Dsign_relation_stop_times']]
        out[mode]['extrema_stopped_fraction']=float(np.mean([x<=max_n for x in ext_times])) if ext_times else 0.0; out[mode]['Dsign_stopped_fraction']=float(np.mean([x<=max_n for x in d_times])) if d_times else 0.0; out[mode]['median_final_samples']=float(np.median([r['final_total_samples'] for r in rr]));
        ext_emitted=[x for r in rr for x in r['false_extrema_certificates']]; top_emitted=[r['false_topk_certificate'] for r in rr if r['false_topk_certificate'] is not None]; d_emitted=[x for r in rr for x in r['false_Dsign_certificates']]
        for emitted,key in [(ext_emitted,'extrema_false_certificate_rate'),(top_emitted,'topk_false_certificate_rate'),(d_emitted,'Dsign_false_certificate_rate')]:
            out[mode][key]=float(np.mean(emitted)) if emitted else None
            out[mode][key.replace('_rate','_count')]=int(sum(bool(x) for x in emitted))
            out[mode][key.replace('_rate','_emitted')]=int(len(emitted))
    strata={'topk':{},'local':{}}
    for family,field,metric in [('topk','topk_regime','N_topk'),('local','local_regime','N_extrema')]:
        for name in ('small','mid','large'):
            strata[family][name]={}
            for mode in ('uniform','D_targeted','C_extremal','C_topk_targeted'):
                rr=[r for r in rows if r['mode']==mode and r[field]==name]
                strata[family][name][mode]={'n':len(rr),'median_N':float(np.median([r[metric] for r in rr])) if rr else None,'stopped_fraction':float(np.mean([r[metric]<=max_n for r in rr])) if rr else None,'median_gap':float(np.median([r['topk_gap' if family=='topk' else 'local_gap_min'] for r in rr])) if rr else None}
    return {'protocol_version':PROTOCOL_VERSION,'development_only':True,'instances':int(instances),'seed':int(seed),'delta':float(delta),'max_n':int(max_n),'noise_scale':float(noise_scale),'sequential_confidence':{'method':'finite-look Bonferroni Gaussian envelope','looks':int(n_looks),'z':z,'familywise_cells':int(K*R)},'geometry_generator_audit':{'max_topk_gap_design_abs_error':float(max(r['topk_gap_design_abs_error'] for r in rows)) if rows else 0.0,'stratified_generation':True},'by_allocation':out,'geometry_strata':strata}

def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--instances',type=int,default=200); p.add_argument('--seed',type=int,default=0); p.add_argument('--K',type=int,default=6); p.add_argument('--relations',type=int,default=5); p.add_argument('--delta',type=float,default=.05); p.add_argument('--max-n',type=int,default=4096); p.add_argument('--batch',type=int,default=16); p.add_argument('--noise-scale',type=float,default=.35); p.add_argument('--out',default='research/high_value_extensions/functional/stopping_summary.json'); a=p.parse_args(argv); payload=run(a.instances,a.seed,a.K,a.relations,a.delta,a.max_n,a.batch,a.noise_scale); atomic_json(Path(a.out),payload); print(json.dumps(payload,indent=2)); return 0
if __name__=='__main__': raise SystemExit(main())
