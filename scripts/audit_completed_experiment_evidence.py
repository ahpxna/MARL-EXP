"""Independent recomputation of saved witnesses and pooled Monte Carlo diagnostics."""
import argparse, hashlib, itertools, json, math
from fractions import Fraction as F
from pathlib import Path
from collections import defaultdict
import numpy as np
from scipy.stats import chi2, binomtest
from scripts.verify_structural_tolerance_curves import scalar, staircase_union

ROOT=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def frontier_check(path):
    d=json.loads(path.read_text());m=d['m'];k=m//2
    cube=list(itertools.product((0,1),repeat=m)); S=set(range(k));T=set(range(k,m))
    def cls(x):
        if d['ansatz']=='full':return x
        if d['ansatz']=='symmetric':return (sum(x[:k]),sum(x[k:]))
        return (x[0],sum(x[1:k]),x[k],sum(x[k+1:]))
    rows=[]
    for p in d['points']:
        if p['status']!='OK':continue
        values={tuple(c['class']):F(c['value']) for c in p['world_classes']}
        f={x:values[cls(x)] for x in cube};z=(0,)*m
        theta=[f[tuple(int(i==j) for i in range(m))]-f[z] for j in range(m)]
        delta=F(0)
        for j in range(m):
            diffs=[f[x[:j]+(1,)+x[j+1:]]-f[x] for x in cube if x[j]==0]
            delta=max(delta,max(diffs)-min(diffs))
        losses={}
        for kept in itertools.combinations(range(m),k):
            residual=[f[x]-sum(theta[j]*x[j] for j in kept) for x in cube]
            losses[kept]=(max(residual)-min(residual))/2
        margin=min(abs(theta[j]) for j in S)-max(abs(theta[j]) for j in T)
        comparison=2*(losses[tuple(sorted(S))]-losses[tuple(sorted(T))])
        actual=2*(losses[tuple(sorted(S))]-min(losses.values()))
        assert delta==F(p['delta_square_exact']) and margin==F(p['margin_exact'])
        assert list(map(abs,theta))==list(map(F,p['response_oscillations_exact']))
        assert comparison==F(p['two_D_exact']) and comparison/delta==F(p['ratio_exact'])
        assert delta<=1 and margin>=F(p['mu'])
        upper=k*max(F(0),2-F(p['mu']))
        assert actual<=upper
        rows.append(dict(mu=p['mu'],actual_two_regret=str(actual),complement_comparison=str(comparison),
            independent_upper=str(upper),matches_global_upper=(actual==upper),delta=str(delta),margin=str(margin)))
    return dict(input=str(path),input_sha256=sha(path),m=m,rows=rows,
        interpretation='Exact finite witnesses; matching independent universal margin bound certifies these points. No LP optimality/WLOG assumption.')

def scalar_oracle(w,eps):
    m=len(w);total=sum(abs(x) for x in w)
    r={mask:abs(sum(w[j] for j in range(m) if not(mask>>j&1))) for mask in range(1<<m)}
    best={k:min(v for mask,v in r.items() if mask.bit_count()==k) for k in range(m+1)}
    masks=set()
    for perm in itertools.permutations(range(m)):
        selected=0;covered=0
        for k,j in enumerate(perm,1):
            selected |= 1<<j
            if k<m and F(r[selected]-best[k],total)<=eps: covered|=1<<(k-1)
        masks.add(covered)
    full=(1<<(m-1))-1;seen={0}
    for n in range(1,m):
        seen={u|v for u in seen for v in masks}
        if full in seen:return n
    raise AssertionError('no cover')

def structural_check():
    out=[]
    for w in ([1,-1,2,-2,3],[-2,-1,1,2,3,-3],[-32,7,29,-7,-8,-13,18]):
        curve=scalar(w)
        for row in curve:
            eps=F(row['eps_at_least']);chi=scalar_oracle(w,eps)
            assert chi==row['chi']
            out.append(dict(weights=w,epsilon=str(eps),chi=chi,method='independent enumeration of all permutations and exact cover'))
    old=json.loads((ROOT/'research/structural_tolerance_20260910/tolerance_curves.json').read_text())
    stairs={str(b):staircase_union(b) for b in ([2],[3],[4],[2,2])}
    for b,c in stairs.items():assert c==old['staircase_curves'][b]
    return dict(permutation_checks=out,recomputed_staircases=stairs,
        excluded_claims=['hand-entered m=12 rows','coefficient precision universally bounds curve richness','loose-by-two lower-bound claim'])

def integer_check(paths):
    grouped=defaultdict(list);inputs=[]
    for path in paths:
        d=json.loads(path.read_text());inputs.append(dict(path=str(path),sha256=sha(path),seed=d['seed']))
        for r in d['rows']:
            q=r['q'];n=2*q+1;N=r['N'];Ic=F(q**4,n);It=F(q*q,3)
            info=r['L']*Ic+r['b']*It
            assert info==F(r['information_exact'])==max(l*Ic+((N-l*n)//3)*It for l in range(N//n+1))
            assert r['queries_executed']==n*r['L']+3*r['b']<=N
            assert abs(r['exact_variance']-1/float(info))<1e-14
            p=.5*math.erfc(r['epsilon']*math.sqrt(float(info)/2))
            assert abs(p-r['phase_error_exact'])<1e-14
            grouped[q,N,r['sign']].append(r)
    rows=[];M=len(grouped)
    for (q,N,sign),rr in sorted(grouped.items()):
        n=sum(x['trials'] for x in rr);ratio=sum(x['trials']*x['mse_ratio'] for x in rr)/n
        hits=sum(round(x['trials']*x['phase_error_observed']) for x in rr);p=rr[0]['phase_error_exact']
        mse_ci=[float(chi2.ppf(.025/M,n)/n),float(chi2.ppf(1-.025/M,n)/n)]
        pval=binomtest(hits,n,p).pvalue
        rows.append(dict(q=q,N=N,sign=sign,trials=n,mse_ratio=ratio,
            null_mse_simultaneous_envelope_95=mse_ci,mse_within_envelope=mse_ci[0]<=ratio<=mse_ci[1],
            threshold_error_observed=hits/n,threshold_error_exact=p,
            threshold_error_binomial_p=pval,threshold_error_bonferroni_reject=bool(pval<.05/M)))
    return dict(inputs=inputs,cells=len(rows),trials=sum(x['trials'] for x in rows),rows=rows,
        scope='Two named A-free designs; classification threshold is fixed mu0=0.75, not the D6 allocation phase boundary. No full adaptive matching-regret or Gamma evidence.',
        multiple_comparisons='Separate 95% familywise checks for MSE and binomial error, Bonferroni across pooled cells.',
        all_mse_within_simultaneous_envelope=all(x['mse_within_envelope'] for x in rows),
        binomial_rejections=sum(x['threshold_error_bonferroni_reject'] for x in rows))

def main():
    p=argparse.ArgumentParser();p.add_argument('--out',required=True);a=p.parse_args();out=Path(a.out)
    if out.exists():raise SystemExit(f'refusing to overwrite {out}')
    base=ROOT/'research/confirm_ieee_20260911'
    front=[frontier_check(f) for f in sorted(base.glob('frontier*.json')) if 'manifest' not in f.name]
    print('frontier exact checks complete',flush=True)
    result=dict(evidence_class='INDEPENDENT_RECOMPUTATION_OF_EXISTING_RESULTS',frontier=front,
        integer_blocks=integer_check(sorted(base.glob('d6_integer_block_seed*.json'))),structural=structural_check(),
        script_sha256=sha(Path(__file__)))
    out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(out=str(out),frontier_points=sum(len(x['rows']) for x in front),
        integer_cells=result['integer_blocks']['cells'],integer_trials=result['integer_blocks']['trials'],
        all_mse_pass=result['integer_blocks']['all_mse_within_simultaneous_envelope'],
        binomial_rejections=result['integer_blocks']['binomial_rejections'])),flush=True)
if __name__=='__main__':main()
