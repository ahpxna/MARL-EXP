"""Paired administrative-censoring diagnostics; does not rerun experiments.
Each input remains a separate experiment: changing max_n changes its Bonferroni
threshold. Legacy RNG also changes the worlds when max_n changes. Inputs
remain separate experiments; matching keys alone do not establish pairing.
"""
import argparse, hashlib, json, math, statistics
from pathlib import Path


def median_interval(values, confidence=.95):
    """Exact binomial order-statistic interval, including small-n infinities."""
    values=sorted(values); n=len(values)
    if not n:
        return dict(n=0, lower=None, upper=None, order_indices=None)
    k=0
    for j in range(1,n//2+1):
        if sum(math.comb(n,i) for i in range(j))/2**n <= (1-confidence)/2:
            k=j
    def endpoint(rank):
        value=(-math.inf if rank==0 else math.inf if rank==n+1 else values[rank-1])
        return dict(value=value if math.isfinite(value) else None,
                    interpretation='observed order statistic' if math.isfinite(value)
                    else ('unbounded below' if rank==0 else 'upper endpoint unidentified'))
    return dict(n=n, lower=endpoint(k), upper=endpoint(n-k+1),
                order_indices=[k,n-k+1], confidence_at_least=confidence,
                assumptions='iid instance-level quantities under the stated generator; PRNG treated as sampling')


def restricted_time(row, horizon):
    t=row['N_certificate']
    return horizon if t is None else min(t,horizon)


def analyze(path):
    data=json.loads(path.read_text());H=data['max_n'];runs=data['runs_by_variant']
    variants={}
    for v,rows in runs.items():
        keyed={(x['seed'],x['instance_id']):x for x in rows}
        assert len(keyed)==len(rows), ('duplicate instance keys',v)
        for x in rows:
            assert x['certificate_emitted'] == (x['N_certificate'] is not None), (v,x)
            if x['N_certificate'] is not None:
                assert 0 <= x['N_certificate'] <= H
        variants[v]=keyed
    keys=set(variants['uniform'])
    assert keys and all(set(rows)==keys for rows in variants.values())
    for k in keys:
        assert len({rows[k]['true_topk_gap'] for rows in variants.values()})==1
        hashes={rows[k].get('world_sha256') for rows in variants.values()}
        assert len(hashes)==1, ('unmatched worlds within experiment',k)
    summary={}
    n=len(keys)
    for v,rows in variants.items():
        events=sorted(x['N_certificate'] for x in rows.values() if x['certificate_emitted'])
        # First empirical CDF crossing of 1/2; avoid averaging an event time
        # with the numeric H+1 censor sentinel at exactly 50% events.
        kth=math.ceil(len(rows)/2)
        summary[v]=dict(n=len(rows),certificates=len(events),certificate_fraction=len(events)/len(rows),
            median_first_CDF_crossing=events[kth-1] if len(events)>=kth else None,
            reported_median= data['by_variant'][v]['median_N_certificate'],
            median_distribution_free_interval_95=median_interval(
                [x['N_certificate'] if x['certificate_emitted'] else math.inf for x in rows.values()]),
            restricted_mean_to_horizon=statistics.mean(restricted_time(x,H) for x in rows.values()),
            false_safe_count=sum(x['false_safe'] is True for x in rows.values()))
    paired=[]
    for v,rows in variants.items():
        if v=='uniform':continue
        only_v=sum(rows[k]['certificate_emitted'] and not variants['uniform'][k]['certificate_emitted'] for k in keys)
        only_u=sum(variants['uniform'][k]['certificate_emitted'] and not rows[k]['certificate_emitted'] for k in keys)
        pairs=[(rows[k],variants['uniform'][k]) for k in keys]
        rmst_diff=[restricted_time(x,H)-restricted_time(y,H) for x,y in pairs]
        both=[(x['N_certificate'],y['N_certificate']) for x,y in pairs if x['certificate_emitted'] and y['certificate_emitted']]
        wins=sum(x<y for x,y in both);losses=sum(x>y for x,y in both);ties=len(both)-wins-losses
        sign_p=min(1.,2*sum(math.comb(wins+losses,i) for i in range(min(wins,losses)+1))/2**(wins+losses)) if wins+losses else None
        ratios=[y/x for x,y in both if x>0]
        paired.append(dict(variant=v,
            uniform_over_variant_ratio_among_both_certified=dict(
                n=len(ratios), zero_denominator_excluded=sum(x==0 for x,y in both),
                median=statistics.median(ratios) if ratios else None,
                median_distribution_free_interval_95=median_interval(ratios)),only_variant_certifies=only_v,only_uniform_certifies=only_u,
            conditional_on_both_certifying=dict(variant_wins=wins,uniform_wins=losses,ties=ties,two_sided_sign_p=sign_p,
                caveat='This conditional comparison does not establish unconditional population dominance.'),
            both_certify=sum(x['certificate_emitted'] and y['certificate_emitted'] for x,y in pairs),
            mean_paired_restricted_cost_difference=statistics.mean(rmst_diff),
            sign_convention='negative favors variant; administrative censoring at H'))
    strata=[]
    for lo,hi in [(0,.02),(.02,.05),(.05,.1),(.1,.2),(.2,math.inf)]:
        kk=[k for k in keys if lo<=variants['uniform'][k]['true_topk_gap']<hi]
        strata.append(dict(gap_lo=lo,gap_hi=hi if math.isfinite(hi) else None,n=len(kk),
            certificates={v:sum(rows[k]['certificate_emitted'] for k in kk) for v,rows in variants.items()}))
    groups={}
    for name,kk in {
        'no_variant_certifies':[k for k in keys if not any(rows[k]['certificate_emitted'] for rows in variants.values())],
        'at_least_one_variant_certifies':[k for k in keys if any(rows[k]['certificate_emitted'] for rows in variants.values())],
        'C_anytime_does_not_certify':[k for k in keys if not variants['C_anytime'][k]['certificate_emitted']]
    }.items():
        groups[name]=dict(n=len(kk),median_true_gap=statistics.median(
            [variants['uniform'][k]['true_topk_gap'] for k in kk]) if kk else None)
    return dict(certification_groups=groups, rng_protocol=data.get('rng_protocol','legacy_sequential'),
        input=str(path.resolve()),input_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
        max_n=H,seeds=data['seeds'],instances_per_seed=data['instances_per_seed'],by_variant=summary,
        paired_against_uniform=paired,gap_strata=strata)


def main():
    p=argparse.ArgumentParser();p.add_argument('inputs',nargs='+');p.add_argument('--out',required=True);a=p.parse_args()
    out=Path(a.out)
    if out.exists():raise SystemExit(f'refusing to overwrite {out}')
    result=dict(evidence_class='REANALYSIS_OF_PAIRED_DEVELOPMENT_RUNS',
        scope='No cross-seed paired comparison, no finite-sample stopping theorem, no inference that censored runs can never certify.',
        horizon_caveat='Calibration depends on max_n. Legacy RNG also changes worlds and cell noise prefixes; equal seed/instance IDs do not justify cross-horizon pairing.',
        results=[analyze(Path(p)) for p in a.inputs],script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    cross=[]
    for i,left in enumerate(a.inputs):
        for right in a.inputs[i+1:]:
            dl=json.loads(Path(left).read_text()); dr=json.loads(Path(right).read_text())
            xl={(x['seed'],x['instance_id']):x for x in dl['runs_by_variant']['uniform']}
            xr={(x['seed'],x['instance_id']):x for x in dr['runs_by_variant']['uniform']}
            common=sorted(xl.keys() & xr.keys())
            if common:
                gap_equal=sum(xl[k]['true_topk_gap']==xr[k]['true_topk_gap'] for k in common)
                hash_equal=sum(xl[k].get('world_sha256') is not None and
                               xl[k].get('world_sha256')==xr[k].get('world_sha256') for k in common)
                cross.append(dict(left=left,right=right,common_keys=len(common),
                    equal_true_gap=gap_equal,verified_equal_world_hash=hash_equal,
                    different_worlds_detected=gap_equal<len(common),
                    common_worlds_verified=hash_equal==len(common),
                    caution='Equal gap alone is insufficient to verify equal worlds or noise prefixes.'))
    result['cross_input_pairability']=cross
    out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'out':str(out),'datasets':len(result['results'])}))
if __name__=='__main__':main()
