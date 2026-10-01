"""Ten-seed synthesis of BYTEBUDGET vs the 0-byte distilled student (30/09 14:2x EDT; ledger L-173).  Copied verbatim from the
session scratchpad (ten_seed.py) for provenance; development panel 901-964 x 8/16; two-level bootstrap (training seeds, then traffic
seeds with both headways together), 4000 draws, rng seed 0.  Rows read: distill_none_sN none, set_none_sN none,
bb_set_full_sN prefix (s0: d5_q4_bc3_fo), set_full_sN full.
"""
import json, os, numpy as np
E='/Users/phanan/cig-amf-main/research/marl_budget/e3_codesign_eval_20260929/'
def L(t, rule=None):
    p=E+t+'/rows.json'
    if not os.path.exists(E+t+'/manifest.json'): return None
    return {x['episode']:x['queue_sum'] for x in json.load(open(p)) if rule is None or x['rule']==rule}
eps=sorted(L('set_none_s0','none')); ts=sorted({e.split('_')[0] for e in eps}); idx={u:[i for i,e in enumerate(eps) if e.startswith(u+'_')] for u in ts}
def vec(d): return None if d is None else np.array([d[e] for e in eps])
bbtag={0:'d5_q4_bc3_fo'}; 
stu={s:vec(L(f'distill_none_s{s}','none' if s==0 else None)) for s in range(10)}
sn={s:vec(L(f'set_none_s{s}','none')) for s in range(10)}
bb={s:vec(L(bbtag.get(s,f'bb_set_full_s{s}'),'prefix')) for s in range(10)}
full={s:vec(L(f'set_full_s{s}' if s else 'set_full_s0','full')) for s in range(10)}
rng=np.random.default_rng(0)
def report(name,A,B):
    S=[s for s in range(10) if A.get(s) is not None and B.get(s) is not None]; per={s:A[s].sum()/B[s].sum()-1 for s in S}; bs=[]
    for _ in range(4000):
        ss=rng.choice(S,len(S)); ii=np.concatenate([idx[ts[p]] for p in rng.choice(len(ts),len(ts))]); bs.append(np.mean([A[s][ii].sum()/B[s][ii].sum()-1 for s in ss]))
    lo,hi=np.percentile(bs,[2.5,97.5])
    print(f'{name:40s} n_seeds={len(S)} {S}\n   per-seed: '+' '.join(f's{s}:{100*per[s]:+.1f}' for s in S)+f'\n   mean {100*np.mean(list(per.values())):+.1f}% [{100*lo:+.1f},{100*hi:+.1f}]  below 0: {sum(v<0 for v in per.values())}/{len(S)}')
report('BYTEBUDGET vs 0-byte student', bb, stu)
report('0-byte student vs set_none', stu, sn)
report('BYTEBUDGET vs set_none', bb, sn)
report('full delivery vs set_none', full, sn)
