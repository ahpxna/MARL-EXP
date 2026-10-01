#!/usr/bin/env python3
"""V-U with a SAME-INFORMATION NULL (ledger L-178).  The L-176 V-U split "the zero-byte student Z disagrees with the teacher T"
makes "relay R recovers T's decision there" true by construction for any other policy (Z is wrong there by definition).
Null: a second zero-byte student Z' (same teacher, same recipe, seed 100 + s; scripts/RUN_marl_e3_zero_replicate.sh), probed
on the SAME states (the rollouts are R's; records must align: L_relay, L_T, ages identical, asserted).
  recovery_R    = P(R = T | Z != T)       recovery_null = P(Z' = T | Z != T)      excess = recovery_R - recovery_null
  loss_R        = P(R != T | Z = T)       loss_null     = P(Z' != T | Z = T)
and symmetrically with Z and Z' exchanged.  excess > 0 is message value where local information did not settle Z's decision;
excess <= 0 means relay's "recovery" is what any second imitator gets.
"""
from __future__ import annotations
import argparse, json
from pathlib import Path
import numpy as np

A = Path('research/marl_budget/e3_theory_probe_20260930'); B = Path('research/marl_budget/e3_theory_probe_rep_20260930')


def am(L):
    return np.where(L > -1e8, L, -np.inf).argmax(-1)


def boot(x, g, n=4000, seed=0):
    """cluster bootstrap over traffic seeds of a per-record statistic (mean of x)."""
    u = np.unique(g); idx = {k: np.where(g == k)[0] for k in u}; rng = np.random.default_rng(seed); out = []
    for _ in range(n):
        pick = np.concatenate([idx[k] for k in rng.choice(u, len(u))]); out.append(x[pick].mean())
    return np.quantile(out, [0.025, 0.975])


def main(a):
    rep = {}; L = []
    for p in sorted(A.glob('*/probe.npz')):
        q = B / p.parent.name / 'probe.npz'
        if not q.exists() or not (B / p.parent.name / 'manifest.json').exists():
            continue
        d, e = dict(np.load(p)), dict(np.load(q))
        for k in ('L_relay', 'L_T', 'ages', 'seed', 'load', 't', 'recv'):
            assert np.array_equal(d[k], e[k]), f'{p.parent.name}: records do not align on {k}'
        R, T, Z, Zp = am(d['L_relay']), am(d['L_T']), am(d['L_0']), am(e['L_0'])
        g = d['seed'] * 100 + 0      # cluster = traffic seed (both headways together)
        S = Z != T; Sp = Zp != T
        r = dict(agree_T=dict(relay=float((R == T).mean()), zero=float((Z == T).mean()), zero_rep=float((Zp == T).mean())),
                 zero_vs_rep_disagree=float((Z != Zp).mean()),
                 split_Z=dict(share=float(S.mean()), recovery_relay=float((R == T)[S].mean()), recovery_null=float((Zp == T)[S].mean()),
                              loss_relay=float((R != T)[~S].mean()), loss_null=float((Zp != T)[~S].mean())),
                 split_Zrep=dict(share=float(Sp.mean()), recovery_relay=float((R == T)[Sp].mean()), recovery_null=float((Z == T)[Sp].mean())))
        # excess recovery on the Z-split, cluster-bootstrapped: per record indicator difference on S
        x = ((R == T).astype(float) - (Zp == T).astype(float)); xs = x[S]; gs = g[S]
        r['split_Z']['excess'] = float(xs.mean()); r['split_Z']['excess_ci'] = [float(v) for v in boot(xs, gs)]
        both = S & Sp; r['both_zero_wrong'] = dict(share=float(both.mean()), relay_recovery=float((R == T)[both].mean()))
        rep[p.parent.name] = r
        z = r['split_Z']
        L.append(f'{p.parent.name}: agree T relay {r["agree_T"]["relay"]:.3f} Z {r["agree_T"]["zero"]:.3f} Zrep {r["agree_T"]["zero_rep"]:.3f} (Z!=Zrep {r["zero_vs_rep_disagree"]:.3f}) | '
                 f'Z!=T {z["share"]:.3f}: relay {z["recovery_relay"]:.3f} vs null Zrep {z["recovery_null"]:.3f} -> excess {z["excess"]:+.3f} [{z["excess_ci"][0]:+.3f},{z["excess_ci"][1]:+.3f}] | '
                 f'both zero students wrong {r["both_zero_wrong"]["share"]:.3f}, relay right there {r["both_zero_wrong"]["relay_recovery"]:.3f}')
    print('\n'.join(L)); Path(a.out).write_text(json.dumps(rep, indent=1)); Path(a.out).with_suffix('.txt').write_text('\n'.join(L) + '\n')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('--out', default='research/marl_budget/e3_vu_null_report_20260930.json')
    main(p.parse_args())
