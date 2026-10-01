#!/usr/bin/env python3
"""E3 figure for the manuscript (handoff F7: actor improvement and selector increment in SEPARATE panels; read-only).

(a) ACTOR improvement: per finished learned actor, max pressure's closed-loop Σ waiting against the actor with the
    same prefix communication (development 501-508, msguse/report.json 'mp2_vs_actual_pct', episode bootstrap).
    Filled marker: the actor passes G1 on its own; the caption states which recipe gate governs reading.
(b) SELECTOR increment on the SAME actor: closed loop, pilot panel 901-916, +84 B, direct; each selector variant
    against that actor's committed prefix (init seeds averaged per episode; bootstrap over episodes), from
    <actor>/cl_v3_direct/rows.json.  No max-pressure row here (that is panel a).
(c) Where the selector loses, development labels (48 states): realised gain of the choice of each evaluator arm
    (MARL_e3_paired_eval.py output <actor>/e3_dev_arms.json), with the oracle over the same candidates.
Self-checks (refuse to plot): every closed-loop method covers the prefix episodes; no deployable row used oracle
access; every panel-(c) arm is scored on the same number of states for one actor.
"""
from __future__ import annotations
import argparse, hashlib, json
from collections import defaultdict
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

M = Path(__file__).resolve().parents[1] / 'research/marl_budget'
ACTORS = [('BC s0 (pilot)', 'e3_run_20260928_003858/actor_s0'), ('BC s1', 'e3_run_20260928_003858/actor_s1'), ('BC s2', 'e3_run_20260928_003858/actor_s2'),
          ('BC s3', 'e3_run_seeds34_20260928/actor_s3'), ('BC s4', 'e3_run_seeds34_20260928/actor_s4'),
          ('scratch s0', 'e3_scratch_rs_20260928/actor_s0'), ('scratch s1', 'e3_scratch_rs_20260928/actor_s1'),
          ('scratch s2', 'e3_scratch_rs_20260928/actor_s2'), ('scratch s3', 'e3_scratch_seeds34_20260928/actor_s3'),
          ('scratch s4', 'e3_scratch_rs_20260928/actor_s4'), ('mix s3', 'e3_mixactor_20260928/actor_s3')]
CL = [('scratch s3 (gated)', 'e3_scratch_seeds34_20260928/actor_s3'), ('BC s0 (recorded, gate failed)', 'e3_run_20260928_003858/actor_s0')]
ARMS = [('legal', 'legal\nbid+head'), ('no_bid', 'no bid'), ('top2_bid', 'top-2 bid\n(10 B)'), ('queue_bid', 'queue bid\n(10 B)'),
        ('multi_head', 'multi-class\nhead'), ('acq_targeted', 'targeted\nacq. B=24'), ('acq_uniform', 'uniform\nacq. B=24'),
        ('privileged', 'privileged\n(diagnostic)')]
DEV = [('scratch s3', 'e3_scratch_seeds34_20260928/actor_s3'), ('BC s3', 'e3_run_seeds34_20260928/actor_s3')]


def boot(v, B=10000, seed=0):
    rng = np.random.default_rng(seed); v = np.asarray(v, float)
    return [float(x) for x in np.quantile([v[rng.integers(0, len(v), len(v))].mean() for _ in range(B)], [0.025, 0.975])]


def closed_loop(d):
    raw = (M / d / 'cl_v3_direct/rows.json').read_bytes(); rows = json.loads(raw); per = defaultdict(lambda: defaultdict(list))
    for r in rows:
        if not r['method'].startswith('oracle') and r['summary'].get('oracle_access_used'):
            raise SystemExit(f'SELF-CHECK FAIL: oracle access in {d} {r["method"]}')
        per[r['method'].split('/')[0]][r['episode']].append(r['queue_sum'])
    eps = sorted(per['prefix']); pq = {e: per['prefix'][e][0] for e in eps}; out = {}
    for m, dd in per.items():
        if m in ('prefix', 'mp2'):
            continue
        if sorted(dd) != eps:
            raise SystemExit(f'SELF-CHECK FAIL: {m} does not cover the prefix episodes in {d}')
        rel = [100 * (np.mean(dd[e]) - pq[e]) / pq[e] for e in eps]
        out[m] = dict(mean=float(np.mean(rel)), ci=boot(rel), n=len(eps), init_seeds=len(dd[eps[0]]))
    return out, hashlib.sha256(raw).hexdigest()


def main(a):
    act = []
    for name, d in ACTORS:
        f = M / d / 'msguse/report.json'
        if not f.exists():
            continue
        r = json.loads(f.read_text()); none = r['none_vs_actual_pct']; chg = r['input_action_change_rate']['none']
        g1 = bool(chg >= 0.10 and none['mean'] > 0 and none['ci95'][0] > 0)
        act.append(dict(actor=name, mp2=r['mp2_vs_actual_pct']['mean'], ci=r['mp2_vs_actual_pct']['ci95'], g1=g1, source=str(f.relative_to(M))))
    cl = {name: closed_loop(d) for name, d in CL}
    dev = {}
    for name, d in DEV:
        J = json.loads((M / d / 'e3_dev_arms.json').read_text())
        if len({J['states']}) != 1 or any(k not in J['arms'] for k, _ in ARMS):
            raise SystemExit(f'SELF-CHECK FAIL: panel (c) arms missing for {d}')
        diag = json.loads((M / d / 'selectors_v3_diag.json').read_text())
        orc = diag['legal_bid_resp_s0']['direct']['dev']['oracle_best']
        dev[name] = dict(states=J['states'], oracle=orc, arms={k: J['arms'][k] for k, _ in ARMS}, source=str((M / d / 'e3_dev_arms.json').relative_to(M)))
    fig, ax = plt.subplots(1, 3, figsize=(17.0, 4.6), gridspec_kw=dict(width_ratios=[1.45, 1.05, 1.9]))
    for x, r in enumerate(act):
        ax[0].errorbar(x, r['mp2'], yerr=[[r['mp2'] - r['ci'][0]], [r['ci'][1] - r['mp2']]], fmt='o', ms=8, capsize=3,
                       color='tab:green', mfc='tab:green' if r['g1'] else 'white')
    ax[0].axhline(0, color='gray', lw=0.8); ax[0].set_xticks(range(len(act))); ax[0].set_xticklabels([r['actor'].replace(' (pilot)', '*') for r in act], fontsize=7.5, rotation=45, ha='right')
    ax[0].set_ylabel('max pressure vs learned actor, Σ waiting (%)\nhigher = the actor is better')
    ax[0].set_title('(a) actor improvement (development 501-508)\nfilled: passes G1 on its own; * = BC pilot seed', fontsize=9)
    names = ['sel_nobid', 'sel_bid', 'sel_resp', 'sel_bid_resp']; w = 0.38
    for k, (cname, (res, _)) in enumerate(cl.items()):
        xs = np.arange(len(names)) + (k - 0.5) * w
        for x, n in zip(xs, names):
            o = res[n]; ax[1].errorbar(x, o['mean'], yerr=[[o['mean'] - o['ci'][0]], [o['ci'][1] - o['mean']]], fmt='o' if k == 0 else 's',
                                      ms=7, capsize=3, color='tab:blue' if k == 0 else 'tab:gray', label=cname if n == names[0] else None)
    ax[1].axhline(0, color='gray', lw=0.8); ax[1].set_xticks(range(len(names))); ax[1].set_xticklabels(['no bid', 'bid', 'head', 'bid+head'], fontsize=8)
    ax[1].set_ylabel('selector vs the SAME actor\'s prefix, Σ waiting (%)\nlower is better'); ax[1].legend(fontsize=7, frameon=False)
    ax[1].set_title('(b) selector increment, closed loop 901-916, +84 B', fontsize=9)
    for k, (name, D) in enumerate(dev.items()):
        xs = np.arange(len(ARMS)) + (k - 0.5) * w
        for x, (key, _) in zip(xs, ARMS):
            o = D['arms'][key]; y = o['mean_gain']; c = o['ci_episode']
            ax[2].errorbar(x, y, yerr=[[y - c[0]], [c[1] - y]], fmt='o' if k == 0 else 's', ms=6, capsize=2,
                           color=('tab:purple' if key == 'privileged' else 'tab:blue') if k == 0 else 'tab:gray', mfc='white' if key == 'privileged' else None,
                           label=f'{name} (oracle {D["oracle"]:.1f})' if key == 'legal' else None)
    ax[2].axhline(0, color='gray', lw=0.8); ax[2].set_xticks(range(len(ARMS))); ax[2].set_xticklabels([l for _, l in ARMS], fontsize=7)
    ax[2].set_ylabel('realised gain of the chosen profile\n(held-out development labels)'); ax[2].legend(fontsize=7, frameon=False, loc='upper left')
    ax[2].set_title('(c) where the loss is: evaluator arms on the same 48 development states\nhollow: privileged diagnostic (never deployable)', fontsize=9)
    fig.tight_layout(); od = Path(a.out); od.mkdir(parents=True, exist_ok=True)
    fig.savefig(od / 'fig_e3.png', dpi=200, bbox_inches='tight'); fig.savefig(od / 'fig_e3.pdf', bbox_inches='tight'); plt.close(fig)
    (od / 'fig_e3.json').write_text(json.dumps(dict(actors=act, closed_loop={k: dict(methods=v[0], rows_sha256=v[1]) for k, v in cl.items()}, dev=dev), indent=1))
    for r in act:
        print(f'{r["actor"]:14s} MP2 {r["mp2"]:+.1f}% [{r["ci"][0]:+.1f},{r["ci"][1]:+.1f}] G1 {r["g1"]}')
    for k, (res, _) in cl.items():
        print(k, {n: round(res[n]['mean'], 2) for n in names})
    for k, D in dev.items():
        print(k, {a_: round(D['arms'][a_]['mean_gain'], 2) for a_, _ in ARMS}, 'oracle', round(D['oracle'], 2))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('--out', default=str(M / 'figures_20260928_v4')); main(p.parse_args())
