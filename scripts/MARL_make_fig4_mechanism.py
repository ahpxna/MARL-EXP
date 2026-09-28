#!/usr/bin/env python3
"""F4 (readiness audit P4): the mechanism on the fixed-MP2 actor, from existing artifacts only (read-only).

(a) Held phase, preregistered B2 panel 601-616, +84 B direct: gain per method (init seeds averaged per
    episode; bootstrap over the 32 episodes), with edit rate and harm-over-edits; oracle level dashed.
(b) Offline -> closed loop: the share of the oracle's improvement realised by the response-bid selector
    in the held phase (B2) and in closed loop (B3 601-616 frozen, 1101-1116 frozen, B4 801-816 retrained).
(c) Target: continuation gain realised by the held-phase argmax against the continuation-best gain on
    the 16 development states of the target diagnostic (1:1 line = no mismatch).
Writes <out>/fig4_mechanism_mp2.{png,pdf,json}; every number is recomputed from the named files.
"""
from __future__ import annotations
import argparse, json
from collections import defaultdict
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

M = Path(__file__).resolve().parents[1] / 'research/marl_budget'
B2 = M / 'b2_confirm_20260927_225002/confirm'
CL = {'B3 601-616 (frozen)': M / 'b3_closed_loop_20260927_225248', '1101-1116 (frozen)': M / 'cl_baselines_20260927_232931',
      'B4 801-816 (DAgger)': M / 'b4_run_20260927_230436/cl_test'}
TD = M / 'target_diag_20260928_000455/rows.json'


def boot(v, B=10000, seed=0):
    rng = np.random.default_rng(seed); v = np.asarray(v, float)
    return [float(x) for x in np.quantile([v[rng.integers(0, len(v), len(v))].mean() for _ in range(B)], [0.025, 0.975])]


def b2():
    out = {}; orc = None
    for L in ('ctrl_history', 'ctrl_public', 'bid_queue', 'mlp_top2_joint'):
        per = defaultdict(list); er, hr = [], []
        for s in (0, 1, 2):
            j = json.loads((B2 / f'conf_{L}_s{s}.json').read_text())['results']['+84']
            sm = j['direct']['summary']
            for e, g in sm['gain_by_episode'].items():
                per[e].append(g)
            er.append(sm['edit_rate']); hr.append(sm['harm_over_edits'])
            if orc is None:
                orc = j['oracle_R1']['summary']
        v = [np.mean(per[e]) for e in sorted(per)]
        out[L] = dict(gain=float(np.mean(v)), ci=boot(v), edit_rate=float(np.mean(er)), harm_over_edits=float(np.mean(hr)))
    return out, float(orc['gain'])


def closed_loop(run):
    rows = json.loads((run / 'rows.json').read_text()); per = defaultdict(lambda: defaultdict(list))
    for r in rows:
        per[r['method'].split('/')[0]][r['episode']].append(r['queue_sum'])
    eps = sorted(per['prefix']); pq = {e: per['prefix'][e][0] for e in eps}
    rel = lambda m: np.array([(np.mean(per[m][e]) - pq[e]) / pq[e] for e in eps])
    b, o = rel('mlp_top2_joint'), rel('oracle_heldphase')
    rng = np.random.default_rng(0); sh = []
    for _ in range(10000):
        k = rng.integers(0, len(eps), len(eps)); sh.append(b[k].mean() / o[k].mean())
    return dict(share=float(b.mean() / o.mean()), ci=[float(x) for x in np.quantile(sh, [0.025, 0.975])], bid=float(b.mean()), oracle=float(o.mean()))


def main(a):
    g, orc = b2(); cl = {k: closed_loop(v) for k, v in CL.items()}
    S = json.loads(TD.read_text()); td = [(s['summary']['feas_any']['cont_best_gain'], s['summary']['feas_any']['cont_gain_of_held_best']) for s in S]
    fig, ax = plt.subplots(1, 3, figsize=(14.5, 4.2))
    names = {'ctrl_history': 'Direct\n(no bid)', 'ctrl_public': 'Direct\n(public ctx)', 'bid_queue': 'Queue bid\n(1 B)', 'mlp_top2_joint': 'Response bid\n(1 B)'}
    for x, (L, v) in enumerate(g.items()):
        ax[0].bar(x, v['gain'], yerr=[[v['gain'] - v['ci'][0]], [v['ci'][1] - v['gain']]], capsize=3, color='tab:blue' if L == 'mlp_top2_joint' else 'tab:gray')
        ax[0].text(x, v['ci'][1] + 0.3, f'edit {v["edit_rate"]:.2f}\nharm {v["harm_over_edits"]:.2f}', ha='center', fontsize=7)
    ax[0].axhline(orc, ls='--', color='k', lw=1); ax[0].text(3.4, orc, f'oracle {orc:.1f}', va='bottom', ha='right', fontsize=8)
    ax[0].set_xticks(range(len(g))); ax[0].set_xticklabels([names[k] for k in g], fontsize=8)
    ax[0].set_ylabel('held-phase gain over the prefix'); ax[0].set_title('(a) held phase, B2 panel 601-616, +84 B', fontsize=9)
    ax[0].set_ylim(0, orc * 1.12)
    held_share = g['mlp_top2_joint']['gain'] / orc
    labels = ['held phase\n(B2)'] + [k.replace(' (', '\n(') for k in cl]; vals = [held_share] + [v['share'] for v in cl.values()]
    errs = [[0] + [v['share'] - v['ci'][0] for v in cl.values()], [0] + [v['ci'][1] - v['share'] for v in cl.values()]]
    ax[1].bar(range(4), [100 * x for x in vals], yerr=[[100 * x for x in errs[0]], [100 * x for x in errs[1]]], capsize=3, color=['tab:blue'] + ['tab:orange'] * 3)
    ax[1].axhline(0, color='gray', lw=0.8); ax[1].set_xticks(range(4)); ax[1].set_xticklabels(labels, fontsize=8)
    ax[1].set_ylabel('% of the oracle improvement realised'); ax[1].set_title('(b) offline -> closed loop (response bid)', fontsize=9)
    cb, hb = zip(*td); lim = max(max(cb), max(hb)) * 1.1
    ax[2].scatter(cb, hb, s=18); ax[2].plot([min(0, min(hb)), lim], [min(0, min(hb)), lim], 'k--', lw=0.8)
    ax[2].axhline(0, color='gray', lw=0.8); ax[2].set_xlabel('continuation-best gain'); ax[2].set_ylabel('continuation gain of the held-phase argmax')
    ax[2].set_title(f'(c) target mismatch, 16 dev states: {100 * sum(hb) / sum(cb):.0f}% captured', fontsize=9)
    fig.suptitle('F4 — mechanism on the fixed max-pressure actor (development/confirmation artifacts; see JSON for sources)', fontsize=9)
    fig.tight_layout(); od = Path(a.out); od.mkdir(parents=True, exist_ok=True)
    fig.savefig(od / 'fig4_mechanism_mp2.png', dpi=200); fig.savefig(od / 'fig4_mechanism_mp2.pdf'); plt.close(fig)
    (od / 'fig4_mechanism_mp2.json').write_text(json.dumps(dict(b2_plus84_direct=g, b2_oracle=orc, held_share=held_share, closed_loop=cl,
        target_states=td, sources=dict(b2=str(B2), closed_loop={k: str(v) for k, v in CL.items()}, target=str(TD))), indent=1))
    print(json.dumps(dict(held_share=held_share, closed_loop={k: (round(v['share'], 3), [round(x, 3) for x in v['ci']]) for k, v in cl.items()},
                          b2={k: (round(v['gain'], 2), round(v['harm_over_edits'], 2)) for k, v in g.items()}, oracle=orc), indent=1))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out', default=str(M / 'figures_20260928_v4'))
    main(p.parse_args())
