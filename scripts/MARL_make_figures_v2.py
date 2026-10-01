#!/usr/bin/env python3
"""v2 of the four main figures (v1: MARL_make_figures.py, unchanged), corrected per
MARL_E1_INDEPENDENT_AUDIT_20260927 §7: per-setting E1a lower bounds, allotted-query labels, the
uniform/targeted duplicate marked as a negative control, fig1 labelled a best-gain illustration.
Built ONLY from saved artifacts (read-only).

Fig 1  traffic scene (heterogeneous receivers, exact oracle): the prefix profile and the R=1
       repaired profile for one snapshot where repair helps, and one where it does not.
Fig 2  controlled frontier (E1): geometric floor by R and learning regret by N (E1b);
       worst-case error vs N/|Amb| against the proved T2 bounds (E1a).
Fig 3  traffic resource-quality (Step 3 pilot test panel): gain over the same prefix vs extra
       accounted bytes for true-scored search, learned R1 and direct search with the same critic;
       post-grant selection latency (latency benchmark).
Fig 4  acquisition ablation (E1): proxy / uniform / targeted / adaptive at matched N.
Every panel states its evidence class in the title.  Oracle rows are labelled as oracle.
"""
from __future__ import annotations
import argparse, gzip, json
from collections import defaultdict
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[1]


def fig1(hetero_records, out):
    rows = [json.loads(l) for l in gzip.open(hetero_records, 'rt')]
    best, flat = None, None
    for r in rows:
        for e in r['evals']:
            gain = e['adv_R1']['value'] - e['adv_R0']['value']
            if best is None or gain > best[0]:
                best = (gain, r, e)
            if gain == 0 and flat is None:
                flat = (gain, r, e)
    fig, axes = plt.subplots(1, 2, figsize=(10, 4.4))
    for ax, (gain, r, e), title in ((axes[0], best, 'BEST-GAIN illustration (selected max)'), (axes[1], flat, 'no repair needed')):
        m = len(e['K']); M = np.zeros((m, m))
        P = e['adv_R0']['sets']; S = e['adv_R1']['sets']
        for i in range(m):
            for j in range(m):
                p, s = (P[i] >> j) & 1, (S[i] >> j) & 1
                M[i, j] = 1 if p and s else (2 if s and not p else (3 if p and not s else 0))
        cmap = matplotlib.colors.ListedColormap(['white', '#9ecae1', '#31a354', '#de2d26'])
        ax.imshow(M, cmap=cmap, vmin=0, vmax=3)
        ax.set_xlabel('sender'); ax.set_ylabel('receiver (capacity k_i)')
        ax.set_yticks(range(m)); ax.set_yticklabels([f'{i} ({e["K"][i]})' for i in range(m)])
        ax.set_xticks(range(m))
        ax.set_title(f'{title}: {r["episode_id"]} t={r["t"]}\nR=0 {e["adv_R0"]["value"]:.0f} -> R=1 {e["adv_R1"]["value"]:.0f} '
                     f'({e["adv_R1"]["bytes"] - e["adv_R0"]["bytes"]:+d} B)', fontsize=9)
    fig.suptitle('Fig 1 (ORACLE, frozen MP2, held-phase H=3): prefix (blue) vs one patch per receiver '
                 '(green added, red removed)', fontsize=9)
    fig.tight_layout(); fig.savefig(out / 'fig1_traffic_scene.png', dpi=160); plt.close(fig)


def fig2_fig4(e1_json, out):
    E = json.loads(Path(e1_json).read_text())
    B = E['E1b']; curves = defaultdict(dict)
    for c in B['curves']:
        curves[(c['R'], c['method'])][c['N']] = c
    # Fig 2
    fig, axes = plt.subplots(1, 2, figsize=(11, 4.2))
    ax = axes[0]
    for R, col in ((0, 'k'), (1, 'tab:blue'), (2, 'tab:red')):
        d = curves[(R, 'targeted')]; Ns = sorted(d)
        ax.plot(Ns, [d[n]['global_regret'] for n in Ns], '-o', color=col, ms=3, label=f'R={R} targeted calibration')
        fl = B.get('geometric_floor_same_instances', B['geometric_floor_exact'])
        ax.axhline(fl[str(R)] if str(R) in fl else fl[R], color=col, ls=':', lw=1)
    ax.set_xscale('log'); ax.set_xlabel('allotted paired queries N (nominal)'); ax.set_ylabel('global regret (value units)')
    ax.set_title('E1b Bayes-decoder task (mean-structure extension, NOT the Gaussian pair channel):\nfloor (dotted) by R; this full-pool strategy by N', fontsize=8)
    ax.legend(fontsize=7)
    ax = axes[1]
    for s in E['E1a']:
        c = s['curves']['targeted']
        ln, = ax.plot([e['N'] / s['n_amb'] for e in c], [e['worst'] for e in c], '-', lw=1,
                      label=f'|Amb|={s["n_amb"]} (m={s["m"]},k={s["k"]},R={s["R"]}, beta={s["beta"]:g})')
        ax.axvline(s['proved_lower'] / s['n_amb'], color=ln.get_color(), ls='--', lw=0.8)
    ax.plot([], [], 'k--', lw=0.8, label='proved lower / |Amb| (same colour, per setting)')
    ax.axhline(E['E1a'][0]['alpha'], color='gray', ls=':', lw=1)
    ax.set_xscale('log'); ax.set_xlabel('nominal N / |Amb| (each arm gets floor(N/|Amb|))'); ax.set_ylabel('worst-case error')
    ax.set_title('E1a exact T2 needle model: block tests vs the per-arm proved lower bound', fontsize=9)
    ax.legend(fontsize=6)
    fig.suptitle('Fig 2 (CONTROLLED SIMULATION)', fontsize=9)
    fig.tight_layout(); fig.savefig(out / 'fig2_controlled_frontier.png', dpi=160); plt.close(fig)
    # Fig 4
    fig, axes = plt.subplots(1, 3, figsize=(14, 4.0))
    for ax, R in zip(axes[:2], (1, 2)):
        for mth, col in (('proxy', 'tab:gray'), ('uniform', 'tab:orange'), ('targeted', 'tab:blue'), ('adaptive', 'tab:green')):
            d = curves[(R, mth)]; Ns = sorted(d)
            lab = {'uniform': 'uniform (= targeted here: negative control)', 'targeted': 'targeted (= uniform here)',
                   'adaptive': 'adaptive (EXPLORATORY)'}.get(mth, mth)
            ax.plot(Ns, [d[n]['reachable_regret'] for n in Ns], '-o', ms=3, color=col, label=lab)
        pre = curves[(R, 'prefix')][0]['reachable_regret']
        ax.axhline(pre, color='k', ls=':', lw=1, label='prefix (no calibration)')
        ax.set_xscale('log'); ax.set_xlabel('allotted paired queries N (nominal)'); ax.set_ylabel('regret within F_R')
        ax.set_title(f'E1b, R={R}: same N, same decision rule', fontsize=9); ax.legend(fontsize=7)
    ax = axes[2]
    s = E['E1a'][-1]
    for mth, col in (('proxy_only', 'tab:gray'), ('uniform_all_ksets', 'tab:orange'), ('targeted', 'tab:blue')):
        c = s['curves'][mth]
        ax.plot([e['N'] for e in c], [e['worst'] for e in c], '-', color=col, label=mth)
    ax.axvline(s['proved_lower'], color='k', ls='--', lw=1, label='proved lower (targeted class)')
    ax.set_xscale('log'); ax.set_xlabel('N'); ax.set_ylabel('worst-case error')
    ax.set_title(f'E1a |Amb|={s["n_amb"]}, C(m,k)={s["n_ksets"]}', fontsize=9); ax.legend(fontsize=7)
    fig.suptitle('Fig 4 (CONTROLLED SIMULATION): acquisition ablation', fontsize=9)
    fig.tight_layout(); fig.savefig(out / 'fig4_acquisition_ablation.png', dpi=160); plt.close(fig)


def fig3(pilot_eval, latency_json, out):
    rows = [json.loads(l) for l in gzip.open(pilot_eval, 'rt')]
    agg = defaultdict(lambda: defaultdict(list))
    for r in rows:
        key = (r['method'], 'oracle' if r['critic'] is None else r['critic'].split('/')[0], r['cap_extra'])
        agg[key][r['episode_id']].append((r['value'] - r['prefix_value'], r['bytes'] - r['prefix_bytes']))
    fig, axes = plt.subplots(1, 2, figsize=(11, 4.2))
    ax = axes[0]
    style = {('oracle_search_R1', 'oracle'): ('k', 'true-scored R1 search (ORACLE)'),
             ('learned_R1', 'public'): ('tab:blue', 'learned R1, public critic'),
             ('direct_unrestricted', 'public'): ('tab:orange', 'direct search, same critic'),
             ('learned_R1', 'privileged'): ('tab:purple', 'learned R1, privileged summaries')}
    for (mth, var), (col, lab) in style.items():
        pts = []
        for cap in (0, 28, 56, None):
            ep = agg.get((mth, var, cap))
            if not ep:
                continue
            g = np.mean([np.mean([x[0] for x in v]) for v in ep.values()])
            b = np.mean([np.mean([x[1] for x in v]) for v in ep.values()])
            pts.append((b, g))
        pts = sorted(pts)
        ax.plot([p[0] for p in pts], [p[1] for p in pts], '-o', color=col, ms=4, label=lab)
    ax.axhline(0, color='gray', lw=0.8)
    ax.set_xlabel('extra accounted bytes over the prefix'); ax.set_ylabel('gain over the same prefix')
    ax.set_title('Step 3 pilot (seeds 61-64, now development data): caps +0/+28/+56/none', fontsize=9)
    ax.legend(fontsize=7)
    ax = axes[1]
    L = json.loads(Path(latency_json).read_text()); post = L['microseconds_post_grant_by_k']
    ks = sorted(post, key=int)
    for key, col in (('prefix', 'k'), ('table_lookup', 'tab:green'), ('repair_R1_indexed', 'tab:blue'),
                     ('repair_R1_fresh', 'tab:orange'), ('repair_R2_fresh', 'tab:red')):
        ax.plot([int(k) for k in ks], [post[k][key] for k in ks], '-o', ms=3, color=col, label=key)
    ax.set_yscale('log'); ax.set_xlabel('budget k'); ax.set_ylabel('post-grant selection time (us)')
    ax.set_title('PROTOCOL_v1 latency: tabulation is as fast as a prefix', fontsize=9); ax.legend(fontsize=7)
    fig.suptitle('Fig 3 (frozen MP2, held-phase H=3; latency on CPU, excludes transmission)', fontsize=9)
    fig.tight_layout(); fig.savefig(out / 'fig3_resource_quality.png', dpi=160); plt.close(fig)


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True)
    fig1(a.hetero, out); fig2_fig4(a.e1, out); fig3(a.pilot, a.latency, out)
    (out / 'SOURCES.json').write_text(json.dumps(vars(a), indent=1))
    print('figures written to', out)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--hetero', required=True); p.add_argument('--e1', required=True)
    p.add_argument('--pilot', required=True); p.add_argument('--latency', required=True)
    p.add_argument('--out', required=True)
    main(p.parse_args())
