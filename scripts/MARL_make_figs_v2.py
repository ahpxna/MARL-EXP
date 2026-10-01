#!/usr/bin/env python3
"""Figures of paper_marl_v2.tex (30/09 19:0x EDT; ledger L-178), made ONLY from saved report JSONs (no rerun):
  fig_prereg  e3_relayrot_panel_report_20260930.json            (pre-registered panel 2601-2664, L-175)
  fig_va      e3_theory_sim_20260930.json + e3_theory_cl_report_20260930.json   (V-A, L-176/L-177)
  fig_vs      e3_theory_cl_report_20260930.json                  (V-S)
  fig_vf      e3_theory_probe_report_20260930.json               (V-F)
  fig_vu      e3_vu_null_report_20260930.json + probe report + theory_cl report (V-U with the same-information null, L-178)
  fig_math    e3_math_replica_20260930.json (the channel mathematics in the replica, L-181)
Every plotted number is also written to figs_v2/figures_data.json.
"""
from __future__ import annotations
import json
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

M = Path('research/marl_budget'); OUT = Path('research/papers/_tex/figs_v2'); OUT.mkdir(exist_ok=True)
plt.rcParams.update({'font.size': 8, 'axes.titlesize': 8, 'axes.labelsize': 8, 'legend.fontsize': 7, 'xtick.labelsize': 7, 'ytick.labelsize': 7,
                     'pdf.fonttype': 42, 'axes.spines.top': False, 'axes.spines.right': False})
C0, C1, CG, CR, CP = '#0072B2', '#D55E00', '#009E73', '#CC79A7', '#E69F00'
DATA = {}
COND = ['iid', 'cap4', 'low']


def fig_prereg():
    r = json.loads((M / 'e3_relayrot_panel_report_20260930.json').read_text())
    fig, ax = plt.subplots(figsize=(3.3, 2.5)); y = 0; ticks = []; lab = []; D = {}
    for s, col in (('s0', C0), ('s1', C1)):
        for c in COND:
            a = r[s][f'PRIMARY {c}: relay+agefirst vs 0-byte student']; b = r[s][f'{c}: relay+prefix order vs 0-byte student']
            ax.errorbar(a[0], y + 0.15, xerr=[[a[0] - a[1]], [a[2] - a[0]]], fmt='o', color=col, ms=3.5, capsize=1.5, lw=1)
            ax.errorbar(b[0], y - 0.15, xerr=[[b[0] - b[1]], [b[2] - b[0]]], fmt='s', mfc='white', color=col, ms=3.2, capsize=1.5, lw=0.8)
            ticks.append(y); lab.append(f'seed {s[1]}, {c}'); D[f'{s}_{c}'] = dict(rotation=a, default_order=b); y += 1
        y += 0.4
    ax.axvline(0, color='k', lw=0.6); ax.set_yticks(ticks); ax.set_yticklabels(lab); ax.invert_yaxis()
    ax.set_xlabel('waiting vs zero-byte student (%)')
    ax.plot([], [], 'o', color='grey', ms=3.5, label='relay + rotating head (primary)'); ax.plot([], [], 's', mfc='white', color='grey', ms=3.2, label='relay, default order')
    ax.legend(loc='lower center', bbox_to_anchor=(0.45, 1.0), ncol=1, frameon=False, handletextpad=0.3)
    fig.tight_layout(); fig.savefig(OUT / 'fig_prereg.pdf'); plt.close(fig); DATA['fig_prereg'] = D


def fig_va():
    sim = json.loads((M / 'e3_theory_sim_20260930.json').read_text())['V_A']; cl = json.loads((M / 'e3_theory_cl_report_20260930.json').read_text())['V_A']
    fig, axs = plt.subplots(1, 3, figsize=(6.9, 2.1)); D = {'sim': [], 'closed_loop': {}}
    for capx, ls in (('low', '-'), ('cap4', '--')):
        pts = sorted([p for p in sim if p['capacity'] == capx and p['relay']], key=lambda p: p['beta'])
        if not pts:
            continue
        bs = [p['beta'] for p in pts]; XB = sorted({p['beta'] for p in sim}); pos = lambda b: XB.index(b)
        axs[0].plot([pos(b) for b in bs], [p['never_covered_pairs'] for p in pts], ls, color=C0, marker='.', label=f'never covered, {capx}')
        axs[1].plot([pos(b) for b in bs], [p['mean_age'] for p in pts], ls, color=C1, marker='.', label=f'mean age, {capx}')
        D['sim'] += pts
    raw = sorted([p for p in sim if p['capacity'] == 'low' and not p['relay']], key=lambda p: p['beta'])
    if raw:
        axs[0].plot([pos(p['beta']) for p in raw], [p['never_covered_pairs'] for p in raw], ':', color='grey', marker='.', label='never covered, low, raw')
    for a in axs[:2]:
        a.set_xticks(range(len(XB))); a.set_xticklabels([f'{b:g}' for b in XB], fontsize=6); a.set_xlabel(r'rotation share $\beta$'); a.legend(frameon=False, fontsize=6)
    axs[0].set_ylabel('share of (receiver, agent) pairs'); axs[1].set_ylabel('decision steps')
    axs[0].set_title('(a) coverage, traffic-free replica'); axs[1].set_title('(b) age, traffic-free replica')
    for s, col in (('s0', C0), ('s1', C1)):
        for c, mk in zip(COND, ('o', 's', '^')):
            v = cl.get(f'{s}_{c}') or {}
            bs = sorted(float(b) for b in v)
            ys = [v[str(b) if str(b) in v else repr(b)]['vs_student'][0] for b in bs]
            XC = [0.0, 0.05, 0.1, 0.25, 0.5, 1.0]
            axs[2].plot([XC.index(b) for b in bs], ys, '-', color=col, marker=mk, ms=3, lw=0.9, label=f'seed {s[1]} {c}')
            D['closed_loop'][f'{s}_{c}'] = dict(zip(map(str, bs), ys))
    axs[2].axhline(0, color='k', lw=0.6); axs[2].set_xticks(range(6)); axs[2].set_xticklabels(['0', '.05', '.1', '.25', '.5', '1'], fontsize=6); axs[2].set_xlabel(r'rotation share $\beta$')
    axs[2].set_ylabel('waiting vs zero-byte student (%)'); axs[2].set_title('(c) closed loop (development)'); axs[2].legend(frameon=False, ncol=1, fontsize=5.5, loc='center left', bbox_to_anchor=(1.0, 0.5))
    fig.tight_layout(); fig.savefig(OUT / 'fig_va.pdf'); plt.close(fig); DATA['fig_va'] = D


def fig_vs():
    vs = json.loads((M / 'e3_theory_cl_report_20260930.json').read_text())['V_S']
    fig, axs = plt.subplots(1, 2, figsize=(6.9, 2.3), sharey=True); D = {}
    sty = {'relay_agefirst': (C0, 'o', 'relay + rotating head'), 'relay_prefix': (C1, 's', 'relay, default order'),
           'setprefix': (CR, '^', 'set actor, stale cache kept'), 'FO': (CG, 'D', 'FO (fresh-only receiver)')}
    for ax, s in zip(axs, ('s0', 's1')):
        for cfg, (col, mk, lab) in sty.items():
            v = vs.get(f'{s}_{cfg}')
            if not v:
                continue
            ks = sorted(int(k) for k in v['vs_student']); e = [v['vs_student'][str(k)] for k in ks]
            ax.errorbar(ks, [x[0] for x in e], yerr=[[x[0] - x[1] for x in e], [x[2] - x[0] for x in e]], color=col, marker=mk, ms=3, lw=0.9, capsize=1.2, label=lab)
            D[f'{s}_{cfg}'] = dict(K=ks, vs_student=e, worse_with_more_packets_at_K=v['worse_with_more_packets_at_K'])
        ax.axhline(0, color='k', lw=0.6); ax.set_xlabel('decoded packets per receiver $K$ (constant)'); ax.set_title(f'seed {s[1]}')
    axs[0].set_ylabel('waiting vs zero-byte student (%)')
    h, l = axs[0].get_legend_handles_labels(); fig.legend(h, l, loc='lower center', ncol=4, frameon=False, fontsize=6.5)
    fig.tight_layout(rect=(0, 0.1, 1, 1)); fig.savefig(OUT / 'fig_vs.pdf'); plt.close(fig); DATA['fig_vs'] = D


def fig_vf():
    pr = json.loads((M / 'e3_theory_probe_report_20260930.json').read_text())
    fig, axs = plt.subplots(1, 2, figsize=(6.9, 2.0)); D = {}
    for run, col, ls in (('s0_agefirst_low', C0, '-'), ('s1_agefirst_low', C1, '-'), ('s0_prefix_low', C0, ':'), ('s1_prefix_low', C1, ':')):
        v = pr[run]['V_F_agree_by_max_age']; hs = sorted(int(h) for h in v if int(h) >= 1)
        axs[0].plot(hs, [v[str(h)][1] for h in hs], ls, color=col, marker='.', label=run.replace('_', ' '))
        D[run] = dict(by_age={h: v[str(h)] for h in map(str, hs)}, by_gap=pr[run]['V_F_agree_by_gap_quintile'])
    axs[0].set_xlabel('largest relayed age in the view (decision steps)'); axs[0].set_ylabel('P(relay action = fresh action)')
    axs[0].set_title('(a) agreement vs age, low capacity'); axs[0].legend(frameon=False, fontsize=6)
    for run, col in (('s0_agefirst_iid', C0), ('s1_agefirst_iid', C1), ('s0_agefirst_low', CG), ('s1_agefirst_low', CR)):
        q = pr[run]['V_F_agree_by_gap_quintile']; axs[1].plot(range(1, 6), q, '-', color=col, marker='.', label=run.replace('_', ' '))
        D.setdefault(run, {})['by_gap'] = q
    axs[1].set_xlabel('fresh-view decision margin quintile'); axs[1].set_ylabel('P(relay action = fresh action)'); axs[1].set_xticks(range(1, 6))
    axs[1].set_title('(b) agreement vs margin'); axs[1].legend(frameon=False, fontsize=6)
    fig.tight_layout(); fig.savefig(OUT / 'fig_vf.pdf'); plt.close(fig); DATA['fig_vf'] = D


def fig_vu():
    nu = json.loads((M / 'e3_vu_null_report_20260930.json').read_text()); cl = json.loads((M / 'e3_theory_cl_report_20260930.json').read_text())['V_A']
    runs = [f'{s}_{o}_{c}' for s in ('s0', 's1') for o in ('agefirst', 'prefix') for c in COND]
    fig, axs = plt.subplots(1, 2, figsize=(6.9, 2.2), gridspec_kw={'width_ratios': [1.6, 1]}); D = {}
    x = np.arange(len(runs)); rr = [nu[r]['split_Z']['recovery_relay'] for r in runs]; rn = [nu[r]['split_Z']['recovery_null'] for r in runs]
    axs[0].bar(x - 0.2, rr, 0.4, color=C0, label='relay student'); axs[0].bar(x + 0.2, rn, 0.4, color='lightgrey', edgecolor='grey', label='second zero-byte student (null)')
    axs[0].set_xticks(x); axs[0].set_xticklabels([r.replace('agefirst', 'rot').replace('prefix', 'def').replace('_', '\n') for r in runs], fontsize=5.5)
    axs[0].set_ylabel('recovery rate'); axs[0].set_title('(a) recovery where the zero-byte student errs'); axs[0].legend(frameon=False, fontsize=6)
    xs, ys, cs = [], [], []
    for r in runs:
        s, o, c = r.split('_'); b = '1.0' if o == 'agefirst' else '0.0'
        w = cl[f'{s}_{c}'][b]['vs_student'][0]; a = nu[r]['agree_T']['relay'] - nu[r]['agree_T']['zero']
        xs.append(a); ys.append(w); cs.append(C0 if s == 's0' else C1)
        D[r] = dict(recovery_relay=nu[r]['split_Z']['recovery_relay'], recovery_null=nu[r]['split_Z']['recovery_null'], excess=nu[r]['split_Z']['excess'],
                    excess_ci=nu[r]['split_Z']['excess_ci'], net_teacher_agreement=a, waiting_vs_student=w)
    axs[1].scatter(xs, ys, c=cs, s=12); rho = np.corrcoef(xs, ys)[0, 1]
    axs[1].axhline(0, color='k', lw=0.6); axs[1].axvline(0, color='k', lw=0.6)
    axs[1].set_xlabel('teacher agreement: relay minus zero-byte'); axs[1].set_ylabel('waiting vs zero-byte student (%)')
    axs[1].set_title(f'(b) 12 runs, Pearson r = {rho:.2f}')
    axs[1].scatter([], [], c=C0, s=12, label='seed 0'); axs[1].scatter([], [], c=C1, s=12, label='seed 1'); axs[1].legend(frameon=False, fontsize=6)
    fig.tight_layout(); fig.savefig(OUT / 'fig_vu.pdf'); plt.close(fig); D['pearson_r'] = float(rho); DATA['fig_vu'] = D


def fig_math():
    d = json.loads((M / 'e3_math_replica_20260930.json').read_text())
    fig, axs = plt.subplots(1, 2, figsize=(6.9, 2.3)); D = {}
    kinds = ['iid', 'cap4', 'low', 'const1', 'const2', 'const3', 'rich7']; x = np.arange(len(kinds))
    ag = [d['floor'][k]['agefirst']['mean_age'] for k in kinds]; hb = [d['floor'][k]['hub']['mean_age'] for k in kinds]
    inj = [d['floor'][k]['agefirst']['mean_injection_age'] for k in kinds]
    axs[0].bar(x - 0.2, ag, 0.4, color=C0, label='receiver age, age-first head'); axs[0].bar(x + 0.2, hb, 0.4, color=CP, label='receiver age, hub head')
    axs[0].plot(x, inj, 'k_', ms=14, mew=1.5, label='injection age, age-first (= floor for constant L)')
    axs[0].set_xticks(x); axs[0].set_xticklabels(kinds, fontsize=6.5); axs[0].set_ylabel('mean age (steps)'); axs[0].legend(frameon=False, fontsize=5.8, loc='upper left')
    axs[0].set_title('(a) receiver age vs injection floor')
    ks = sorted(int(k) for k in d['hetero'])
    for key, sub, col, ls, lab in (('homogeneous', 'relay_hub', 'k', '-', 'all K=k, relay, hub head'), ('one_rich', 'relay_hub', CP, '-', 'one K=k, rest 1: relay, hub head'),
                                   ('one_rich', 'relay_agefirst', C0, '--', 'one K=k, rest 1: relay, age-first head'), ('one_rich', 'raw_agefirst', CR, ':', 'one K=k, rest 1: raw packets')):
        ys = [d['hetero'][str(k)][key][sub]['mean_age'] for k in ks]; axs[1].plot(ks, ys, ls, color=col, marker='.', label=lab); D[f'{key}_{sub}'] = dict(zip(ks, ys))
    axs[1].set_xlabel('capacity k of the rich receiver(s)'); axs[1].set_ylabel('mean receiver age (steps)'); axs[1].legend(frameon=False, fontsize=5.8)
    axs[1].set_title('(b) heterogeneous capacity')
    fig.tight_layout(); fig.savefig(OUT / 'fig_math.pdf'); plt.close(fig)
    DATA['fig_math'] = dict(kinds=kinds, agefirst=ag, hub=hb, injection=inj, hetero=D)


def fig_seeds():
    d = json.loads((M / 'e3_seed_prediction_report_20260930.json').read_text())
    G = {int(k): v for k, v in d['G'].items()}; H = {int(k): v for k, v in d['H'].items()}
    fig, ax = plt.subplots(figsize=(3.3, 2.4))
    for s in sorted(G):
        if s not in H:
            continue
        col = C1 if s >= 6 else C0
        ax.scatter(H[s], G[s], c=col, s=16, zorder=3); ax.annotate(f's{s}', (H[s], G[s]), textcoords='offset points', xytext=(3, 3), fontsize=6)
    ax.axhline(0, color='k', lw=0.6); ax.axvline(0, color='k', lw=0.6)
    ax.scatter([], [], c=C0, s=16, label='seeds 1-5 (seen)'); ax.scatter([], [], c=C1, s=16, label='seeds 6-9 (predicted before run)')
    ax.set_xlabel('teacher headroom over compiled silence (%)'); ax.set_ylabel('relay gain vs zero-byte student (%)')
    ax.set_title(f"Spearman = {d['rho']:.2f}"); ax.legend(frameon=False, fontsize=5.8, loc='lower right')
    fig.tight_layout(); fig.savefig(OUT / 'fig_seeds.pdf'); plt.close(fig); DATA['fig_seeds'] = d


def fig_rich():
    import sys
    sys.path.insert(0, 'scripts')
    from MARL_e3_music_report import paired
    E = M / 'e3_rich_dev_20260930'; Cd = M / 'e3_codesign_eval_20260929'; R = M / 'e3_satrot_eval_20260930'
    rows = lambda p, rule: {r['episode']: r for r in json.loads(Path(p).read_text()) if r['rule'] == rule}
    fig, ax = plt.subplots(figsize=(3.3, 2.3)); D = {}
    arms = [('relay_s{s}_agefirst', 'relay, age-first'), ('relay_s{s}_hub', 'relay, hub head'), ('relay_s{s}_prefix', 'relay, congestion'), ('FO_s{s}_prefix', 'FO (no relay)')]
    x = np.arange(len(arms))
    for k, (s, col) in enumerate(((0, C0), (1, C1))):
        Z = rows(Cd / f'distill_none_s{s}/rows.json', 'none'); ys, lo, hi = [], [], []
        for a, _ in arms:
            v = paired(rows(E / a.format(s=s) / 'rows.json', 'prefix'), Z); ys.append(v[0]); lo.append(v[0] - v[1]); hi.append(v[2] - v[0])
            D[f's{s}_{a.format(s=s)}'] = v
        ax.bar(x + (k - 0.5) * 0.38, ys, 0.38, yerr=[lo, hi], color=col, capsize=1.5, label=f'seed {s}', error_kw=dict(lw=0.7))
    ax.axhline(0, color='k', lw=0.6); ax.set_xticks(x); ax.set_xticklabels([l for _, l in arms], fontsize=6, rotation=15)
    ax.set_ylabel('waiting vs zero-byte student (%)'); ax.set_title('rich7: one receiver K = 7, the rest K = 1'); ax.legend(frameon=False, fontsize=6)
    fig.tight_layout(); fig.savefig(OUT / 'fig_rich.pdf'); plt.close(fig); DATA['fig_rich'] = D


if __name__ == '__main__':
    for f in (fig_prereg, fig_va, fig_vs, fig_vf, fig_vu, fig_math, fig_seeds, fig_rich):
        f(); print('made', f.__name__, flush=True)
    (OUT / 'figures_data.json').write_text(json.dumps(DATA, indent=1, default=str))
