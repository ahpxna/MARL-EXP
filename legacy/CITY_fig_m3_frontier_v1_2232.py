#!/usr/bin/env python3
"""Figure 2 of paper_two_population (M3 deliverable): the light-cost / fleet-benefit frontier of light-side certainty mechanisms.
Panel A (confirmatory panels, computed here from raw rows, crossed bootstrap R.crossed, 2 000 draws): x = clean light cost = agent fuel %
of the shadow rows (light mechanism, fleet driving as σ*) vs R; y = clean fleet contribution = agent fuel % of fleet rows vs shadow rows.
Net effect on the frozen fleet = x + y (to first order); the line y = -x is break-even, below it the fleet would gain.
  grid4 M3-NC (C-86): WC5, RPC-receiver over 5 lights x 4 fleets x 510-529; spider 4a (C-82): WCK5 over 2 lights x 1000-1019;
  reference with update rights: F1-scratch (C-85), light unchanged (x = 0), y = F1-scratch vs R.
Panel B (DEV screens, descriptive, parsed from the generated reports): x = clean light cost in city TL (s/veh), y = clean fleet contribution
(agent fuel %): E family (A2 shadow report), W-c 5/10/15 (M3 DEV report; W-c is fleet-blind, so clean by construction), RPC triggers
(M3' DEV report).  B-ETA is omitted (its decomposition is joint, C-69)."""
import re, sys
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt  # noqa: E402
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402
from scripts.CITY_spatp_report import rows  # noqa: E402
CS = ROOT / 'research/city_sim'; OUT = ROOT / 'research/papers/_tex/figs_two_pop'


def pct(A, B, s, k='fuel_agent'):
    return 100 * (A[s][k] / B[s][k] - 1)


def est(c):
    dr = R.draws(c.shape); p, ci, _ = R.crossed(c, dr); return p, ci


def panel_a():
    pts = []
    N = rows(CS / 'm3nc_20261004/eval'); S = range(510, 530); LT, FL = (4, 5, 6, 7, 8), (213, 313, 413, 513)
    for nm, arm, sh in (('WC5 (grid4)', 'WC5', lambda l, f: f'WC5sig_t{l}'), ('RPC (grid4)', 'RPC', lambda l, f: f'RPCsh_t{l}_{f}')):
        x = np.array([[[pct(N[sh(l, f)], N[f'R_t{l}'], s) for s in S] for f in FL] for l in LT])
        y = np.array([[[pct(N[f'{arm}_t{l}_{f}'], N[sh(l, f)], s) for s in S] for f in FL] for l in LT]); pts.append((nm, est(x), est(y)))
    A, B = rows(CS / 'm4_20261004/spider/s4/eval'), rows(CS / 'm4_20261004/spider/s3/eval'); S = range(1000, 1020)
    x = np.array([[pct(A[f'WCK5sh_RLK{k}'], B[f'F0_RLK{k}_labelled'], s) for s in S] for k in (11, 111)])
    y = np.array([[pct(A[f'WCK5_RLK{k}'], A[f'WCK5sh_RLK{k}'], s) for s in S] for k in (11, 111)]); pts.append(('WCK5 (spider)', est(x), est(y)))
    F = rows(CS / 'f1a1_20261004/eval'); S = range(530, 550)
    y = np.array([[[pct(F[f'F1s_s{f}_on_t{l}'], F[f'R_t{l}'], s) for s in S] for f in (213, 313, 413, 513)] for l in LT])
    pts.append(('F1-scratch retrain\n(reference, more rights)', ((0.0, np.array([0.0, 0.0]))), est(y)))
    return pts


def panel_b():
    pts = []
    for ln in (CS / 'm3_20261004/report_m3_shadow.txt').read_text().splitlines():
        m = re.match(r'\s+(E_\w+)\s+M3-4clean city TL ([+-][\d.]+).*M3-3clean agent fuel % ([+-][\d.]+)', ln)
        if m:
            pts.append((m.group(1).replace('E_', 'E-').replace('_lam', ' λ'), float(m.group(2)), float(m.group(3)), 'E family'))
    for ln in (CS / 'm3_20261004/report_m3_dev.txt').read_text().splitlines():
        m = re.match(r'\s+W-c\s+(WC\d+)\s+.*M3-3 fleet contrib fuel % ([+-][\d.]+) \| M3-4 light cost city TL ([+-][\d.]+)', ln)
        if m:
            pts.append((m.group(1), float(m.group(3)), float(m.group(2)), 'fixed-W commitment'))
    for ln in (CS / 'm3p_20261004/report_m3p_dev.txt').read_text().splitlines():
        m = re.match(r'\s+(RPC-\w+)\s+.*M3-4clean city TL ([+-][\d.]+).*M3-3clean fleet fuel % ([+-][\d.]+)', ln)
        if m:
            pts.append((m.group(1), float(m.group(2)), float(m.group(3)), 'receiver-triggered commitment'))
    return pts


if __name__ == '__main__':
    A, Bp = panel_a(), panel_b(); fig, ax = plt.subplots(1, 2, figsize=(11, 4.4))
    a = ax[0]; lim = 12
    a.fill_between([-1, lim], [1, -lim], [-lim, -lim], color='tab:green', alpha=0.08, label="net gain for the fleet's agents")
    a.plot([-1, lim], [1, -lim], 'k--', lw=0.8, label='break-even (net = 0)')
    for (nm, (xp, xci), (yp, yci)), c in zip(A, ('tab:blue', 'tab:red', 'tab:purple', 'tab:gray')):
        a.errorbar(xp, yp, xerr=[[xp - xci[0]], [xci[1] - xp]], yerr=[[yp - yci[0]], [yci[1] - yp]], fmt='o', color=c, capsize=3)
        a.annotate(f'{nm}\nnet {xp + yp:+.1f} %', (xp, yp), textcoords='offset points', xytext=(6, 4), fontsize=7.5)
    a.set_xlim(-1, lim); a.set_ylim(-5, 2); a.axhline(0, color='0.7', lw=0.6); a.axvline(0, color='0.7', lw=0.6)
    a.set_xlabel('clean light cost: agent fuel %, shadow vs no-SPaT'); a.set_ylabel('clean fleet benefit: agent fuel %, fleet vs shadow')
    a.set_title('A. Confirmatory panels (fresh traffic, new lights / fleets)', fontsize=9); a.legend(fontsize=7, loc='lower right')
    b = ax[1]; mk = {'E family': 'o', 'fixed-W commitment': 's', 'receiver-triggered commitment': '^'}
    for fam in mk:
        P = [p for p in Bp if p[3] == fam]; b.scatter([p[1] for p in P], [p[2] for p in P], marker=mk[fam], label=fam, s=28)
        for i, p in enumerate(P):
            off = (3, 3) if fam != 'receiver-triggered commitment' else ((-38, 8), (4, -10), (6, 6))[i % 3]
            b.annotate(p[0], (p[1], p[2]), textcoords='offset points', xytext=off, fontsize=6)
    b.axhline(0, color='0.7', lw=0.6); b.set_xlabel('clean light cost: city time loss, s/veh'); b.set_ylabel('clean fleet benefit: agent fuel %')
    b.set_title('B. DEV screens (descriptive; grid4 light seeds 0, 1)', fontsize=9); b.legend(fontsize=7)
    fig.tight_layout(); OUT.mkdir(parents=True, exist_ok=True)
    for ext in ('pdf', 'png'):
        fig.savefig(OUT / f'fig2_m3_frontier.{ext}', dpi=160)
    for nm, (xp, xci), (yp, yci) in A:
        print(f'A {nm!r}: light cost {xp:+.2f} [{xci[0]:+.2f}, {xci[1]:+.2f}], fleet benefit {yp:+.2f} [{yci[0]:+.2f}, {yci[1]:+.2f}], net {xp + yp:+.2f}')
    print('B points', len(Bp), [p[0] for p in Bp])
