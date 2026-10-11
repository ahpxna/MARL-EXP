#!/usr/bin/env python3
"""Figure 2 of paper_two_population (M3 deliverable): the light-cost / fleet-benefit frontier of light-side certainty mechanisms.
Panel A (computed here from raw rows, crossed bootstrap R.crossed, 2 000 draws).  v2 (04/10 22:3x, after the user's review): both
components on the SAME denominator R in every cell, so they add exactly to the endpoint:
  x = 100 (S - R) / R   light-mechanism cost (shadow rows S: the mechanism runs, the fleet drives as σ*)
  y = 100 (A - S) / R   closed-loop contribution of activating the fleet under that mechanism (NOT an isolated message effect)
  net = 100 (A - R) / R = x + y, the registered M3-1 endpoint; the line y = -x is net = 0 for the means as well.
(v1 used 100 (A/S - 1) for y, which adds to the endpoint only to first order: WC5 +3.11 vs +2.98.)
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
        y = np.array([[[100 * (N[f'{arm}_t{l}_{f}'][s]['fuel_agent'] - N[sh(l, f)][s]['fuel_agent']) / N[f'R_t{l}'][s]['fuel_agent'] for s in S] for f in FL] for l in LT])
        pts.append((nm, est(x), est(y), est(x + y)))
    A, B = rows(CS / 'm4_20261004/spider/s4/eval'), rows(CS / 'm4_20261004/spider/s3/eval'); S = range(1000, 1020)
    x = np.array([[pct(A[f'WCK5sh_RLK{k}'], B[f'F0_RLK{k}_labelled'], s) for s in S] for k in (11, 111)])
    y = np.array([[100 * (A[f'WCK5_RLK{k}'][s]['fuel_agent'] - A[f'WCK5sh_RLK{k}'][s]['fuel_agent']) / B[f'F0_RLK{k}_labelled'][s]['fuel_agent'] for s in S] for k in (11, 111)])
    pts.append(('WCK5 (spider, rule fleet)', est(x), est(y), est(x + y)))
    F = rows(CS / 'f1a1_20261004/eval'); S = range(530, 550)
    y = np.array([[[pct(F[f'F1s_s{f}_on_t{l}'], F[f'R_t{l}'], s) for s in S] for f in (213, 313, 413, 513)] for l in LT])
    pts.append(('F1-scratch retrained fleet (more rights)\nfuel improves; agent-TL NI not established\n(upper +0.55 > +0.50)', ((0.0, np.array([0.0, 0.0]))), est(y), est(y)))
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
    A, Bp = panel_a(), panel_b(); fig, ax = plt.subplots(1, 2, figsize=(12.5, 4.6))
    a = ax[0]; lim = 12
    a.fill_between([-1, lim], [1, -lim], [-lim, -lim], color='tab:green', alpha=0.06, label='agent fuel lower than R (fuel only; not the deployment gate)')
    a.plot([-1, lim], [1, -lim], 'k--', lw=0.8, label='net fuel change = 0')
    for (nm, (xp, xci), (yp, yci), (np_, nci)), c in zip(A, ('tab:blue', 'tab:red', 'tab:purple', 'tab:gray')):
        a.errorbar(xp, yp, xerr=[[xp - xci[0]], [xci[1] - xp]], yerr=[[yp - yci[0]], [yci[1] - yp]], fmt='o' if 'F1' not in nm else 'D', color=c, capsize=3,
                   mfc='white' if 'F1' in nm else c)
        a.annotate(f'{nm}\nnet {np_:+.2f} % [{nci[0]:+.2f}, {nci[1]:+.2f}]', (xp, yp), textcoords='offset points', xytext=(6, -62) if 'F1' in nm else (6, 4), fontsize=7,
                   arrowprops=dict(arrowstyle='-', lw=0.5, color='0.5') if 'F1' in nm else None)
    a.set_xlim(-1, lim); a.set_ylim(-5, 2); a.axhline(0, color='0.7', lw=0.6); a.axvline(0, color='0.7', lw=0.6)
    a.set_xlabel('light-mechanism cost: agent fuel change, % of R (shadow - R)'); a.set_ylabel('fleet contribution to fuel change, % of R (fleet - shadow)')
    a.set_title('A. Cost-contribution comparison (panels differ: see caption)', fontsize=9); a.legend(fontsize=7, loc='lower right')
    b = ax[1]; mk = {'E family': 'o', 'fixed-W commitment': 's', 'receiver-triggered commitment': '^'}
    codes = []
    for fam in mk:
        P = [p for p in Bp if p[3] == fam]; b.scatter([p[1] for p in P], [p[2] for p in P], marker=mk[fam], label=fam, s=28)
        for p in P:
            codes.append(p[0]); b.annotate(str(len(codes)), (p[1], p[2]), textcoords='offset points', xytext=(3, 3) if len(codes) % 2 else (3, -9), fontsize=6.5)
    b.text(1.02, 0.0, '\n'.join(f'{i + 1} {c}' for i, c in enumerate(codes)), transform=b.transAxes, fontsize=6, va='bottom')
    b.axhline(0, color='0.7', lw=0.6); b.set_xlabel('light-mechanism cost: city time loss, s/veh (shadow - R)'); b.set_ylabel('fleet contribution, agent fuel % (DEV report units)')
    b.set_title('B. DEV screens (descriptive; grid4 light seeds 0, 1)', fontsize=9); b.legend(fontsize=7)
    fig.tight_layout(); OUT.mkdir(parents=True, exist_ok=True)
    for ext in ('pdf', 'png'):
        fig.savefig(OUT / f'fig2_m3_frontier.{ext}', dpi=160)
    for nm, (xp, xci), (yp, yci), (np_, nci) in A:
        print(f'A {nm!r}: light cost {xp:+.2f} [{xci[0]:+.2f}, {xci[1]:+.2f}], fleet contribution {yp:+.2f} [{yci[0]:+.2f}, {yci[1]:+.2f}], net {np_:+.2f} [{nci[0]:+.2f}, {nci[1]:+.2f}] (x+y {xp + yp:+.2f})')
    print('B points', len(Bp), [p[0] for p in Bp])
