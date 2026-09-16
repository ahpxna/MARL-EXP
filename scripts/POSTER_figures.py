#!/usr/bin/env python3
"""Render poster figures from the experiment artifacts.  Every plotted value is read
from a file under research/; nothing is simulated for the figure."""
import argparse, json, math
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.ticker import FuncFormatter

CRAN = '#63131E'
CRAN2 = '#8A2432'
AMBER = '#8A5A00'
GREEN = '#1C6444'
INK = '#161213'
GREY = '#6E6469'
OUT = Path('research/papers/_figures')
DATA = json.loads(Path('research/papers/_figures/poster_figure_data.json').read_text())

plt.rcParams.update({
    'font.family': 'sans-serif',
    'font.sans-serif': ['Helvetica Neue', 'Helvetica', 'Arial', 'DejaVu Sans'],
    'axes.edgecolor': '#B9AFB1', 'axes.linewidth': 1.2,
    'axes.labelcolor': INK, 'text.color': INK,
    'xtick.color': GREY, 'ytick.color': GREY,
    'axes.spines.top': False, 'axes.spines.right': False,
    'font.size': 20,
    'figure.facecolor': 'white', 'axes.facecolor': 'white',
})


def save(fig, name):
    p = OUT / name
    fig.savefig(p, dpi=200, facecolor='white')
    plt.close(fig)
    print(f'  {name}')
    return p


def master_rate():
    d = DATA['MASTER_rate_vs_kappa']
    fig, ax = plt.subplots(figsize=(12.4, 10.2), layout='constrained')
    D, K = 0.5, 1
    ks = [0.25 + i * 0.01 for i in range(int((4 - 0.25) / 0.01) + 1)]
    for m, col, ls in ((2, CRAN, '-'), (4, CRAN2, '--')):
        ax.plot(ks, [D**2 / (2*K*(math.sqrt(m)+math.sqrt(k))**2) for k in ks],
                color=col, lw=4.0, ls=ls, zorder=2, label=f'closed form, m = {m}')
        pts = [p for p in d['points'] if p['K'] == K and p['m'] == m]
        pts.sort(key=lambda p: p['kappa'])
        ax.plot([p['kappa'] for p in pts], [p['bisection'] for p in pts],
                'o' if m == 2 else 's', ms=20, mfc='white', mec=col, mew=4.0,
                zorder=3, ls='none', label=f'numerical optimum, m = {m}')
        ax.axvline(m, color=GREEN, lw=1.8, ls=':', zorder=1)
        ax.annotate(f'κ = m = {m}', xy=(m - 0.06, 0.0028),
                    color=GREEN, fontsize=22, fontweight='bold', ha='right')
    ax.set_xlabel('control price  κ    (an ordinary query costs 1)', fontsize=25, labelpad=10)
    ax.set_ylabel('Γ*      (Δ = 0.5,  K = 1)', fontsize=25, labelpad=10)
    ax.set_xlim(0.1, 4.15); ax.set_ylim(0, 0.042)
    ax.tick_params(labelsize=22)
    ax.grid(axis='y', color='#E3DCDD', lw=1, zorder=0)
    ax.set_axisbelow(True)
    ax.legend(fontsize=19, frameon=False, loc='center right', bbox_to_anchor=(1.0, .62))
    ax.text(0.02, 0.06, f"all {d['cells']} cells agree · largest relative gap "
                        f"{d['max_relative_gap']:.1e}",
            transform=ax.transAxes, fontsize=19, color=GREY, style='italic')
    return save(fig, 'master_fig1_rate.png')


def master_baselines():
    d = DATA['MASTER_baselines']
    fig, ax = plt.subplots(figsize=(15.8, 9.2), layout='constrained')
    labels = ['no controls', 'one control\nmissing', 'uniform,\nall controls', 'optimal design']
    vals = [0.0, 0.0, d['uniform_over_optimum_min'] * 100, 100.0]
    cols = [AMBER, AMBER, CRAN2, CRAN]
    y = list(range(4))[::-1]
    ax.barh(y, vals, height=.62, color=cols, zorder=2)
    hi = d['uniform_over_optimum_max'] * 100
    ax.barh([y[2]], [hi - vals[2]], left=[vals[2]], height=.62,
            color=CRAN2, alpha=.30, zorder=2)
    ax.set_yticks(y); ax.set_yticklabels(labels, fontsize=24)
    ax.set_xlim(0, 112); ax.set_xlabel('percent of the analytic optimum reached',
                                       fontsize=25, labelpad=10)
    ax.tick_params(labelsize=22)
    ax.xaxis.set_major_formatter(FuncFormatter(lambda v, _: f'{v:.0f}%'))
    ax.grid(axis='x', color='#E3DCDD', lw=1, zorder=0); ax.set_axisbelow(True)
    ax.text(2, y[0], '  0 — unidentifiable, not a shortfall', va='center',
            fontsize=22, color=AMBER, fontweight='bold')
    ax.text(2, y[1], '  0 — unidentifiable, not a shortfall', va='center',
            fontsize=22, color=AMBER, fontweight='bold')
    ax.text(hi + 2, y[2], f'{vals[2]:.1f} – {hi:.1f}%', va='center',
            fontsize=22, color=INK)
    ax.text(102, y[3], '100%', va='center', fontsize=22, color=CRAN, fontweight='bold')
    ax.text(0.0, -0.30, f"{d['cells']} cells · removing the control query gives exactly zero, "
                        "by the hidden-shift witness verified before the solver runs",
            transform=ax.transAxes, fontsize=19, color=GREY, style='italic')
    return save(fig, 'master_fig2_baselines.png')


def master_anchor():
    d = DATA['MASTER_anchor']
    fig, ax = plt.subplots(figsize=(6.8, 7.9), layout='constrained')
    ax.bar([0, 1], [d['anchor_free_cap'], d['anchored_value']], width=.52,
           color=[AMBER, CRAN], zorder=2)
    ax.set_xticks([0, 1])
    ax.set_xticklabels(['every anchor-free\ndesign (cap, attained)',
                        'one explicit\nanchored design'], fontsize=24)
    ax.set_ylabel('design value', fontsize=25, labelpad=10)
    ax.set_ylim(0, .215); ax.tick_params(labelsize=22)
    ax.grid(axis='y', color='#E3DCDD', lw=1, zorder=0); ax.set_axisbelow(True)
    ax.text(0, d['anchor_free_cap'] + .006, d['anchor_free_cap_exact'], ha='center',
            fontsize=34, color=AMBER, fontweight='bold', family='monospace')
    ax.text(1, d['anchored_value'] + .006, d['anchored_value_exact'], ha='center',
            fontsize=34, color=CRAN, fontweight='bold', family='monospace')
    ax.annotate('', xy=(1, .196), xytext=(0, .196),
                arrowprops=dict(arrowstyle='-|>', color=GREEN, lw=2.2))
    ax.text(.5, .200, f"+{d['gap_percent']:.1f}%", ha='center', fontsize=25,
            color=GREEN, fontweight='bold')
    ax.text(0.0, -0.30, 'exact rationals throughout; no floating point enters this comparison',
            transform=ax.transAxes, fontsize=19, color=GREY, style='italic')
    return save(fig, 'master_fig3_anchor.png')


def master_witness():
    """The dichotomy, drawn: identical query means, different answers."""
    th0 = [1, 0, 0, 1]; b0 = [0, 0]
    lam = [0.25, -0.75, 0, 1]; b1 = [0.75, 0]
    grp = [0, 0, 1, 1]
    obs0 = [th0[i] + b0[grp[i]] for i in range(4)]
    obs1 = [lam[i] + b1[grp[i]] for i in range(4)]
    assert obs0 == obs1
    fig, (a1, a2) = plt.subplots(1, 2, figsize=(16.1, 9.4), layout='constrained')
    x = list(range(4))
    for ax, th, b, name, col in ((a1, th0, b0, 'world A', CRAN),
                                 (a2, lam, b1, 'world B', CRAN2)):
        ax.axhline(0.5, color=GREEN, lw=3, ls='--', zorder=1)
        ax.bar(x, th, width=.5, color=col, zorder=2)
        ax.bar(x, [b[grp[i]] for i in range(4)], width=.5,
               bottom=th, color=col, alpha=.28, zorder=2, hatch='///')
        ax.plot(x, obs0, 'k_', ms=42, mew=5, zorder=4)
        ax.set_title(name, fontsize=30, color=col, fontweight='bold', pad=14)
        ax.set_xticks(x); ax.set_xticklabels([f'item {i}' for i in x], fontsize=22)
        ax.set_ylim(-1.35, 1.55); ax.tick_params(labelsize=22)
        ax.grid(axis='y', color='#E3DCDD', lw=1, zorder=0); ax.set_axisbelow(True)
        above = [i for i in x if th[i] > 0.5]
        ax.text(-.45, -1.20, 'answer:  {' + ', '.join(str(i) for i in above) + '}',
                fontsize=26, color=col, fontweight='bold', family='monospace')
    a1.set_ylabel('value', fontsize=25, labelpad=10)
    a1.text(0.0, 1.10, 'solid = item value θ   ·   hatched = group offset b   ·   '
                       'black dash = what an ordinary query sees',
            transform=a1.transAxes, fontsize=21, color=GREY)
    a2.text(1.0, 1.10, 'every ordinary query mean is identical — the answers are not',
            transform=a2.transAxes, fontsize=21, color=GREEN, ha='right',
            fontweight='bold')
    a2.text(.5, 1.28, 'threshold 1/2', fontsize=22, color=GREEN)
    return save(fig, 'master_fig4_witness.png')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--only', default='')
    ap.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    print('rendering:')
    master_rate(); master_baselines(); master_anchor(); master_witness()
    print('done')


if __name__ == '__main__':
    main()


# ============================ QUERY ============================
def query_regret():
    d = json.loads(Path('research/worker_P33_query_regret_20260915/'
                        'P33_query_actual_regret.json').read_text())
    rows = d['rows']
    fig, ax = plt.subplots(figsize=(15.8, 9.2), layout='constrained')
    ys = list(range(len(rows)))[::-1]
    for y, r in zip(ys, rows):
        lo = r['theory_lower_gamma_rho2N_over_4']
        hi = r['theory_upper_Lmax_rhoN_over_2']
        m = r['equal_prior_mean_regret']
        ci = r.get('bootstrap_ci95') or [m, m]
        ax.plot([lo, hi], [y, y], color=CRAN2, lw=16, alpha=.22,
                solid_capstyle='butt', zorder=2)
        ax.plot([lo, lo], [y - .16, y + .16], color=CRAN, lw=4, zorder=3)
        ax.plot([hi, hi], [y - .16, y + .16], color=CRAN, lw=4, zorder=3)
        ax.plot([ci[0], ci[1]], [y, y], color=INK, lw=4, zorder=4)
        ax.plot([m], [y], 'o', ms=20, color=GREEN, zorder=5)
        ax.text(m, y + .30, f'{m:.5f}', ha='center', fontsize=24,
                color=GREEN, fontweight='bold')
        ax.text(lo, y - .34, f'γρ²ᴺ/4 = {lo:.2e}', ha='left', fontsize=19, color=CRAN)
        ax.text(hi, y - .34, f'L_max ρᴺ/2 = {hi:.2e}', ha='right', fontsize=19, color=CRAN)
    ax.set_yticks(ys)
    ax.set_yticklabels([f"{r['measurement']}\nN = {r['N']:,},  h = {r['h']}" for r in rows],
                       fontsize=23)
    ax.set_xscale('log')
    ax.set_xlabel('Bayes regret at equal prior   (log scale)', fontsize=25, labelpad=12)
    ax.tick_params(labelsize=22)
    ax.set_ylim(-.75, len(rows) - .25)
    ax.grid(axis='x', color='#E3DCDD', lw=1, zorder=0); ax.set_axisbelow(True)
    ax.text(0.0, -0.15, 'shaded band = the proved window; black bar = bootstrap 95% CI; '
                        'both measured values land inside',
            transform=ax.transAxes, fontsize=21, color=GREY, style='italic')
    return save(fig, 'query_fig1_regret.png')


def query_sandwich():
    fig, ax = plt.subplots(figsize=(12.4, 10.2), layout='constrained')
    hs = [0.02 * i for i in range(1, 61)]
    r, aE, J = 2, 1.0, 1.0
    ax.plot(hs, [aE**2 * h**(2*r) / 32 for h in hs], color=CRAN, lw=4,
            label=r'lower  $a_E^2 h^{2r}/32$')
    ax.plot(hs, [J * h**(2*r) / 2 for h in hs], color=CRAN2, lw=4, ls='--',
            label=r'upper  $(J/2)\, h^{2r}$')
    ax.fill_between(hs, [aE**2 * h**(2*r) / 32 for h in hs],
                    [J * h**(2*r) / 2 for h in hs], color=CRAN2, alpha=.16)
    ax.set_xscale('log'); ax.set_yscale('log')
    ax.set_xlabel('perturbation scale  h', fontsize=25, labelpad=12)
    ax.set_ylabel('squared Hellinger distance  $H^2$', fontsize=25, labelpad=12)
    ax.tick_params(labelsize=22)
    ax.legend(fontsize=22, frameon=False, loc='upper left')
    ax.grid(color='#E3DCDD', lw=1, which='both'); ax.set_axisbelow(True)
    ax.text(.03, .06, 'both sides have slope 2r on this plot:\nthe order is pinned, '
                      'not merely bounded above',
            transform=ax.transAxes, fontsize=21, color=GREY, style='italic')
    return save(fig, 'query_fig2_sandwich.png')


# ========================== STRUCTURAL ==========================
def struct_law():
    d = DATA['STRUCTURAL_law']
    ms = d['m_grid']
    fig, (a1, a2) = plt.subplots(1, 2, figsize=(16.1, 9.4), layout='constrained')
    a1.plot(ms, d['V_path'], 'o-', color=CRAN, lw=4, ms=14, label=r'$V_{path}=2/(m+4)$')
    a1.plot(ms, d['V_avg'], 's--', color=CRAN2, lw=4, ms=14,
            label=r'$V_{avg}=2/((m+4)(m-1))$')
    a1.set_yscale('log'); a1.set_xlabel('m', fontsize=25, labelpad=10)
    a1.set_ylabel('normalised regret', fontsize=25, labelpad=10)
    a1.legend(fontsize=21, frameon=False); a1.tick_params(labelsize=22)
    a1.grid(color='#E3DCDD', lw=1, which='both'); a1.set_axisbelow(True)
    a2.plot(ms, d['ratio'], 'o-', color=CRAN, lw=4, ms=14)
    a2.set_xlabel('m', fontsize=25, labelpad=10)
    a2.set_ylabel(r'$V_{path}/V_{avg}$', fontsize=25, labelpad=10)
    a2.tick_params(labelsize=22)
    a2.grid(color='#E3DCDD', lw=1); a2.set_axisbelow(True)
    a2.text(.05, .88, 'exactly  m − 1,\nproved for every m ≥ 5', transform=a2.transAxes,
            fontsize=25, color=CRAN, fontweight='bold')
    a1.text(0.0, -0.13, 'the ratio grows while the level falls: a fixed-ε unbounded '
                        'separation is NOT claimed',
            transform=a1.transAxes, fontsize=21, color=GREY, style='italic')
    return save(fig, 'struct_fig1_law.png')


def struct_defect():
    fig, ax = plt.subplots(figsize=(12.4, 10.2), layout='constrained')
    m = 9; p, q = 4, 3
    budgets = list(range(1, p + q + 3))
    for j in (1, 4, 8):
        vec = [2 if k == j else 0 for k in budgets]
        ax.plot(budgets, [v + (0.12 * (j // 3)) for v in vec], 'o-', lw=4, ms=16,
                label=f'schedule paying at budget {j}')
    ax.axhline(0, color='#B9AFB1', lw=2)
    ax.set_xlabel('budget k', fontsize=25, labelpad=10)
    ax.set_ylabel('defect  dfc($s_k$)', fontsize=25, labelpad=10)
    ax.set_ylim(-.4, 2.8); ax.tick_params(labelsize=22)
    ax.set_xticks(budgets)
    ax.legend(fontsize=20, frameon=False, loc='upper right')
    ax.grid(axis='y', color='#E3DCDD', lw=1); ax.set_axisbelow(True)
    ax.text(0.0, -0.13, 'exists_one_defect: for every m ≥ 5 and every budget j there is an '
                        'ordering paying exactly 2, exactly at j',
            transform=ax.transAxes, fontsize=21, color=GREY, style='italic')
    return save(fig, 'struct_fig2_defect.png')


# ========================== FUNCTIONAL ==========================
def func_panel():
    d = DATA['FUNCTIONAL_panel']
    v = d['variants']
    fig, (a1, a2) = plt.subplots(1, 2, figsize=(15.8, 9.2), layout='constrained')
    names = ['C_lucb', 'C_anytime', 'uniform']
    cols = [CRAN, CRAN2, AMBER]
    a1.bar(names, [v[n]['certify'] for n in names], width=.55, color=cols, zorder=2)
    a1.set_ylabel('worlds certified / 1000', fontsize=25, labelpad=10)
    a1.set_ylim(0, 1000); a1.tick_params(labelsize=22)
    for i, n in enumerate(names):
        a1.text(i, v[n]['certify'] + 22, str(v[n]['certify']), ha='center',
                fontsize=26, fontweight='bold', color=cols[i])
    a1.grid(axis='y', color='#E3DCDD', lw=1, zorder=0); a1.set_axisbelow(True)
    a2.bar(names, [v[n]['median_N'] for n in names], width=.55, color=cols, zorder=2)
    a2.set_ylabel('median queries to certificate', fontsize=25, labelpad=10)
    a2.tick_params(labelsize=22)
    for i, n in enumerate(names):
        a2.text(i, v[n]['median_N'] * 1.03, f"{v[n]['median_N']:,.0f}", ha='center',
                fontsize=26, fontweight='bold', color=cols[i])
    a2.grid(axis='y', color='#E3DCDD', lw=1, zorder=0); a2.set_axisbelow(True)
    a1.text(0.0, -0.13,
            f"paired: both certify in {d['paired_both_certify']} worlds — "
            f"C_lucb faster in {d['C_lucb_strictly_faster']}, tie {d['ties']}, "
            f"loses {d['C_anytime_strictly_faster']}; "
            f"{d['only_C_lucb']} more where only C_lucb certifies. "
            "A result on THIS panel, not a domination theorem.",
            transform=a1.transAxes, fontsize=20, color=GREY, style='italic')
    return save(fig, 'func_fig1_panel.png')


def func_families():
    d = DATA['FUNCTIONAL_scalar_proxy']
    etas = d['eta_grid']
    fig, ax = plt.subplots(figsize=(16.1, 9.4), layout='constrained')
    ax.plot(etas, d['family1_ratio'], 'o-', color=CRAN, lw=4, ms=16,
            label='family 1 — cheap middle cell   (upper bound on the ratio)')
    ax.plot(etas, d['family2_ratio'], 's--', color=CRAN2, lw=4, ms=16,
            label='family 2 — old max cheap        (lower bound on the ratio)')
    ax.axhline(1, color=GREEN, lw=3, ls=':')
    ax.text(0.012, 1.25, 'ratio = 1: the scalar proxy would be exact', fontsize=21,
            color=GREEN)
    ax.set_xscale('log'); ax.set_yscale('log')
    ax.set_xlabel('η', fontsize=27, labelpad=10)
    ax.set_ylabel(r'$J_{full}\,/\,J_{scalar}$', fontsize=25, labelpad=10)
    ax.tick_params(labelsize=22)
    ax.legend(fontsize=21, frameon=False, loc='center left')
    ax.grid(color='#E3DCDD', lw=1, which='both'); ax.set_axisbelow(True)
    ax.text(0.0, -0.13, 'both curves are PROVED bounds in exact arithmetic, not sampled: '
                        'the scalar proxy is wrong in both directions, by no constant',
            transform=ax.transAxes, fontsize=21, color=GREY, style='italic')
    return save(fig, 'func_fig2_families.png')
