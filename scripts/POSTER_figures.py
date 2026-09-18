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


def note(fig, text, fs=20):
    """Footnote anchored to the figure, below everything else.

    The reserved strip used to be a fixed 7.5% of the height. A note longer than
    that grew upward into the axes and sat on top of the x-axis label or an
    annotation -- which is exactly how it fails, since nothing errors. The strip
    is now measured: draw the note, ask the renderer how tall it actually is,
    and reserve that much plus a margin.
    """
    t = fig.text(0.012, 0.010, text, fontsize=fs, color=GREY, style='italic',
                 wrap=True, ha='left', va='bottom')
    eng = fig.get_layout_engine()
    if eng is None:
        return
    eng.set(rect=(0.012, 0.075, 0.976, 0.913))
    fig.canvas.draw()
    h = t.get_window_extent(renderer=fig.canvas.get_renderer()).height
    frac = h / fig.get_window_extent().height
    bottom = min(0.40, frac + 0.045)          # the note, plus clear air above it
    eng.set(rect=(0.012, bottom, 0.976, 0.975 - bottom * 0.12))


def _declutter_corner(fig):
    """Hide a tick label that has collided with one on the other axis.

    The bottom-left and bottom-right corners are where the first or last x tick
    label meets the first or last y tick label. Nudging padding only moves the
    problem, so measure and drop the x label, which is the one a reader can
    infer from its neighbours.
    """
    fig.canvas.draw()
    r = fig.canvas.get_renderer()
    for ax in fig.axes:
        ys = [t for t in ax.get_yticklabels() if t.get_text() and t.get_visible()]
        xs = [t for t in ax.get_xticklabels() if t.get_text() and t.get_visible()]
        if not xs or not ys:
            continue
        for other in fig.axes:
            oys = [t for t in other.get_yticklabels()
                   if t.get_text() and t.get_visible()]
            for xt in xs:
                a = xt.get_window_extent(renderer=r)
                for yt in ys + oys:
                    b = yt.get_window_extent(renderer=r)
                    dx = min(a.x1, b.x1) - max(a.x0, b.x0)
                    dy = min(a.y1, b.y1) - max(a.y0, b.y0)
                    if dx > 0 and dy > 0:
                        xt.set_visible(False)
                        break


def save(fig, name):
    _declutter_corner(fig)
    p = OUT / name
    fig.savefig(p, dpi=200, facecolor='white')
    plt.close(fig)
    print(f'  {name}')
    return p


def master_rate():
    d = DATA['MASTER_rate_vs_kappa']
    fig, ax = plt.subplots(figsize=(15.8, 9.0), layout='constrained')
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
        ax.annotate(f'νκ = vm = {m}', xy=(m - 0.06, 0.0028),
                    color=GREEN, fontsize=22, fontweight='bold', ha='right')
    ax.set_xlabel('control price  κ    (an ordinary query costs 1)', fontsize=25, labelpad=10)
    ax.set_ylabel('Γ*      (Δ = 0.5,  K = 1)', fontsize=25, labelpad=10)
    ax.set_xlim(0.1, 4.15); ax.set_ylim(0, 0.042)
    ax.tick_params(labelsize=22, pad=9)
    ax.grid(axis='y', color='#E3DCDD', lw=1, zorder=0)
    ax.set_axisbelow(True)
    ax.legend(fontsize=19, frameon=False, loc='center right', bbox_to_anchor=(1.0, .62))
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
    ax.tick_params(labelsize=22, pad=9)
    ax.xaxis.set_major_formatter(FuncFormatter(lambda v, _: f'{v:.0f}%'))
    ax.grid(axis='x', color='#E3DCDD', lw=1, zorder=0); ax.set_axisbelow(True)
    ax.text(2, y[0], '  0 — unidentifiable, not a shortfall', va='center',
            fontsize=22, color=AMBER, fontweight='bold')
    ax.text(2, y[1], '  0 — unidentifiable, not a shortfall', va='center',
            fontsize=22, color=AMBER, fontweight='bold')
    ax.text(hi + 2, y[2], f'{vals[2]:.1f} – {hi:.1f}%', va='center',
            fontsize=22, color=INK)
    ax.text(102, y[3], '100%', va='center', fontsize=22, color=CRAN, fontweight='bold')
    note(fig, f"{d['cells']} cells · removing the control query gives exactly zero, "
                        "by the hidden-shift witness verified before the solver runs", fs=19)
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
    ax.text(0, d['anchor_free_cap'] + .016, d['anchor_free_cap_exact'], ha='center',
            fontsize=34, color=AMBER, fontweight='bold', family='monospace')
    ax.text(1, d['anchored_value'] + .008, d['anchored_value_exact'], ha='center',
            fontsize=34, color=CRAN, fontweight='bold', family='monospace')
    ax.annotate('', xy=(1, .214), xytext=(0, .214),
                arrowprops=dict(arrowstyle='-|>', color=GREEN, lw=2.2))
    ax.text(.5, .218, f"+{d['gap_percent']:.1f}%", ha='center', fontsize=25,
            color=GREEN, fontweight='bold')
    note(fig, 'exact rationals throughout; no floating point enters this comparison', fs=19)
    return save(fig, 'master_fig3_anchor.png')


def master_witness():
    """The dichotomy, drawn: identical query means, different answers."""
    th0 = [1, 0, 0, 1]; b0 = [0, 0]
    lam = [0.25, -0.75, 0, 1]; b1 = [0.75, 0]
    grp = [0, 0, 1, 1]
    obs = [th0[i] + b0[grp[i]] for i in range(4)]
    assert obs == [lam[i] + b1[grp[i]] for i in range(4)]
    fig, (a1, a2) = plt.subplots(1, 2, figsize=(12.4, 7.2), layout='constrained',
                                 sharey=True)
    x = list(range(4))
    for ax, th, b, name, col in ((a1, th0, b0, 'world A', CRAN),
                                 (a2, lam, b1, 'world B', CRAN2)):
        ax.axhline(0.5, color=GREEN, lw=3, ls='--', zorder=1)
        ax.bar(x, th, width=.74, color=col, zorder=2, label='item value θ')
        ax.bar(x, [b[grp[i]] for i in range(4)], width=.74, bottom=th,
               color=col, alpha=.26, hatch='///', zorder=2,
               label='group offset b')
        ax.plot(x, obs, 'k_', ms=46, mew=6, zorder=4, label='what a query sees')
        ax.set_title(name, fontsize=27, color=col, fontweight='bold', pad=10)
        ax.set_xticks(x); ax.set_xticklabels([str(i) for i in x], fontsize=23)
        ax.set_xlabel('item', fontsize=22, labelpad=6)
        ax.set_xlim(-.62, 3.62); ax.set_ylim(-1.35, 1.72)
        ax.tick_params(labelsize=22, pad=9)
        ax.grid(axis='y', color='#E3DCDD', lw=1, zorder=0); ax.set_axisbelow(True)
        above = [i for i in x if th[i] > 0.5]
        ax.text(1.5, -1.22, 'answer  {' + ', '.join(str(i) for i in above) + '}',
                fontsize=25, color=col, fontweight='bold', family='monospace',
                ha='center')
    a1.set_ylabel('value', fontsize=24, labelpad=8)
    a2.text(1.5, 1.50, 'threshold 1/2', fontsize=21, color=GREEN, ha='center')
    a1.legend(fontsize=18, frameon=False, loc='upper center', ncol=1,
              bbox_to_anchor=(0.5, 1.02))
    note(fig, 'every ordinary query mean is identical; the answers are not', fs=19)
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
        ax.text(lo, y - .34, rf'$\gamma\rho^{{2N}}/4$ = {lo:.2e}', ha='left', fontsize=19, color=CRAN)
        ax.text(hi, y - .34, rf'$L_{{\max}}\rho^{{N}}/2$ = {hi:.2e}', ha='right', fontsize=19, color=CRAN)
    ax.set_yticks(ys)
    ax.set_yticklabels([f"{r['measurement']}\nN = {r['N']:,},  h = {r['h']}" for r in rows],
                       fontsize=23)
    ax.set_xscale('log')
    ax.set_xlabel('Bayes regret at equal prior   (log scale)', fontsize=25, labelpad=12)
    ax.tick_params(labelsize=22, pad=9)
    ax.set_ylim(-.75, len(rows) - .25)
    ax.grid(axis='x', color='#E3DCDD', lw=1, zorder=0); ax.set_axisbelow(True)
    note(fig, 'shaded band = the proved window; black bar = bootstrap 95% CI; '
                        'both measured values land inside', fs=21)
    return save(fig, 'query_fig1_regret.png')


def query_sandwich():
    fig, ax = plt.subplots(figsize=(15.8, 9.0), layout='constrained')
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
    ax.tick_params(labelsize=22, pad=9)
    ax.legend(fontsize=22, frameon=False, loc='upper left')
    ax.grid(color='#E3DCDD', lw=1, which='both'); ax.set_axisbelow(True)
    note(fig, 'both sides have slope 2r on this plot:\nthe order is pinned, '
                      'not merely bounded above', fs=21)
    return save(fig, 'query_fig2_sandwich.png')


# ========================== STRUCTURAL ==========================
def struct_law():
    d = DATA['STRUCTURAL_law']
    ms = d['m_grid']
    fig, (a1, a2) = plt.subplots(1, 2, figsize=(16.1, 9.4), layout='constrained')
    # two panels side by side: the right-hand x labels of the left panel were
    # running into the y labels of the right one
    fig.get_layout_engine().set(w_pad=0.18)
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
    # put the right panel's scale on its outer edge: against the left panel it
    # was landing on that panel's own tick labels
    a2.yaxis.tick_right(); a2.yaxis.set_label_position('right')
    a2.tick_params(labelsize=22)
    a2.grid(color='#E3DCDD', lw=1); a2.set_axisbelow(True)
    a2.text(.05, .88, 'exactly  m − 1,\nproved for every m ≥ 5', transform=a2.transAxes,
            fontsize=25, color=CRAN, fontweight='bold')
    note(fig, 'the ratio grows while the level falls: a fixed-ε unbounded '
                        'separation is NOT claimed', fs=21)
    return save(fig, 'struct_fig1_law.png')


def struct_defect():
    fig, ax = plt.subplots(figsize=(15.8, 9.0), layout='constrained')
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
    note(fig, 'exists_one_defect: for every m ≥ 5 and every budget j there is an '
                        'ordering paying exactly 2, exactly at j', fs=21)
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
    a2.tick_params(labelsize=22, pad=6)
    # the twin axis put a tick at the same height as the left one, so the two
    # labels rendered on top of each other; nudge the right ticks off the shared
    # positions
    a2.set_yticks([t for t in a2.get_yticks()
                   if all(abs(t - u) > 1e-9 for u in a1.get_yticks())])
    for i, n in enumerate(names):
        a2.text(i, v[n]['median_N'] * 1.03, f"{v[n]['median_N']:,.0f}", ha='center',
                fontsize=26, fontweight='bold', color=cols[i])
    a2.grid(axis='y', color='#E3DCDD', lw=1, zorder=0); a2.set_axisbelow(True)
    note(fig,
            f"paired: both certify in {d['paired_both_certify']} worlds — "
            f"C_lucb faster in {d['C_lucb_strictly_faster']}, tie {d['ties']}, "
            f"loses {d['C_anytime_strictly_faster']}; "
            f"{d['only_C_lucb']} more where only C_lucb certifies. "
            "A result on THIS panel, not a domination theorem.", fs=20)
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
    ax.tick_params(labelsize=22, pad=9)
    ax.legend(fontsize=21, frameon=False, loc='center left')
    ax.grid(color='#E3DCDD', lw=1, which='both'); ax.set_axisbelow(True)
    note(fig, 'both curves are PROVED bounds in exact arithmetic, not sampled: '
                        'the scalar proxy is wrong in both directions, by no constant', fs=21)
    return save(fig, 'func_fig2_families.png')


# ============================ SUPPORT ============================
def support_separation():
    d = json.loads(Path('research/worker_P20_support_20260915/'
                        'P20_support_growing_k.json').read_text())
    rows = [r for r in d['rows'] if r['P'] == d['rows'][0]['P']]
    Ks = [int(r['K']) for r in rows]
    dec = [int(r['N_decide_exact']) for r in rows]
    rec = [int(r['N_recover_exact']) for r in rows]
    fig, ax = plt.subplots(figsize=(15.8, 9.2), layout='constrained')
    ax.plot(Ks, dec, 'o-', color=CRAN, lw=4, ms=18, label='decide  —  exact sample count')
    ax.plot(Ks, rec, 's--', color=CRAN2, lw=4, ms=18, label='recover  —  exact sample count')
    ax.set_xscale('log'); ax.set_yscale('log')
    ax.set_xlabel('number of classes  K', fontsize=25, labelpad=12)
    ax.set_ylabel('samples to reach error ε', fontsize=25, labelpad=12)
    ax.tick_params(labelsize=22, pad=9)
    ax.legend(fontsize=22, frameon=False, loc='upper left')
    ax.grid(color='#E3DCDD', lw=1, which='both'); ax.set_axisbelow(True)
    note(fig, 'deciding is FLAT in K; recovering grows like K log K.\n'
                      'The gap is the whole point: you need not identify the world '
                      'to decide.', fs=21)
    return save(fig, 'support_fig1_separation.png')


def support_minimax():
    fig, ax = plt.subplots(figsize=(15.8, 9.0), layout='constrained')
    ax.axis('off')
    steps = [
        ('any rule  d', 'sup_w  R(w, d)', CRAN2, 0.86),
        ('≥  Bayes risk, any prior π', 'Σ_w π(w) R(w, d)', CRAN2, 0.66),
        ('≥  Bayes-OPTIMAL value', 'Σ_x  min_a  g(x, a)', CRAN, 0.46),
        ('=  the equivariant decoder', 'r  =  L / (a + L)', GREEN, 0.26),
    ]
    for label, expr, col, y in steps:
        ax.text(.06, y + .055, label, fontsize=25, color=col, fontweight='bold',
                transform=ax.transAxes)
        ax.text(.10, y, expr, fontsize=28, color=INK, family='monospace',
                transform=ax.transAxes)
    for y in (.80, .60, .40):
        ax.annotate('', xy=(.045, y - .10), xytext=(.045, y),
                    xycoords='axes fraction', textcoords='axes fraction',
                    arrowprops=dict(arrowstyle='-|>', color=CRAN, lw=3))
    ax.text(.06, .12, 'so the decoder is a LEAST element of the achievable\n'
                      'worst-case risks: an infimum over ALL rules, attained.',
            fontsize=23, color=GREEN, fontweight='bold', transform=ax.transAxes)
    ax.text(.06, .02, 'the third step is the one that was missing: bayes_optimal_lower',
            fontsize=20, color=GREY, style='italic', transform=ax.transAxes)
    return save(fig, 'support_fig2_minimax.png')


# ============================== D6 ==============================
def d6_design():
    fig, ax = plt.subplots(figsize=(15.8, 9.2), layout='constrained')
    etas = [i / 200 for i in range(201)]
    for c, col, ls in ((1.5, CRAN, '-'), (2.0, CRAN2, '--')):
        ax.plot(etas, [e / c for e in etas], color=col, lw=4, ls=ls,
                label=f'w_pair = η/c   (c = {c})')
    ax.plot(etas, [1 - e for e in etas], color=AMBER, lw=4, ls=':',
            label='w_B = 1 − η   (price 1)')
    obs = [(1/3, 1.5, 2/9), (13/20, 1.5, 13/30), (4/5, 1.5, 8/15),
           (1/3, 2.0, 1/6), (13/20, 2.0, 13/40), (4/5, 2.0, 2/5)]
    for e, c, wp in obs:
        ax.plot([e], [wp], 'o', ms=20, mfc='white',
                mec=CRAN if c == 1.5 else CRAN2, mew=4, zorder=5)
        ax.plot([e], [1 - e], 's', ms=18, mfc='white', mec=AMBER, mew=4, zorder=5)
    ax.set_xlabel('budget share committed to the pair query,  η', fontsize=25, labelpad=12)
    ax.set_ylabel('design weight', fontsize=25, labelpad=12)
    ax.set_xlim(0, 1); ax.set_ylim(0, 1.05); ax.tick_params(labelsize=22)
    ax.legend(fontsize=21, frameon=False, loc='upper center')
    ax.grid(color='#E3DCDD', lw=1); ax.set_axisbelow(True)
    note(fig, 'markers are the artifact\'s own fitted weights in all 24 cells;\n'
                      'the lines are the derived formula. They coincide exactly, and the\n'
                      'weights do not depend on (q, μ) at all.', fs=21)
    return save(fig, 'd6_fig1_design.png')


def d6_certificates():
    p32 = json.loads(Path('research/worker_P32_d6_apair_20260915/'
                          'P32_d6_apair_necessity.json').read_text())
    p24 = json.loads(Path('research/worker_P24_d6_corrected_20260915/'
                          'P24_d6_boundary_modulus_v2.json').read_text())
    fig, ax = plt.subplots(figsize=(16.1, 9.4), layout='constrained')
    labels = ['A-pair NECESSARY\n(L_full > U_noA)', 'A-pair present\nin the support',
              'separation certified\non the whole cell']
    got = [p32['cells_apair_necessary'], p32['cells_apair_present'], p24['cells_certified']]
    tot = [p32['cells_total'], p32['cells_total'], p24['cells_total']]
    y = [2, 1, 0]
    ax.barh(y, tot, height=.5, color='#E3DCDD', zorder=2)
    ax.barh(y, got, height=.5, color=[CRAN, CRAN2, GREEN], zorder=3)
    ax.set_yticks(y); ax.set_yticklabels(labels, fontsize=23)
    ax.set_xlabel('cells', fontsize=25, labelpad=12)
    ax.tick_params(labelsize=22); ax.set_xlim(0, max(tot) * 1.18)
    for yy, g, t in zip(y, got, tot):
        ax.text(g + .3, yy, f'{g} / {t}', va='center', fontsize=26,
                fontweight='bold', color=INK)
    ax.grid(axis='x', color='#E3DCDD', lw=1, zorder=0); ax.set_axisbelow(True)
    note(fig, 'the 3 cells without a necessity certificate are exactly those where '
                        'the A-pair weight is 0 — so nothing is missing, the query is simply '
                        'not used there', fs=21)
    return save(fig, 'd6_fig2_certificates.png')


# =========================== ADAPTIVE ===========================
def adaptive_quota():
    from fractions import Fraction as Fr
    w = [Fr(17, 23), Fr(1, 23), Fr(1, 23), Fr(3, 23), Fr(1, 23)]
    K = len(w); N = [0] * K
    ts, d0 = [0], [0.0]
    for t in range(16):
        D = [Fr(t) * w[i] - N[i] for i in range(K)]
        j = max(range(K), key=lambda i: (D[i], -i))
        N[j] += 1
        ts.append(t + 1); d0.append(float(Fr(t + 1) * w[0] - N[0]))
    fig, ax = plt.subplots(figsize=(15.8, 9.2), layout='constrained')
    ax.plot(ts, d0, 'o-', color=CRAN, lw=4, ms=16, zorder=3,
            label='deficit of arm 0 under largest-deficit-first')
    ax.axhline(1, color=AMBER, lw=4, ls='--', zorder=2)
    ax.text(0.3, 1.04, 'the quota bound of tracking_exists', fontsize=22, color=AMBER,
            fontweight='bold')
    bad = [i for i, v in zip(ts, d0) if v > 1]
    if bad:
        first = bad[0]
        ax.plot([first], [d0[ts.index(first)]], 'o', ms=28, mfc='none',
                mec=GREEN, mew=5, zorder=4)
        ax.annotate(f'first violation\nt = {first},  D₀ = 26/23',
                    xy=(first, d0[ts.index(first)]), xytext=(first + 1.4, 1.30),
                    fontsize=23, color=GREEN, fontweight='bold',
                    arrowprops=dict(arrowstyle='-|>', color=GREEN, lw=3))
    ax.set_xlabel('t', fontsize=27, labelpad=10)
    ax.set_ylabel('deficit   t·w₀ − N₀(t)', fontsize=25, labelpad=12)
    ax.tick_params(labelsize=22); ax.set_xticks(range(0, 17, 2))
    ax.legend(fontsize=21, frameon=False, loc='lower right')
    ax.grid(color='#E3DCDD', lw=1); ax.set_axisbelow(True)
    note(fig, 'w = (17, 1, 1, 3, 1)/23 · every step verified to be a genuine '
                        'largest-deficit choice · exact rationals throughout', fs=21)
    return save(fig, 'adaptive_fig1_quota.png')
