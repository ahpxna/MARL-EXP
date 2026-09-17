"""Figures for the seven IEEE papers.

Every panel is either an exact evaluation of a proved formula or a plot of a
committed artifact under research/.  Nothing is simulated for the figure; the
provenance of each is recorded in the caption written in the paper.
"""
import json, math
from fractions import Fraction as F
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

CRAN, AMBER, GREEN, INK, GREY = '#63131E', '#8A5A00', '#1C6444', '#161213', '#6E6469'
BLUE = '#1F4E79'
OUT = Path('research/papers/_figures')
W, H = 3.45, 2.45          # IEEE single column

plt.rcParams.update({
    'font.size': 7.2, 'axes.labelsize': 7.6, 'axes.titlesize': 7.8,
    'xtick.labelsize': 6.8, 'ytick.labelsize': 6.8, 'legend.fontsize': 6.6,
    'axes.edgecolor': INK, 'axes.linewidth': 0.6, 'grid.color': '#DED7D8',
    'grid.linewidth': 0.5, 'lines.linewidth': 1.3, 'figure.dpi': 200,
})


def fin(fig, name):
    for ax in fig.axes:
        ax.grid(True, alpha=0.8); ax.set_axisbelow(True)
        for sp in ('top', 'right'):
            ax.spines[sp].set_visible(False)
    fig.savefig(OUT / name, bbox_inches='tight', pad_inches=0.02)
    plt.close(fig)
    print(' ', name)


# ============================== MASTER ==============================
def master_crossover():
    fig, ax = plt.subplots(figsize=(W, H), layout='constrained')
    ks = [0.05 * i for i in range(1, 161)]
    for m, col in ((2, CRAN), (4, AMBER), (8, GREEN)):
        ax.plot(ks, [math.sqrt(m / k) for k in ks], color=col, label=f'$m={m}$')
        ax.plot([m], [1.0], 'o', ms=4.5, mfc='white', mec=col, mew=1.3, zorder=5)
    ax.axhline(1.0, color=GREY, ls=':', lw=1.0)
    ax.set_xscale('log'); ax.set_yscale('log')
    ax.set_xlabel(r'calibration price  $\kappa$')
    ax.set_ylabel(r'optimal split  $z^{\star}/x^{\star}$')
    ax.legend(frameon=False, loc='upper right')
    fin(fig, 'master_fig5_crossover.png')


def master_limits():
    fig, ax = plt.subplots(figsize=(W, H), layout='constrained')
    ks = [10 ** (-2 + 4 * i / 400) for i in range(401)]
    K, m, D = 4, 4, 1.0
    g = [D ** 2 / (2 * K * (math.sqrt(m) + math.sqrt(k)) ** 2) for k in ks]
    ax.plot(ks, g, color=CRAN, label=r'$\Gamma^{*}$ exact')
    ax.plot(ks, [D ** 2 / (2 * K * m)] * len(ks), color=AMBER, ls='--',
            label=r'$\kappa\!\to\!0$:  $\Delta^{2}/(2Km)$')
    ax.plot(ks, [D ** 2 / (2 * K * k) for k in ks], color=GREEN, ls=':',
            label=r'$\kappa\!\to\!\infty$:  $\Delta^{2}/(2K\kappa)$')
    ax.axvline(m, color=GREY, ls=':', lw=1.0)
    ax.annotate(r'$\kappa=m$', xy=(m, min(g)), xytext=(m * 1.5, min(g) * 3),
                fontsize=6.4, color=GREY)
    ax.set_xscale('log'); ax.set_yscale('log')
    ax.set_xlabel(r'calibration price  $\kappa$'); ax.set_ylabel(r'$\Gamma^{*}$')
    ax.legend(frameon=False, loc='lower left')
    fin(fig, 'master_fig6_limits.png')


def master_unitprice():
    fig, ax = plt.subplots(figsize=(W, H), layout='constrained')
    ks = [0.05 * i for i in range(1, 201)]
    for m, col in ((2, CRAN), (4, AMBER), (8, GREEN), (16, BLUE)):
        ax.plot(ks, [(math.sqrt(m) + math.sqrt(k)) ** 2 for k in ks], color=col,
                label=f'$m={m}$')
        ax.plot(ks, [m + k for k in ks], color=col, ls=':', lw=0.8)
    ax.set_xlabel(r'calibration price  $\kappa$')
    ax.set_ylabel(r'price of one unit,  $(\sqrt{m}+\sqrt{\kappa})^{2}$')
    ax.legend(frameon=False, loc='upper left', ncol=2)
    ax.text(0.97, 0.05, 'dotted: additive $m+\\kappa$', transform=ax.transAxes,
            ha='right', fontsize=6.2, color=GREY)
    fin(fig, 'master_fig7_unitprice.png')


def master_collapse():
    """Measured: research/paper_exp_20260916/master_finite.json."""
    import collections
    d = json.loads(Path('research/paper_exp_20260916/master_finite.json').read_text())
    rows = d['rows']
    fig, ax = plt.subplots(figsize=(W, H), layout='constrained')
    xs = [c['lam'] for c in rows if not c['optimal'].get('skipped')]
    ys = [c['optimal']['error'] for c in rows if not c['optimal'].get('skipped')]
    ax.plot(xs, ys, 'o', ms=1.6, color=GREY, alpha=0.45, mew=0, zorder=2,
            label='instances (optimal)')
    lo, hi = min(xs), max(xs)
    grid = [lo * (hi / lo) ** (i / 120) for i in range(121)]
    from math import sqrt, erfc
    law = [0.5 * erfc(sqrt(g) / sqrt(2)) for g in grid]
    ax.plot(grid, law, color=CRAN, lw=1.5, zorder=5, label=r'law  $\Phi(-\sqrt{\lambda})$')
    for kind, col, st in (('uniform', AMBER, '--'), ('one_missing', GREEN, ':'),
                          ('anchor_free', BLUE, '-.')):
        acc = collections.defaultdict(list)
        for c in rows:
            if not c[kind].get('skipped'):
                acc[c['lam']].append(c[kind]['error'])
        ls = sorted(acc)
        ax.plot(ls, [sum(acc[l]) / len(acc[l]) for l in ls], st, color=col, lw=1.2,
                zorder=4, label=kind.replace('_', ' '))
    ax.set_xscale('log'); ax.set_yscale('log')
    ax.set_ylim(0.015, 0.58)
    ax.set_xlabel(r'delivered information  $\lambda=\Gamma^{*}B$')
    ax.set_ylabel('realised error')
    ax.legend(frameon=False, loc='lower left', fontsize=6.0)
    fin(fig, 'master_fig8_collapse.png')


def master_plugin():
    """Measured: research/paper_exp_20260916/master_finite.json."""
    import collections
    d = json.loads(Path('research/paper_exp_20260916/master_finite.json').read_text())
    rows = d['rows']
    pts = collections.defaultdict(list)
    for c in rows:
        for k in d['designs']:
            if c[k].get('skipped'):
                continue
            pts[k].append((c[k]['n_ordinary'], c[k]['error'] - c[k]['predicted']))
    fig, ax = plt.subplots(figsize=(W, H), layout='constrained')
    edges = [4, 8, 16, 32, 64, 128, 512, 10 ** 9]
    for kind, col, mk in (('optimal', CRAN, 'o'), ('uniform', AMBER, 's'),
                          ('one_missing', GREEN, '^'), ('anchor_free', BLUE, 'D')):
        xs, ys = [], []
        for lo, hi in zip(edges[:-1], edges[1:]):
            v = [dv for n, dv in pts[kind] if lo <= n < hi]
            if v:
                xs.append(lo); ys.append(sum(v) / len(v))
        ax.plot(xs, ys, mk + '-', ms=3.2, color=col, lw=1.0, label=kind.replace('_', ' '))
    ref = [4 * 1.3 ** i for i in range(26)]
    ax.plot(ref, [0.042 / r for r in ref], color=GREY, ls=':', lw=1.0,
            label=r'$\propto 1/n_{x}$')
    ax.axhline(0.0, color=INK, lw=0.7)
    ax.set_xscale('log'); ax.set_ylim(-0.0016, 0.0195)
    ax.set_xlabel(r'ordinary observations per group  $n_{x}$')
    ax.set_ylabel('measured error $-$ predicted')
    ax.legend(frameon=False, loc='upper right', fontsize=6.0)
    fin(fig, 'master_fig9_plugin.png')


# ============================== QUERY ==============================
def query_order_curves():
    """Measured: research/paper_exp_20260916/query_generalize.json."""
    import collections
    d = json.loads(Path('research/paper_exp_20260916/query_generalize.json').read_text())
    hs = d['h_grid']
    fig, ax = plt.subplots(figsize=(W, H), layout='constrained')
    by = collections.defaultdict(list)
    for r in d['rows']:
        if r['verified_order'] is not None and r.get('h2_curve'):
            by[r['verified_order']].append(r)
    for r, col in ((1, CRAN), (2, AMBER), (3, GREEN)):
        sel = by[r][:3]
        for k, row in enumerate(sel):
            ax.plot(hs, row['h2_curve'], color=col, lw=1.0, alpha=0.9,
                    label=(f'order $r={r}$' if k == 0 else None))
    ax.axvline(d['tail_h_max'], color=GREY, ls=':', lw=1.0)
    ax.set_xscale('log'); ax.set_yscale('log')
    ax.set_xlabel(r'perturbation scale  $h$')
    ax.set_ylabel(r'$H^{2}$ between the two worlds')
    ax.legend(frameon=False, loc='lower right', fontsize=6.2)
    ax.text(0.03, 0.96, 'dotted: start of the fit window', transform=ax.transAxes,
            va='top', fontsize=6.0, color=GREY)
    fin(fig, 'query_fig3_order.png')


def query_samples():
    """Measured: research/paper_exp_20260916/query_generalize.json."""
    import collections
    d = json.loads(Path('research/paper_exp_20260916/query_generalize.json').read_text())
    by = collections.defaultdict(list)
    for r in d['rows']:
        if r['verified_order'] is not None and r.get('N_at_h0'):
            by[r['verified_order']].append(r['N_at_h0'])
    fig, ax = plt.subplots(figsize=(W, H), layout='constrained')
    cols = {1: CRAN, 2: AMBER, 3: GREEN}
    for r in sorted(by):
        v = sorted(by[r])
        ax.plot([r] * len(v), v, 'o', ms=2.2, color=cols.get(r, BLUE), alpha=0.35, mew=0)
        med = v[len(v) // 2]
        ax.plot([r - 0.24, r + 0.24], [med, med], '-', color=INK, lw=1.5, zorder=6)
        ax.annotate(f'{med:,}', xy=(r + 0.27, med), fontsize=6.0, color=INK, va='center')
    ax.set_yscale('log'); ax.set_xticks(sorted(by))
    ax.set_xlim(0.5, 3.8)
    ax.set_xlabel('verified leakage order  $r$')
    ax.set_ylabel(r'samples to reach $\varepsilon=0.05$  at $h=0.5$')
    ax.text(0.03, 0.95, 'bars: median', transform=ax.transAxes, va='top',
            fontsize=6.2, color=GREY)
    fin(fig, 'query_fig4_samples.png')


def query_slopes():
    """Measured: research/paper_exp_20260916/query_generalize.json."""
    import collections
    d = json.loads(Path('research/paper_exp_20260916/query_generalize.json').read_text())
    fig, ax = plt.subplots(figsize=(W, H), layout='constrained')
    tail = collections.defaultdict(list); full = collections.defaultdict(list)
    for r in d['rows']:
        if r['dev_tail'] is not None:
            tail[r['verified_order']].append(r['dev_tail'])
        if r['dev_full'] is not None:
            full[r['verified_order']].append(r['dev_full'])
    for r in sorted(tail):
        ax.plot([r - 0.16] * len(tail[r]), tail[r], 'o', ms=2.2, color=CRAN,
                alpha=0.35, mew=0, label='tail fit' if r == min(tail) else None)
        ax.plot([r + 0.16] * len(full[r]), full[r], 's', ms=2.2, color=BLUE,
                alpha=0.35, mew=0, label='full-grid fit' if r == min(tail) else None)
    ax.axhline(0.0, color=INK, lw=0.9)
    ax.set_xticks(sorted(tail)); ax.set_xlim(0.5, 3.5)
    ax.set_xlabel('verified leakage order  $r$')
    ax.set_ylabel(r'fitted slope  $-\;2r$')
    ax.legend(frameon=False, loc='lower left', fontsize=6.2)
    fin(fig, 'query_fig6_slopes.png')


def query_window():
    d = json.loads((OUT / 'poster_figure_data.json').read_text())['QUERY_regret']
    r = d['rows'][0]
    gam, Lmx = 13983 / 32768, 2401 / 4096
    rho = 1 - r['H2']
    Ns = [int(r['N'] * (0.3 + 0.1 * i)) for i in range(26)]
    fig, ax = plt.subplots(figsize=(W, H), layout='constrained')
    lo = [gam / 4 * rho ** (2 * n) for n in Ns]
    hi = [Lmx / 2 * rho ** n for n in Ns]
    ax.fill_between(Ns, lo, hi, color=CRAN, alpha=0.16, lw=0)
    ax.plot(Ns, lo, color=CRAN, lw=1.0, label=r'$\frac{\gamma}{4}\rho^{2N}$')
    ax.plot(Ns, hi, color=AMBER, lw=1.0, label=r'$\frac{L_{\max}}{2}\rho^{N}$')
    ax.plot([r['N']], [r['equal_prior_mean_regret']], 'o', ms=5,
            mfc='white', mec=GREEN, mew=1.4, zorder=5, label='measured')
    ax.set_yscale('log'); ax.set_xlabel('samples  $N$'); ax.set_ylabel('Bayes regret')
    ax.legend(frameon=False, loc='upper right')
    fin(fig, 'query_fig5_window.png')


# ============================== STRUCTURAL ==============================
def struct_enum():
    """Measured: research/paper_exp_20260916/struct_enum_large.json (exact DP,
    validated against brute-force enumeration for every m it reached)."""
    d = json.loads(Path('research/paper_exp_20260916/struct_enum_large.json').read_text())
    rows = d['rows']
    ms = [r['m'] for r in rows]
    fig, ax = plt.subplots(figsize=(W, H), layout='constrained')
    ax.axvspan(5, 13, color=GREY, alpha=0.16, lw=0)
    ax.plot(ms, [float(r['orderings']) for r in rows], color=BLUE, lw=1.4,
            label='orderings certified')
    ax2 = ax.twinx()
    ax2.plot(ms, [r['optimal_fraction'] for r in rows], color=CRAN, ls='--', lw=1.3,
             label='fraction at the bound')
    ax2.set_yscale('log'); ax2.set_ylabel('fraction attaining defect 2'); ax2.grid(False)
    ax2.spines['top'].set_visible(False)
    ax.set_yscale('log'); ax.set_xlabel(r'population size  $m$')
    ax.set_ylabel('orderings')
    ax.text(13.5, 3e30, 'reachable by\nenumeration', fontsize=5.8, color=GREY, va='top')
    h1, l1 = ax.get_legend_handles_labels(); h2, l2 = ax2.get_legend_handles_labels()
    ax.legend(h1 + h2, l1 + l2, frameon=False, loc='center right', fontsize=6.2)
    fin(fig, 'struct_fig3_enum.png')


def struct_defectdist():
    """Measured: research/paper_exp_20260916/struct_enum_large.json."""
    d = json.loads(Path('research/paper_exp_20260916/struct_enum_large.json').read_text())
    fig, ax = plt.subplots(figsize=(W, H), layout='constrained')
    for m, col in ((10, CRAN), (20, AMBER), (40, GREEN), (80, BLUE)):
        r = next(x for x in d['rows'] if x['m'] == m)
        hist = {int(k): v for k, v in r['total_defect_distribution'].items()}
        tot = sum(hist.values())
        ks = sorted(hist)
        ax.plot(ks, [hist[k] / tot for k in ks], color=col, lw=1.2, label=f'$m={m}$')
    ax.axvline(2, color=INK, lw=0.9)
    ax.annotate('proved bound', xy=(2, 1e-4), xytext=(9, 3e-4), fontsize=6.2, color=INK,
                arrowprops=dict(arrowstyle='->', color=INK, lw=0.6))
    ax.set_yscale('log'); ax.set_xscale('log')
    ax.set_xlabel('total defect of an ordering')
    ax.set_ylabel('fraction of orderings')
    ax.set_ylim(1e-15, 2.0)
    ax.legend(frameon=False, loc='lower center', ncol=2, fontsize=6.2)
    fin(fig, 'struct_fig6_defectdist.png')


def struct_tolerance():
    fig, ax = plt.subplots(figsize=(W, H), layout='constrained')
    eps = [i / 20000 for i in range(1, 601)]
    ax.step([0] + eps, [5] + [5 if e < 1 / 114 else 1 for e in eps],
            where='post', color=CRAN, label=r'witness $F_{7}$')
    for r, col in ((3, AMBER), (5, GREEN)):
        ax.step([0] + eps, [r] + [r if e < 1 / (2 * r) else 1 for e in eps],
                where='post', color=col, ls='--',
                label=r'staircase $F_{%d}$' % r)
    ax.axvline(1 / 114, color=GREY, ls=':', lw=1.0)
    ax.annotate(r'$1/114$', xy=(1 / 114, 5), xytext=(1 / 114 * 1.6, 4.4),
                fontsize=6.4, color=GREY)
    ax.set_xscale('log'); ax.set_xlabel(r'tolerance  $\varepsilon$  (normalised)')
    ax.set_ylabel(r'rankings required  $\chi_{\varepsilon}$')
    ax.set_ylim(0.5, 5.8); ax.legend(frameon=False, loc='upper right')
    fin(fig, 'struct_fig4_tolerance.png')


def struct_traces():
    import itertools, math as _m
    m = 7
    p, q = _m.ceil((m - 2) / 2), (m - 2) // 2
    g = [-3] + [-1] * p + [1] * q + [3]
    found = {}
    for pr in sorted(set(itertools.permutations(g))):
        s, ss, d = 0, [], []
        for k in range(1, m):
            s += pr[k - 1]; ss.append(s); d.append(abs(s) - (k % 2))
        nz = [i for i, x in enumerate(d) if x > 0]
        if len(nz) == 1 and d[nz[0]] == 2 and nz[0] not in found:
            found[nz[0]] = ss
    fig, ax = plt.subplots(figsize=(W, H), layout='constrained')
    cols = [CRAN, AMBER, GREEN, BLUE, '#7A3B8F', '#0F6F73']
    for j in sorted(found):
        ax.plot(range(1, m), found[j], '-o', ms=2.6, color=cols[j % len(cols)],
                label=f'pays at $k={j+1}$')
    ax.axhspan(-1, 1, color=GREY, alpha=0.14, lw=0)
    ax.set_xlabel('budget  $k$'); ax.set_ylabel('prefix sum  $s_{k}$')
    ax.legend(frameon=False, ncol=2, loc='upper center', fontsize=5.8)
    ax.text(0.02, 0.04, 'shaded: free band $\\{-1,0,1\\}$', transform=ax.transAxes,
            fontsize=6.2, color=GREY)
    fin(fig, 'struct_fig5_traces.png')


# ============================== FUNCTIONAL ==============================
def func_shrinkexpand():
    fig, ax = plt.subplots(figsize=(W, H), layout='constrained')
    zs = [i / 400 for i in range(0, 481)]
    Ci, Cj, eta = 1.0, 0.5, 0.25
    S = [0.0 if z >= Ci else (Ci - z) ** 2 / 4 for z in zs]
    E = [max(0.0, z - Cj) ** 2 / 4 for z in zs]
    ax.plot(zs, S, color=CRAN, label=r'shrink  $S_{i}(z)$')
    ax.plot(zs, E, color=GREEN, label=r'expand  $E_{j}(z)$')
    tot = [a + b for a, b in zip(S, E)]
    ax.plot(zs, tot, color=INK, lw=1.6, label=r'$S_{i}(z)+E_{j}(z)$')
    k = min(range(len(zs)), key=lambda i: tot[i])
    ax.plot([zs[k]], [tot[k]], 'o', ms=5, mfc='white', mec=AMBER, mew=1.4, zorder=5)
    ax.annotate('inner optimum', xy=(zs[k], tot[k]), xytext=(zs[k] + 0.15, tot[k] + 0.03),
                fontsize=6.2, color=AMBER,
                arrowprops=dict(arrowstyle='-', color=AMBER, lw=0.7))
    ax.set_xlabel(r'target range  $z$'); ax.set_ylabel('energy')
    ax.legend(frameon=False, loc='upper center')
    fin(fig, 'func_fig3_shrinkexpand.png')


def func_ratio():
    fig, ax = plt.subplots(figsize=(W, H), layout='constrained')
    es = [10 ** (-2 + 2 * i / 300) for i in range(301)]
    ax.plot(es, [9 * e for e in es], color=CRAN, label=r'family 1: $\leq 9\eta$')
    ax.plot(es, [(1 + 3 * e) / (16 * e) for e in es], color=GREEN,
            label=r'family 2: $\geq (1+3\eta)/(16\eta)$')
    ax.axhline(1.0, color=GREY, ls=':', lw=1.0)
    ax.set_xscale('log'); ax.set_yscale('log')
    ax.set_xlabel(r'$\eta$')
    ax.set_ylabel(r'$J_{\mathrm{full}}/J_{\mathrm{scalar}}$')
    ax.legend(frameon=False, loc='upper center')
    ax.text(0.03, 0.06, 'any constant correction is crossed by both',
            transform=ax.transAxes, fontsize=6.2, color=GREY)
    fin(fig, 'func_fig4_ratio.png')


def func_paneldetail():
    p = Path('research/confirm_ieee_20260912/functional_v4_lucb_ieee10seed_cellv1.json')
    names, fr, med = [], [], []
    if p.exists():
        d = json.loads(p.read_text())
        bv = d.get('by_variant', {})
        for k, v in bv.items():
            if isinstance(v, dict) and 'certificate_fraction' in v:
                names.append(k); fr.append(v['certificate_fraction'])
                med.append(v.get('median_N_certificate') or 0)
    if not names:
        d = json.loads((OUT / 'poster_figure_data.json').read_text())['FUNCTIONAL_panel']
        for k, v in d['variants'].items():
            names.append(k); fr.append(v['certificate_fraction']); med.append(v['median_N'])
    order = sorted(range(len(names)), key=lambda i: -fr[i])
    names = [names[i] for i in order]; fr = [fr[i] for i in order]; med = [med[i] for i in order]
    fig, ax = plt.subplots(figsize=(W, H), layout='constrained')
    ax.scatter(med, fr, s=26, c=CRAN, zorder=5)
    for n, x, y in zip(names, med, fr):
        ax.annotate(n.replace('_', r'\_') if False else n, (x, y), fontsize=5.8,
                    xytext=(3, 3), textcoords='offset points', color=INK)
    ax.set_xlabel('median queries when certified'); ax.set_ylabel('fraction certified')
    ax.set_xscale('log')
    ax.text(0.02, 0.05, 'upper-left is better', transform=ax.transAxes,
            fontsize=6.2, color=GREY)
    fin(fig, 'func_fig5_panel_detail.png')


# ============================== D6 ==============================
def d6_threshold():
    fig, ax = plt.subplots(figsize=(W, H), layout='constrained')
    rs = [1 + i / 200 for i in range(0, 301)]
    for A, col in ((3, CRAN), (4, AMBER), (5, GREEN)):
        ax.plot(rs, [A * (2 - r) for r in rs], color=col, label=f'$|A|={A}$')
    ax.axvline(2.0, color=GREY, ls=':', lw=1.0)
    ax.axhline(0.0, color=INK, lw=0.7)
    ax.annotate(r'$\rho=2\delta$', xy=(2, 0), xytext=(2.05, 1.2),
                fontsize=6.4, color=GREY)
    ax.text(1.05, -1.4, 'Top-$C$ strictly suboptimal', fontsize=6.2, color=CRAN)
    ax.text(2.25, 0.5, 'Top-$C$ optimal', fontsize=6.2, color=GREEN)
    ax.set_xlabel(r'margin  $\rho$   (at $\delta=1$)')
    ax.set_ylabel(r'$2\,(L(A)-L(A^{\complement}))$')
    ax.legend(frameon=False, loc='upper right')
    fin(fig, 'd6_fig3_threshold.png')


def d6_affine():
    fig, ax = plt.subplots(figsize=(W, H), layout='constrained')
    es = [i / 200 for i in range(201)]
    IB = 1.0
    for c, Ip, col, st in ((1.5, 2.4, CRAN, '-'), (1.5, 1.5, AMBER, '--'),
                           (2.0, 1.4, GREEN, ':')):
        ax.plot(es, [IB + e * (Ip / c - IB) for e in es], color=col, ls=st,
                label=r'$c=%.1f$, $I_{\mathrm{pair}}=%.1f$' % (c, Ip))
    ax.set_xlabel(r'budget split  $\eta$'); ax.set_ylabel(r'delivered information  $I(\eta)$')
    ax.legend(frameon=False, loc='upper left')
    ax.text(0.97, 0.05, 'affine: optimum at an endpoint\nunless the slope vanishes',
            transform=ax.transAxes, ha='right', fontsize=6.2, color=GREY)
    fin(fig, 'd6_fig4_affine.png')


def d6_reference():
    """Measured: research/paper_exp_20260916/d6_reference.json (exact rationals,
    transcribed from the Lean definitions and validated at t=0 against
    steered_span before the sweep was reported)."""
    from fractions import Fraction as _F
    d = json.loads(Path('research/paper_exp_20260916/d6_reference.json').read_text())
    rows = [r for r in d['rows'] if r['n'] == 8]
    fig, ax = plt.subplots(figsize=(W, H), layout='constrained')
    cols = {'1': CRAN, '5/4': AMBER, '3/2': GREEN, '7/4': BLUE, '2': '#7A3B8F'}
    for rho, col in cols.items():
        rs = sorted([r for r in rows if r['rho'] == rho], key=lambda r: _F(r['t']))
        x = [float(_F(r['t'])) for r in rs]
        y = [r['doubled_regret'] for r in rs]
        ax.plot(x, y, color=col, lw=1.2, label=r'$\rho=%s$' % rho.replace('/', '/'))
        flip = [r for r in rs if not r['topC_is_A']]
        if flip:
            t0 = float(_F(flip[0]['t']))
            ax.plot([t0], [flip[0]['doubled_regret']], 'v', ms=5, mfc='white',
                    mec=col, mew=1.2, zorder=6)
    ax.axhline(0.0, color=INK, lw=0.7)
    ax.set_xlabel(r'product reference  $t=q_{i}(\mathrm{true})$')
    ax.set_ylabel(r'doubled regret  $2\,(L(A)-L(A^{\complement}))$')
    ax.legend(frameon=False, loc='upper right', ncol=2, fontsize=6.0)
    ax.text(0.02, 0.06, r'$\blacktriangledown$ first $t$ at which $A$ loses Top-$C$',
            transform=ax.transAxes, fontsize=6.0, color=GREY)
    fin(fig, 'd6_fig5_reference.png')


# ============================== SUPPORT ==============================
def support_risk():
    fig, ax = plt.subplots(figsize=(W, H), layout='constrained')
    for (a, b), col in (((3, 2), CRAN), ((5, 3), AMBER), ((8, 5), GREEN)):
        Rs = list(range(0, b + 1))
        ax.plot(Rs, [(b - r) / (a + b - r) for r in Rs], 'o-', ms=3.5, color=col,
                label=f'$a={a}$, $b={b}$')
    ax.set_xlabel(r'revealed unsafe tips  $|R|$')
    ax.set_ylabel(r'decoder risk  $L/(a+L)$')
    ax.legend(frameon=False, loc='upper right')
    fin(fig, 'support_fig3_risk.png')


def support_counts():
    """Measured: research/paper_exp_20260916/support_thresholds.json."""
    import collections
    d = json.loads(Path('research/paper_exp_20260916/'
                        'support_thresholds.json').read_text())
    eps = '1/100'
    fig, ax = plt.subplots(figsize=(W, H), layout='constrained')
    for P, col in (('1/10', CRAN), ('1/4', AMBER), ('1/2', GREEN), ('3/4', BLUE)):
        sub = sorted([r for r in d['rows'] if r['eps'] == eps and r['P'] == P],
                     key=lambda r: r['K'])
        if not sub:
            continue
        Ks = [r['K'] for r in sub]
        ax.plot(Ks, [r['N_recover'] for r in sub], '-', color=col, lw=1.3,
                label=f'$P={P}$')
        ax.plot(Ks, [r['N_decide'] for r in sub], ':', color=col, lw=1.1)
    ax.set_xscale('log', base=2); ax.set_yscale('log')
    ax.set_xlabel('number of classes  $K$')
    ax.set_ylabel(r'samples to reach $\varepsilon=1/100$')
    ax.legend(frameon=False, loc='upper left', fontsize=6.2)
    ax.text(0.97, 0.06, 'solid: recover   dotted: decide', transform=ax.transAxes,
            ha='right', fontsize=6.2, color=GREY)
    fin(fig, 'support_fig4_counts.png')


def support_identity():
    """Measured: research/paper_exp_20260916/support_thresholds.json."""
    d = json.loads(Path('research/paper_exp_20260916/'
                        'support_thresholds.json').read_text())
    sims = d['sims']
    fig, ax = plt.subplots(figsize=(W, H), layout='constrained')
    x = [s['predicted_correct'] for s in sims]
    y = [s['measured_correct'] for s in sims]
    e = [2 * s['se'] for s in sims]
    ax.errorbar(x, y, yerr=e, fmt='o', ms=2.8, color=CRAN, ecolor=GREY,
                elinewidth=0.7, capsize=1.2, mew=0, zorder=5)
    lo, hi = min(x + y) - 0.01, max(x + y) + 0.01
    ax.plot([lo, hi], [lo, hi], color=INK, lw=0.9, zorder=2)
    ax.set_xlim(lo, hi); ax.set_ylim(lo, hi)
    ax.set_xlabel('identity  $1-R_{\\mathrm{rec}}$')
    ax.set_ylabel('measured, simulating the process')
    ax.text(0.03, 0.95, f"{len(sims)} cells, worst $|z|={d['sim_max_z']:.2f}$",
            transform=ax.transAxes, va='top', fontsize=6.2, color=GREY)
    fin(fig, 'support_fig6_identity.png')


def support_threeworld():
    tips = {0: (1, 1, -1), 1: (-1, 1, 1), 2: (1, -1, 1)}
    fig, ax = plt.subplots(figsize=(W, H), layout='constrained')
    cols = [CRAN, AMBER, GREEN]
    for w in range(3):
        rad = [abs(sum(tips[w][l] for l in range(3) if l != j)) / 2 for j in range(3)]
        ax.bar([j + 0.26 * (w - 1) for j in range(3)], rad, width=0.24,
               color=cols[w], label=f'world {w}')
    ax.set_xticks(range(3)); ax.set_xticklabels([f'keep $j={j}$' for j in range(3)])
    ax.set_ylabel(r'$\mathrm{selectedRadius}$')
    ax.legend(frameon=False, loc='upper center', ncol=3)
    ax.text(0.5, -0.30, 'zero-regret sets $\\{0,1\\},\\{1,2\\},\\{0,2\\}$: '
                        'pairwise intersecting, empty triple intersection',
            transform=ax.transAxes, ha='center', fontsize=6.0, color=GREY)
    fin(fig, 'support_fig5_threeworld.png')


# ============================== ADAPTIVE ==============================
def adaptive_trace():
    w = [F(17, 23), F(1, 23), F(1, 23), F(3, 23), F(1, 23)]
    N = [0] * 5
    T = 15
    hist = [[] for _ in range(5)]
    served = []
    for t in range(T):
        D = [t * w[i] - N[i] for i in range(5)]
        for i in range(5):
            hist[i].append(float(D[i]))
        a = D.index(max(D)); served.append(a); N[a] += 1
    fig, ax = plt.subplots(figsize=(W, H), layout='constrained')
    cols = [CRAN, AMBER, GREEN, BLUE, '#7A3B8F']
    for i in range(5):
        ax.plot(range(T), hist[i], '-', color=cols[i], lw=1.1,
                label=f'arm {i}' + (r'  ($w=17/23$)' if i == 0 else ''))
    ax.axhline(1.0, color=INK, ls='--', lw=0.9)
    ax.annotate('quota bound $1$', xy=(1, 1.0), xytext=(1.2, 1.12),
                fontsize=6.2, color=INK)
    ax.plot([11], [26 / 23], 'o', ms=5, mfc='white', mec=CRAN, mew=1.4, zorder=6)
    ax.set_xlabel('horizon  $t$'); ax.set_ylabel(r'deficit  $D_{i}(t)$')
    ax.legend(frameon=False, loc='lower left', ncol=2, fontsize=5.8)
    fin(fig, 'adaptive_fig2_trace.png')


def adaptive_search():
    """Measured: research/paper_exp_20260916/adaptive_bigsearch.json."""
    d = json.loads(Path('research/paper_exp_20260916/adaptive_bigsearch.json').read_text())
    hw = {float(k): v for k, v in d['hist_worst'].items()}
    fig, ax = plt.subplots(figsize=(W, H), layout='constrained')
    xs = sorted(hw)
    ax.plot(xs, [hw[x] for x in xs], color=CRAN, lw=1.2)
    ax.fill_between(xs, [hw[x] for x in xs], 0.5, color=CRAN, alpha=0.16, lw=0)
    ax.axvline(1.0, color=INK, ls='--', lw=1.0)
    ax.annotate('quota bound', xy=(1.0, max(hw.values())), fontsize=6.2, color=INK,
                xytext=(1.06, max(hw.values()) * 0.5))
    ax.set_yscale('log')
    ax.set_xlabel('worst deficit reached by the online rule')
    ax.set_ylabel('violating targets')
    ax.set_title(f"{d['targets_violating_quota']:,} of {d['targets_checked']:,} targets "
                 f"({100*d['violation_fraction']:.1f}\\%)", fontsize=6.8)
    fin(fig, 'adaptive_fig3_search.png')


def adaptive_onset():
    """Measured: research/paper_exp_20260916/adaptive_bigsearch.json."""
    d = json.loads(Path('research/paper_exp_20260916/adaptive_bigsearch.json').read_text())
    pk = d['per_K']
    Ks = sorted(int(k) for k in pk)
    fig, ax = plt.subplots(figsize=(W, H), layout='constrained')
    ax.bar(Ks, [pk[str(k)]['fraction'] for k in Ks], width=0.6, color=BLUE, alpha=0.85,
           label='fraction violating')
    ax2 = ax.twinx()
    ax2.plot(Ks, [pk[str(k)]['worst'] for k in Ks], 'o-', ms=3.5, color=CRAN,
             label='worst deficit')
    ax2.set_ylim(1.0, None)
    ax2.set_ylabel('worst deficit (bound is 1)'); ax2.grid(False)
    ax2.spines['top'].set_visible(False)
    ax.set_xlabel('number of arms  $K$'); ax.set_ylabel('fraction of targets violating')
    ax.set_xticks(Ks)
    h1, l1 = ax.get_legend_handles_labels(); h2, l2 = ax2.get_legend_handles_labels()
    ax.legend(h1 + h2, l1 + l2, frameon=False, loc='upper left', fontsize=6.2)
    fin(fig, 'adaptive_fig5_onset.png')


def adaptive_existence():
    import math as _m
    w = [F(17, 23), F(1, 23), F(1, 23), F(3, 23), F(1, 23)]
    Ts = list(range(1, 31))
    onl, off = [], []
    N = [0] * 5
    for t in range(max(Ts) + 1):
        D = [t * w[i] - N[i] for i in range(5)]
        if t in Ts:
            onl.append(float(max(D)))
        if t:
            N[D.index(max(D))] += 1
    for t in Ts:
        fl = [_m.floor(float(t * wi)) for wi in w]
        short = t - sum(fl)
        frac = sorted(range(5), key=lambda i: -(float(t * w[i]) - fl[i]))
        NN = fl[:]
        for i in frac[:short]:
            NN[i] += 1
        off.append(max(abs(float(t * w[i]) - NN[i]) for i in range(5)))
    fig, ax = plt.subplots(figsize=(W, H), layout='constrained')
    ax.plot(Ts, onl, '-o', ms=3, color=CRAN, label='online largest-deficit')
    ax.plot(Ts, off, '-s', ms=3, color=GREEN, label='offline construction')
    ax.axhline(1.0, color=INK, ls='--', lw=0.9)
    ax.set_xlabel('horizon  $t$'); ax.set_ylabel(r'$\max_{i}|D_{i}(t)|$')
    ax.legend(frameon=False, loc='upper left')
    fin(fig, 'adaptive_fig4_existence.png')


if __name__ == '__main__':
    OUT.mkdir(parents=True, exist_ok=True)
    print('MASTER');     master_crossover(); master_limits(); master_unitprice()
    print('QUERY');      query_order_curves(); query_samples(); query_window()
    print('STRUCTURAL'); struct_enum(); struct_tolerance(); struct_traces()
    print('FUNCTIONAL'); func_shrinkexpand(); func_ratio(); func_paneldetail()
    print('D6');         d6_threshold(); d6_affine(); d6_reference()
    print('SUPPORT');    support_risk(); support_counts(); support_threeworld()
    print('ADAPTIVE');   adaptive_trace(); adaptive_search(); adaptive_existence()


# ====================== NEW EXPERIMENTS (2026-09-16) ======================
def d6_wide():
    """Measured: research/paper_exp_20260916/d6_reference_wide.json."""
    from fractions import Fraction as _F
    d = json.loads(Path('research/paper_exp_20260916/'
                        'd6_reference_wide.json').read_text())
    fig, ax = plt.subplots(figsize=(W, H), layout='constrained')
    cols = [CRAN, AMBER, GREEN]
    for (n, k), col in zip(d['balanced_sizes'], cols):
        xs, ys = [], []
        for rho in d['rhos']:
            v = d['onsets'][f'{n}|{k}|{rho}']
            if v is not None:
                xs.append(float(_F(rho))); ys.append(float(_F(v)))
        ax.plot(xs, ys, 'o-', ms=3.4, color=col, lw=1.2, label=f'$n={n}$, $|A|={k}$')
        last = float(_F(d['rhos'][-1]))
        ax.plot([last], [0.52], 'x', ms=5, color=col, mew=1.3)
    ax.axhline(0.5, color=GREY, ls=':', lw=1.0)
    ax.set_ylim(0, 0.58)
    ax.set_xlabel(r'margin  $\mu$')
    ax.set_ylabel(r'breakdown point  $t^{\star}$')
    ax.legend(frameon=False, loc='upper left', fontsize=6.2)
    ax.text(0.97, 0.06, r'$\times$ at $\mu=2$: no breakdown on the grid',
            transform=ax.transAxes, ha='right', fontsize=6.0, color=GREY)
    fin(fig, 'd6_fig6_wide.png')


def query_highorder():
    """Measured: research/paper_exp_20260916/query_highorder.json."""
    import collections
    d = json.loads(Path('research/paper_exp_20260916/'
                        'query_highorder.json').read_text())
    rows = [r for r in d['rows'] if r.get('built')]
    fig, ax = plt.subplots(figsize=(W, H), layout='constrained')
    ok = collections.defaultdict(list); bad = collections.defaultdict(list)
    for r in rows:
        (ok if r['reliable'] else bad)[r['verified_order']].append(r['dev_tail'])
    for o in sorted(set(list(ok) + list(bad))):
        if ok[o]:
            ax.plot([o - 0.12] * len(ok[o]), ok[o], 'o', ms=2.2, color=CRAN,
                    alpha=0.35, mew=0, label='within tolerance' if o == 1 else None)
        if bad[o]:
            ax.plot([o + 0.12] * len(bad[o]), bad[o], 'x', ms=3.4, color=BLUE,
                    mew=0.9, label='flagged unreliable' if bad[o] and o == max(bad) else None)
    ax.axhline(0.0, color=INK, lw=0.9)
    ax.set_xticks(sorted(set(list(ok) + list(bad))))
    ax.set_xlabel('verified leakage order  $r$')
    ax.set_ylabel(r'fitted slope  $-\;2r$')
    ax.legend(frameon=False, loc='lower left', fontsize=6.2)
    fin(fig, 'query_fig7_highorder.png')


def func_proxy():
    """Measured: research/paper_exp_20260916/functional_proxy.json."""
    d = json.loads(Path('research/paper_exp_20260916/'
                        'functional_proxy.json').read_text())
    rows = d['rows']
    moved = [r['ratio'] for r in rows if r['extremum_moves']]
    fixed = [r['ratio'] for r in rows if not r['extremum_moves']]
    import numpy as np
    bins = np.logspace(-2, 1.7, 46)
    fig, ax = plt.subplots(figsize=(W, H), layout='constrained')
    ax.hist(fixed, bins=bins, color=GREY, alpha=0.55, lw=0,
            label=f'extrema fixed ({len(fixed)})')
    ax.hist(moved, bins=bins, color=CRAN, alpha=0.75, lw=0,
            label=f'an extremum moves ({len(moved)})')
    ax.axvline(1.0, color=INK, lw=0.9)
    ax.set_xscale('log')
    ax.set_xlabel(r'$J_{\mathrm{full}}/J_{\mathrm{scalar}}$')
    ax.set_ylabel('instances')
    ax.legend(frameon=False, loc='upper left', fontsize=6.2)
    fin(fig, 'func_fig6_proxy.png')


def adaptive_rules():
    """Measured: research/paper_exp_20260916/adaptive_rules.json."""
    d = json.loads(Path('research/paper_exp_20260916/'
                        'adaptive_rules.json').read_text())
    rules = [r for r in d['rules'] if r != 'randomized']
    fig, ax = plt.subplots(figsize=(W, H), layout='constrained')
    for r in rules:
        s = d['per_rule'][r]
        x, y = 100 * s['fraction'], 100 * s['fraction_surplus']
        ax.plot([x], [y], 'o', ms=5, mfc='white', mec=CRAN, mew=1.4, zorder=5)
        ax.annotate(r.replace('_', ' '), (x, y), fontsize=5.8, color=INK,
                    xytext=(4, 4), textcoords='offset points')
    ax.set_xlim(-6, 106); ax.set_ylim(-6, 106)
    ax.plot([0, 100], [0, 0], color=GREY, lw=0.7, ls=':')
    ax.plot([0, 0], [0, 100], color=GREY, lw=0.7, ls=':')
    ax.set_xlabel(r'targets violating the deficit bound  (\%)')
    ax.set_ylabel(r'targets violating the surplus bound  (\%)')
    ax.text(0.5, 0.5, 'the origin is empty', transform=ax.transAxes,
            ha='center', fontsize=6.4, color=GREY)
    fin(fig, 'adaptive_fig6_rules.png')


def master_misspec():
    """Measured: research/paper_exp_20260916/master_misspec.json."""
    d = json.loads(Path('research/paper_exp_20260916/'
                        'master_misspec.json').read_text())
    order = ['gaussian', 'heavy_tail_t10', 'heavy_tail_t5', 'heavy_tail_t3',
             'nuisance_t3', 'hetero', 'contaminated_1pct', 'contaminated_5pct',
             'delta_0.75', 'delta_1.25', 'delta_0.5', 'delta_2.0']
    lab = {'gaussian': 'model correct', 'heavy_tail_t10': 'noise $t_{10}$',
           'heavy_tail_t5': 'noise $t_{5}$', 'heavy_tail_t3': 'noise $t_{3}$',
           'nuisance_t3': 'offset $t_{3}$', 'hetero': 'variances $9\\times$ apart',
           'contaminated_1pct': 'anchors 1\\% bad', 'contaminated_5pct': 'anchors 5\\% bad',
           'delta_0.75': r'$\Delta\times0.75$', 'delta_1.25': r'$\Delta\times1.25$',
           'delta_0.5': r'$\Delta\times0.5$', 'delta_2.0': r'$\Delta\times2$'}
    fig, ax = plt.subplots(figsize=(W, H * 1.15), layout='constrained')
    ys = range(len(order))
    vals = [d['summary'][a]['mean_deviation'] for a in order]
    cols = [GREEN if v < 0.005 else (AMBER if v < 0.05 else CRAN) for v in vals]
    ax.barh(list(ys), vals, color=cols, height=0.66)
    ax.axvline(0.0, color=INK, lw=0.8)
    ax.set_yticks(list(ys)); ax.set_yticklabels([lab[a] for a in order], fontsize=6.0)
    ax.invert_yaxis()
    ax.set_xlabel('mean (realised error $-$ predicted)')
    fin(fig, 'master_fig10_misspec.png')


def struct_families():
    """Measured: research/paper_exp_20260916/struct_families.json."""
    d = json.loads(Path('research/paper_exp_20260916/'
                        'struct_families.json').read_text())
    rows = d['rows']
    ms = [r['m'] for r in rows]
    fig, ax = plt.subplots(figsize=(W, H), layout='constrained')
    ax.plot(ms, [r['min_D_forcing'] for r in rows], 'o-', ms=3.2, color=AMBER,
            label='least $D$ forcing a defect')
    ax.plot(ms, [r['min_D_covering'] for r in rows], 's-', ms=3.2, color=CRAN,
            label='least $D$ also covering')
    ax.plot(ms, [r['paper_D'] for r in rows], ':', color=INK, lw=1.4,
            label=r"the paper's $g_{m}$,  $D=m+4$")
    ax.set_xlabel('population size  $m$')
    ax.set_ylabel(r'total variation  $D=\sum_{i}|g_{i}|$')
    ax.legend(frameon=False, loc='upper left', fontsize=6.2)
    fin(fig, 'struct_fig7_families.png')
