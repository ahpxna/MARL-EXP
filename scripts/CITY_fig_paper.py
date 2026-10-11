#!/usr/bin/env python3
"""Paper figures (05/10, story set), one style.  Reads the registered reports through the dashboard's contrast parser (scripts/DASH_build.py),
so re-running after a pending job lands updates every figure.  Pending results are drawn as 'pending' rows, never invented.
  p1_schematic      the two frozen populations, the two interfaces TSI changes, and the closed loop
  p2_problem        M2: the fleet's benefit before / after the learned-light upgrade (grid4 R9, R10; spider rule)
  p3_frontier       agent fuel vs agent time loss of every arm vs R (grid4), feasible region shaded
  p4_mechanism      light reaction (grid4 vs spider), residual cost vs green lengthening, exact vs forecast timing
  p5_evidence       TSI vs R across confirmations, new policies, scope tests, other networks (forest)
  p6_comparators    TSI minus each comparator (forest)
  p7_spider         spider diagnosis (only when the W8-1 report exists)
  p8_robust         wave 9: channel / sensing / simulator-model robustness, one global adapter, MaxPressure (pending rows until the reports exist)
Palette: the dataviz reference categorical slots 1-3 (#2a78d6 TSI, #eb6834 other repairs / comparators, #1baf7a retraining), validated
(light): all checks pass; aqua below 3:1 contrast, so every point is direct-labelled."""
import importlib.util, json, re, sys
from pathlib import Path
import numpy as np
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch, Rectangle
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT)); CS = ROOT / 'research/city_sim'; OUT = ROOT / 'research/papers/_tex/figs_two_pop'
spec = importlib.util.spec_from_file_location('D', ROOT / 'scripts/DASH_build.py'); D = importlib.util.module_from_spec(spec); spec.loader.exec_module(D)
from scripts.CITY_spatp_report import rows  # noqa: E402
BLUE, ORANGE, AQUA, GRAY, LGRAY, INK, INK2, GRID = '#2a78d6', '#eb6834', '#1baf7a', '#8a8984', '#d6d5cf', '#0b0b0b', '#52514e', '#e6e5e0'
plt.rcParams.update({'font.size': 8.5, 'axes.titlesize': 9, 'axes.labelsize': 8.5, 'xtick.labelsize': 8, 'ytick.labelsize': 8, 'legend.fontsize': 7.5,
                     'axes.spines.top': False, 'axes.spines.right': False, 'axes.edgecolor': GRAY, 'axes.linewidth': 0.6, 'xtick.color': INK2,
                     'ytick.color': INK2, 'axes.labelcolor': INK, 'text.color': INK, 'grid.color': GRID, 'grid.linewidth': 0.6, 'pdf.fonttype': 42,
                     'axes.titleweight': 'bold', 'axes.titlelocation': 'left', 'legend.frameon': False})


def rep(p):
    f = CS / p
    return {r['name']: r['m'] for r in D.ch_contrasts(f.read_text())['rows']} if f.exists() else {}


def get(p, name):
    return rep(p).get(name)


def verdict(p, pat):
    """'PASS' / 'FAIL' from the report line containing pat (the registered verdict line), else None (pending)."""
    f = CS / p
    if not f.exists():
        return None
    for line in f.read_text().splitlines():
        if pat in line:
            m = re.search(r':\s*(PASS|FAIL|CONFIRMED|NOT CONFIRMED)\b', line)
            if m:
                return {'CONFIRMED': 'PASS', 'NOT CONFIRMED': 'FAIL'}.get(m.group(1), m.group(1))
    return None


def section(p, marker):
    """contrast rows of the part of a report after a marker line (reports that repeat a contrast name per section)."""
    f = CS / p
    if not f.exists():
        return {}
    t = f.read_text(); i = t.find(marker)
    return {} if i < 0 else {r['name']: r['m'] for r in D.ch_contrasts(t[i:])['rows']}


def save(fig, name):
    OUT.mkdir(parents=True, exist_ok=True)
    for ext in ('pdf', 'png'):
        fig.savefig(OUT / f'{name}.{ext}', dpi=200, bbox_inches='tight')
    plt.close(fig); print('wrote', name)


# ------------------------------------------------------------------------------------------------------------------------------ p1 schematic
def p1():
    fig, ax = plt.subplots(figsize=(7.2, 3.6)); ax.set_xlim(0, 10); ax.set_ylim(0, 5.0); ax.axis('off')

    def box(x, y, w, h, title, sub, fc, ec):
        ax.add_patch(FancyBboxPatch((x, y), w, h, boxstyle='round,pad=0.02,rounding_size=0.12', fc=fc, ec=ec, lw=1.0))
        ax.text(x + w / 2, y + h - 0.28, title, ha='center', va='center', fontsize=8.5, fontweight='bold'); ax.text(x + w / 2, y + 0.38, sub, ha='center', va='center', fontsize=6.8, color=INK2, linespacing=1.3)

    def arr(p0, p1, txt='', col=INK2, rad=0.0, tx=None, ty=None, ha='center'):
        ax.add_patch(FancyArrowPatch(p0, p1, arrowstyle='-|>', mutation_scale=9, lw=1.0, color=col, connectionstyle=f'arc3,rad={rad}'))
        if txt:
            ax.text(tx if tx is not None else (p0[0] + p1[0]) / 2, ty if ty is not None else (p0[1] + p1[1]) / 2 + 0.1, txt, ha=ha, va='bottom', fontsize=6.8, color=col)
    box(0.1, 3.3, 2.9, 1.2, 'Learned signal  $\\pi_L$', 'frozen\nkeep / switch on halting counts', '#f4f3ef', GRAY)
    box(7.0, 3.3, 2.9, 1.2, 'Learned fleet  $\\pi_F$', 'frozen\neco-approach on SPaT', '#f4f3ef', GRAY)
    box(3.55, 3.3, 2.9, 1.2, 'SPaT provider  $P$', 'TSI: table during yellow,\nstate forecast otherwise', '#e8f0fb', BLUE)
    box(0.1, 0.55, 2.9, 1.35, 'Input map  $g$', 'TSI: also count slow vehicles\n$q=h+A\\,n_{[0.1,2)}+B\\,n_{[2,5)}$', '#e8f0fb', BLUE)
    box(3.55, 0.3, 2.9, 1.0, 'Traffic', 'speeds, queues, approach', '#f4f3ef', GRAY)
    arr((3.0, 3.9), (3.55, 3.9), 'timing', tx=3.27, ty=4.0); arr((6.45, 3.9), (7.0, 3.9), 'SPaT $s$', tx=6.72, ty=4.0)
    arr((8.45, 3.3), (6.45, 0.8), 'slower\neco-approach', col=ORANGE, rad=-0.25, tx=8.75, ty=1.3, ha='left')
    arr((3.55, 0.8), (3.0, 1.1), 'raw\nsensing $z$', rad=0.0, tx=3.27, ty=1.35)
    arr((1.55, 1.9), (1.55, 3.3), 'input\n$o=g(z)$', tx=1.45, ty=2.45, ha='right')
    ax.text(5.25, 2.4, 'closed loop: published timing changes the approach;\na halting-count signal does not see slow cars as demand,\nholds its greens longer, and the forecast\'s target shifts',
            ha='center', va='center', fontsize=6.6, color=ORANGE, style='italic', linespacing=1.3)
    ax.text(0.1, 4.8, 'TSI changes only the two blue interfaces; neither learned policy is retrained.', fontsize=7.5, color=INK2)
    save(fig, 'p1_schematic')


# ------------------------------------------------------------------------------------------------------------------------------- p2 problem
def p2():
    import scripts.CITY_fig_m2_crossplay as M
    Dd = {**M.grid4(), **M.spider()}; conds = [('old light (FT)', BLUE, 'fixed-time signal'), ('learned light, labelled', LGRAY, 'learned signal, no SPaT'),
                                              ('learned light, naive', ORANGE, 'learned signal, old SPaT')]
    fig, axs = plt.subplots(1, 2, figsize=(7.2, 2.7)); xs = np.arange(len(Dd)); w = 0.26
    for j, (ax, ttl, idx) in enumerate(((axs[0], 'A  Fleet fuel vs its base driver (%)', 0), (axs[1], 'B  Fleet time loss vs its base driver (s/veh)', 1))):
        for i, (c, col, lab) in enumerate(conds):
            v = [Dd[f][c][idx] for f in Dd]; p = [x[0] for x in v]; lo = [x[0] - x[1][0] for x in v]; hi = [x[1][1] - x[0] for x in v]
            ax.bar(xs + (i - 1) * w, p, w * 0.92, yerr=[lo, hi], color=col, ecolor=INK2, error_kw=dict(lw=0.8, capsize=2), label=lab)
        ax.axhline(0, color=INK2, lw=0.6); ax.set_xticks(xs); ax.set_xticklabels(list(Dd)); ax.set_title(ttl); ax.grid(axis='y'); ax.set_axisbelow(True)
        if idx == 1:
            ax.axhline(0.5, color=INK2, ls=':', lw=0.8); ax.text(2.45, 0.55, '+0.5 margin', fontsize=6.5, color=INK2, ha='right')
    h, l = axs[0].get_legend_handles_labels(); fig.legend(h, l, loc='upper center', ncol=3, bbox_to_anchor=(0.5, 1.07), fontsize=7.5)
    fig.tight_layout(); save(fig, 'p2_problem')


# ------------------------------------------------------------------------------------------------------------------------------ p3 frontier
def m3nc():
    t = (CS / 'm3nc_20261004/report_m3nc.txt').read_text(); out = {}
    for arm in ('WC5', 'RPC-receiver'):
        blk = t.split(f'  {arm}:')[1]; f = re.search(r'agent fuel % ([-+]\d+\.\d+) \[([-+]\d+\.\d+), ([-+]\d+\.\d+)\]', blk); a = re.search(r'agent TL ([-+]\d+\.\d+) \[([-+]\d+\.\d+), ([-+]\d+\.\d+)\]', blk)
        out[arm] = dict(fuel=dict(v=float(f[1]), lo=float(f[2]), hi=float(f[3])), agentTL=dict(v=float(a[1]), lo=float(a[2]), hi=float(a[3])))
    return out


def p3():
    M = m3nc(); pts = [  # (label, data, colour, filled = fresh / confirmation panel, label offset)
        ('TSI-2 (720–739)', get('tsi2_20261005/report_tsi2_confirm.txt', 'TSI2 - R'), BLUE, True, (-74, -14)),
        ('TSI-2 (760–779)', get('w6_20261005/dca/report_dca.txt', 'TSI2 - R'), BLUE, True, (-74, 8)),
        ('TSI attempt 1', get('tsi_20261005/report_tsi_confirm.txt', 'TSI - R'), BLUE, True, (6, -4)),
        ('TSI, new policies 1', get('w7_20261005/fpr/report_fpr.txt', 'TSI - R'), BLUE, True, (6, 2)),
        ('TSI, new policies 2', get('w8_20261005/fresh2/report_fresh2.txt', 'TSI - R'), BLUE, True, (6, 2)),
        ('F1-B (720–739)', get('tsi2_20261005/report_tsi2_confirm.txt', 'F1B - R'), AQUA, True, (8, 8)),
        ('F1-B (760–779)', get('w6_20261005/h45/report_h45.txt', 'F1B - R'), AQUA, True, (10, -16)),
        ('H4', get('w6_20261005/h45/report_h45.txt', 'H4 - R'), AQUA, True, (10, -1)), ('H5', get('w6_20261005/h45/report_h45.txt', 'H5 - R'), AQUA, True, (-16, 6)),
        ('service alone', get('tsi2_20261005/report_tsi2_confirm.txt', 'HYB - R'), ORANGE, True, (8, 4)),
        ('adapter alone', get('tsi2_20261005/report_tsi2_confirm.txt', 'ADP2 - R'), ORANGE, True, (6, 4)),
        ('DCA2 (audit-invalid port)', get('w7_20261005/dca2/report_dca2.txt', 'DCA2 - R'), ORANGE, True, (6, 2)),
        ('DC-Ada-style affine', get('w6_20261005/dca/report_dca.txt', 'DCA - R'), ORANGE, True, (8, -12)),
        ('state forecast only', get('n4_20261005/report_n4.txt', 'N2q05 - R'), ORANGE, False, (6, 2)),
        ('confidence gate', get('n4_20261005/report_n4.txt', 'G - R'), ORANGE, False, (6, 2)),
        ('predictable splits (CEM)', get('n8_20261005/report_n8.txt', 'CDCm3 vs R'), ORANGE, False, (6, -8)),
        ]  # the time-normalised learned predictable light (W8-3) failed its DEV gate (C-141): no confirmation row exists
    fig, ax = plt.subplots(figsize=(7.2, 4.0)); X0, X1, Y0, Y1 = -1.0, 3.3, -6.2, 3.0
    ax.add_patch(Rectangle((X0, Y0), 0.5 - X0, 0 - Y0, fc='#e8f0fb', ec='none', zorder=0)); ax.text(X0 + 0.05, Y0 + 0.15, 'point-estimate region only; full gate also uses CIs and other limits', fontsize=7, color=BLUE)
    ax.axhline(0, color=INK2, lw=0.6); ax.axvline(0.5, color=INK2, lw=0.6, ls='--')
    pend = []
    for lab, d, col, filled, off in pts:
        if not d or 'fuel' not in d or 'agentTL' not in d:
            pend.append(lab); continue
        x, y = d['agentTL'], d['fuel']
        if x.get('lo') is not None:
            ax.plot([x['lo'], x['hi']], [y['v'], y['v']], color=col, lw=0.9, alpha=0.7, zorder=2)
        if y.get('lo') is not None:
            ax.plot([x['v'], x['v']], [y['lo'], y['hi']], color=col, lw=0.9, alpha=0.7, zorder=2)
        ax.plot(x['v'], y['v'], 'o', ms=6, mfc=col if filled else 'white', mec=col, mew=1.3, zorder=3)
        ax.annotate(lab, (x['v'], y['v']), xytext=off, textcoords='offset points', fontsize=6.6, color=INK)
    off = [f'{k} (fleet time {v["agentTL"]["v"]:+.1f} s, fuel {v["fuel"]["v"]:+.1f} %)' for k, v in (('fixed-window commitment', M['WC5']), ('receiver-triggered commitment', M['RPC-receiver']))]
    note = 'Off scale: ' + '; '.join(off) + '.' + (('  Pending: ' + ', '.join(pend) + '.') if pend else '')
    fig.text(0.01, -0.02, note, fontsize=6.4, color=INK2, ha='left', va='top', wrap=True)
    ax.set_xlim(X0, X1); ax.set_ylim(Y0, Y1); ax.set_xlabel('fleet (agent) time loss vs R (s/veh)'); ax.set_ylabel('fleet fuel vs R (%)'); ax.grid(True); ax.set_axisbelow(True)
    h = [plt.Line2D([], [], marker='o', ls='', color=c, mfc=c, label=l) for c, l in ((BLUE, 'TSI'), (AQUA, 'fleet retraining (more rights)'), (ORANGE, 'other repairs / comparators'))]
    h.append(plt.Line2D([], [], marker='o', ls='', color=INK2, mfc='white', label='hollow: development panel'))
    ax.legend(handles=h, loc='upper left', fontsize=7); ax.set_title('Selected repairs vs R (grid4; different panels; 95% intervals)')
    fig.tight_layout(); save(fig, 'p3_frontier')


# ----------------------------------------------------------------------------------------------------------------------------- p4 mechanism
def armmean(d, prefix, f):
    Rt = rows(d); ks = [k for k in Rt if re.match(rf'^{re.escape(prefix)}(_|$)', k)]
    return float(np.mean([np.mean([r[f] for r in Rt[k].values() if r.get(f) is not None]) for k in ks])) if ks else float('nan')


def p4():
    fig, axs = plt.subplots(1, 3, figsize=(7.6, 2.7), gridspec_kw=dict(wspace=0.42))
    g4 = CS / 'tsi2_20261005/conf'; sp = CS / 'sptsi_20261005/conf'
    arms = (('no SPaT (R)', ('R', 'R'), LGRAY), ('service alone', ('HYB', 'HYBK'), ORANGE), ('TSI', ('TSI2', 'TSIK'), BLUE)); xs = np.arange(2); w = 0.26
    for i, (lab, (a4, asp), col) in enumerate(arms):
        v = [armmean(g4, a4, 'green_mean'), armmean(sp, asp, 'green_mean')]; axs[0].bar(xs + (i - 1) * w, v, w * 0.92, color=col, label=lab)
        for x, vv in zip(xs + (i - 1) * w, v):
            axs[0].text(x, vv + 0.4, f'{vv:.0f}', ha='center', fontsize=6.5, color=INK2)
    axs[0].set_xticks(xs); axs[0].set_xticklabels(['grid4', 'spider']); axs[0].set_title('A  Mean green (s)'); axs[0].legend(fontsize=6.5, loc='upper left'); axs[0].grid(axis='y'); axs[0].set_axisbelow(True)
    Rt = rows(CS / 'tsi_20261005/conf'); FL = ('s213', 's313', 's413', 's513'); S = range(700, 720)
    m = lambda a, t, q: np.mean([Rt[f'{a}_t{t}_{f}'][s][q] for f in FL for s in S])
    for a, col, lab in (('HYB', ORANGE, 'service alone'), ('TSI', BLUE, 'TSI, global adapter')):
        x = [m(a, t, 'green_mean') - m('R', t, 'green_mean') for t in (4, 5, 6, 7, 8)]; y = [m(a, t, 'timeloss_agent') - m('R', t, 'timeloss_agent') for t in (4, 5, 6, 7, 8)]
        axs[1].plot(x, y, 'o', ms=5, color=col, label=lab)
    axs[1].axhline(0.5, color=INK2, ls='--', lw=0.7); axs[1].set_xlabel('green lengthening vs R (s)'); axs[1].set_ylabel('fleet time vs R (s/veh)')
    axs[1].set_title('B  Cost of longer greens'); axs[1].legend(fontsize=6.5, loc='upper left'); axs[1].grid(True); axs[1].set_axisbelow(True)
    X = rep('n2m_20261005/report_x3.txt'); N = rep('n2m_20261005/report_n2m.txt')
    items = [('exact timing,\nfixed schedule', X['RPex - RPsig'], BLUE), ('forecast,\nfixed schedule', X['RPn2 - RPsig'], ORANGE), ('forecast,\nclosed loop', N['N2q05 - R'], ORANGE)]
    for k, (lab, d, col) in enumerate(items):
        axs[2].plot(d['agentTL']['v'], d['fuel']['v'], 'o', ms=6, color=col, mfc=col if k != 1 else 'white', mew=1.3)
        axs[2].annotate(lab, (d['agentTL']['v'], d['fuel']['v']), xytext=(5, -3 if k else 3), textcoords='offset points', fontsize=6.5)
    axs[2].axhline(0, color=INK2, lw=0.6); axs[2].axvline(0.5, color=INK2, ls='--', lw=0.7); axs[2].set_xlabel('fleet time vs ref. (s/veh)'); axs[2].set_ylabel('fleet fuel vs ref. (%)')
    axs[2].set_title('C  Exact vs forecast'); axs[2].set_xlim(-0.8, 3.6); axs[2].grid(True); axs[2].set_axisbelow(True)
    save(fig, 'p4_mechanism')


# ------------------------------------------------------------------------------------------------------------------------------ forests
def forest(blocks, fname, title, xlab_f, xlab_t, margin_t=0.5, margin_f=None, figsize=(7.2, 5.2)):
    rowsl = []
    for head, items in blocks:
        rowsl.append(('H', head, None, None, None))
        rowsl += [('I', lab, d, verdict, note) for lab, d, verdict, note in items]
    n = len(rowsl); fig, axs = plt.subplots(1, 2, figsize=figsize, sharey=True, gridspec_kw=dict(wspace=0.08)); ys = np.arange(n)[::-1]
    for ax, key, xl in ((axs[0], 'fuel', xlab_f), (axs[1], 'agentTL', xlab_t)):
        for y, (kind, lab, d, verdict, note) in zip(ys, rowsl):
            if kind == 'H':
                continue
            if not d or key not in d:
                ax.text(0, y, 'pending', fontsize=6.5, color=GRAY, va='center', ha='center'); continue
            v = d[key]; col = BLUE if verdict in ('PASS', 'met', None) else (ORANGE if verdict in ('FAIL', 'not met') else GRAY)
            if v.get('lo') is not None:
                ax.plot([v['lo'], v['hi']], [y, y], color=col, lw=1.6, solid_capstyle='round')
            ax.plot(v['v'], y, 'o', ms=4.5, color=col, mec='white', mew=0.6, zorder=3)
        ax.axvline(0, color=INK2, lw=0.6)
        if key == 'agentTL' and margin_t is not None:
            ax.axvline(margin_t, color=INK2, lw=0.8, ls='--'); ax.text(margin_t, n - 0.4, f'+{margin_t} margin', fontsize=6.3, color=INK2, ha='left')
        if key == 'fuel' and margin_f is not None:
            ax.axvline(margin_f, color=INK2, lw=0.8, ls=':'); ax.text(margin_f, n - 0.4, f'+{margin_f} NI margin', fontsize=6.3, color=INK2, ha='left')
        ax.set_xlabel(xl); ax.grid(axis='x'); ax.set_axisbelow(True)
    axs[0].set_yticks(ys); axs[0].set_yticklabels([('' if k == 'H' else '   ') + lab for k, lab, *_ in rowsl], fontsize=7)
    for t, (k, *_) in zip(axs[0].get_yticklabels(), rowsl):
        if k == 'H':
            t.set_fontweight('bold')
    for y, (kind, lab, d, verdict, note) in zip(ys, rowsl):
        if kind == 'I' and (verdict or note):
            axs[1].text(1.02, y, f'{verdict or ""}  {note or ""}'.strip(), transform=axs[1].get_yaxis_transform(), fontsize=6.5, color=INK2, va='center')
    fig.suptitle(title, x=0.01, ha='left', fontsize=9, fontweight='bold'); save(fig, fname)


def p5():
    G = rep('gen_20261005/report_gen.txt'); fr = rep('w8_20261005/fresh2/report_fresh2.txt')
    blocks = [
        ('Confirmations, grid4 (lights t4–t8, fleets s213–s513)', [
            ('attempt 1, global adapter (700–719)', get('tsi_20261005/report_tsi_confirm.txt', 'TSI - R'), 'FAIL', 'α .05'),
            ('TSI-2, per-light (720–739)', get('tsi2_20261005/report_tsi2_confirm.txt', 'TSI2 - R'), 'PASS', 'α .025'),
            ('TSI-2, third panel (760–779)', get('w6_20261005/dca/report_dca.txt', 'TSI2 - R'), 'PASS', 'α .05')]),
        ('New, independently trained policies, grid4', [
            ('set 1: t9–t13 × s613–s913 (780–799)', get('w7_20261005/fpr/report_fpr.txt', 'TSI - R'), verdict('w7_20261005/fpr/report_fpr.txt', 'FRESH-POLICY REPLICATION VERDICT'), 'α .05'),
            ('set 2: t14–t18 × s1013–s1313 (800–819)', fr.get('TSI - R'), verdict('w8_20261005/fresh2/report_fresh2.txt', '(1) SECOND FRESH-POLICY'), 'α .05')]),
        ('Scope with the design frozen, grid4', [
            ('demand +25%', get('shift_20261005/report_shift.txt', 'TSI2 - R'), 'met', 'descr.'), ('rule fleet R8', G.get('(a) rule TSI2 - R'), 'met', 'descr.'),
            ('search-fitted fleet R9', G.get('(a) r9 TSI2 - R'), 'met', 'descr.'), ('fleet share 25%', G.get('(c) rho 0.25 TSI2 - R'), 'margin', 'descr.'),
            ('fleet share 75%', G.get('(c) rho 0.75 TSI2 - R'), 'met', 'descr.'), ('fleet share 25%, new policies', fr.get('TSI25 - R25'), verdict('w8_20261005/fresh2/report_fresh2.txt', '(4) FLEET SHARE 0.25 VERDICT'), 'α .05')]),
        ('Other networks', [
            ('rand3: new network, new policies', get('w8_20261005/net3/report_net3.txt', 'TSI - R'), verdict('w8_20261005/net3/report_net3.txt', 'THIRD-NETWORK REPLICATION VERDICT'), 'α .05'),
            ('spider attempt 1', get('sptsi_20261005/report_sptsi.txt', 'TSIK - R'), 'FAIL', 'α .05'),
            ('spider attempt 2', get('sptsi_20261005/report_sptsi2.txt', 'TSIK2 - R'), 'FAIL', 'α .025'),
            ('spider attempt 3', get('w6_20261005/sp3/report_sp3.txt', 'TSIK3 - R'), 'FAIL', 'α .0125'),
            ('spider attempt 4, forecaster refit (W10-5)', get('w10_20261005/sp4/report_sp4.txt', 'TSIK1 - R'), verdict('w10_20261005/sp4/report_sp4.txt', 'SPIDER ATTEMPT 4 VERDICT'), 'α .00625'),
            ('rand3 attempt 2, wider grid (W10-6)', get('w10_20261005/n3b/report_n3b.txt', 'TSIX - R'), verdict('w10_20261005/n3b/report_n3b.txt', 'RAND3 ATTEMPT 2 VERDICT'), 'α .025'),
            ('spider rebuilt with 2 lanes (W10-4)', get('w10_20261005/sp2l/report_sp2l.txt', 'TSIK - R'), verdict('w10_20261005/sp2l/report_sp2l.txt', 'SPIDER-2L VERDICT'), 'α .05')])]
    for _, items in blocks:  # verdicts of pending registered rows come from their reports once they exist
        for i, (lab, d, v, note) in enumerate(items):
            if v is None and d:
                items[i] = (lab, d, 'reported', note)
    forest(blocks, 'p5_evidence', 'TSI against the no-SPaT fallback R across every test (95% intervals; verdicts at each test\'s registered level)',
           'fleet fuel vs R (%)', 'fleet time loss vs R (s/veh)')


def f1b_760():
    try:
        import scripts.CITY_wave2_report_v2 as RR
        A = rows(CS / 'w6_20261005/dca/conf'); B = rows(CS / 'w6_20261005/h45/conf'); L = (4, 5, 6, 7, 8); FP = (('s213', 't4'), ('s313', 't5'), ('s413', 't6'), ('s513', 't7')); S = range(760, 780); out = {}
        for k, key, pct in (('fuel', 'fuel_agent', 1), ('agentTL', 'timeloss_agent', 0)):
            c = np.array([[[(100 * (A[f'TSI2_t{t}_{fl}'][s][key] / B[f'F1B_t{t}_{fl}_{kk}'][s][key] - 1)) if pct else A[f'TSI2_t{t}_{fl}'][s][key] - B[f'F1B_t{t}_{fl}_{kk}'][s][key] for s in S] for fl, kk in FP] for t in L])
            p, ci, up = RR.crossed(c, RR.draws(c.shape)); out[k] = dict(v=p, lo=ci[0], hi=ci[1])
        return out
    except Exception as e:
        print('f1b_760 unavailable', e); return None


def p6():
    T2 = rep('tsi2_20261005/report_tsi2_confirm.txt'); G = rep('gen_20261005/report_gen.txt')
    blocks = [
        ('Same rights (both policies frozen)', [
            ('service alone (HYB)', T2.get('TSI2 - HYB'), None, ''), ('adapter alone (ADP)', T2.get('TSI2 - ADP2'), None, ''),
            ('age-only forecast + adapter', G.get('(b) TSI2 - C2Q'), None, ''),
            ('DC-Ada-style affine adapter', get('w6_20261005/dca/report_dca.txt', 'TSI2 - DCA'), None, 'not faithful'),
            ('DCA2 (audit-invalid port)', get('w7_20261005/dca2/report_dca2.txt', 'TSI2 - DCA2'), 'excluded', 'invalid tuning'),
            ('DCA3, corrected port, matched budget', get('w10_20261005/dca3/report_dca3.txt', 'TSI2 - DCA3'), None, 'no ordering'),
            ('DCA3, four-fold budget (secondary)', get('w10_20261005/dca3/report_dca3.txt', 'TSI2 - DCA3X4'), None, 'TSI better'),
            ('DC-Ada with TSI information, full horizon', get('w12_20261006/dcas/report_dcas.txt', 'TSI2 - DCAS'), None, 'no ordering'),
            ('DC-Ada raw input, full horizon', get('w12_20261006/dcas/report_dcas.txt', 'TSI2 - DCAR'), None, 'no ordering')]),
        ('More rights: the fleet retrained (F1-B)', [
            ('F1-B, panel 720–739', T2.get('TSI2 - F1B'), None, ''), 
            ('F1-B fresh, registered NI (800–819)', get('w8_20261005/fresh2/report_fresh2.txt', 'TSI - F1B'), 'not met', 'fuel NI upper +0.73')])]
    forest(blocks, 'p6_comparators', 'TSI minus each comparator (negative = TSI better; 95% intervals)', 'TSI / comparator, relative fleet fuel (%)',
           'TSI − comparator, fleet time loss (s/veh)', margin_t=None, margin_f=0.5, figsize=(7.2, 4.3))


def p7():
    print('p7 omitted: debug event-head samples are not comparable to grid4 served queries; see code audit')
    return
    f = CS / 'w8_20261005/spdiag/report_spdiag.txt'
    if not f.exists():
        print('p7 pending (W8-1 report missing)'); return
    t = f.read_text(); fig, axs = plt.subplots(1, 3, figsize=(7.2, 2.5))
    mae = {m[1]: float(m[2]) for m in re.finditer(r'K=(\w+) kind= r=: n \d+ \| MAE ([\d.]+)', t)}
    labs = ['grid4\n(published)', 'spider\n2-green', 'spider\n3-green']; vals = [3.02, mae.get('2', np.nan), mae.get('3', np.nan)]
    axs[0].bar(range(3), vals, color=[BLUE, ORANGE, ORANGE], width=0.6)
    for i, v in enumerate(vals):
        axs[0].text(i, v + 0.3, f'{v:.1f}', ha='center', fontsize=7, color=INK2)
    axs[0].set_xticks(range(3)); axs[0].set_xticklabels(labs); axs[0].set_title('A  Forecast MAE at queries (s)'); axs[0].grid(axis='y'); axs[0].set_axisbelow(True)
    o = {m[1]: float(m[2]) for m in re.finditer(r'RLK(\d+): fuel ([-+]\d+\.\d+) %', t)}
    vals = [-6.57, o.get('11', np.nan), o.get('111', np.nan)]
    axs[1].bar(range(3), vals, color=[BLUE, ORANGE, ORANGE], width=0.6)
    for i, v in enumerate(vals):
        axs[1].text(i, v / 2, f'{v:+.1f}', ha='center', fontsize=7, color='white', fontweight='bold')
    axs[1].axhline(0, color=INK2, lw=0.6); axs[1].set_xticks(range(3)); axs[1].set_xticklabels(['grid4', 'spider\nlight 11', 'spider\nlight 111'])
    axs[1].set_title('B  Exact-timing fuel value (%)'); axs[1].grid(axis='y'); axs[1].set_axisbelow(True)
    d4 = {(m[1], m[2]): float(m[3]) for m in re.finditer(r'RLK(\d+) (FULL|K2ONLY|K3ONLY): fuel [-+\d.]+ % \| city [-+\d.]+ \| agent ([-+]\d+\.\d+)', t)}
    ax = axs[2]; arms = [('FULL', 'all signals', BLUE), ('K2ONLY', '2-green only', ORANGE), ('K3ONLY', '3-green only', AQUA)]
    for j, (k, lab, c) in enumerate(arms):
        v = [d4.get((l, k), np.nan) for l in ('11', '111')]
        ax.bar(np.arange(2) + (j - 1) * 0.26, v, width=0.24, color=c, label=lab)
    ax.axhline(0.5, color=GRAY, ls=':', lw=0.8); ax.axhline(0, color=INK2, lw=0.6); ax.set_xticks(range(2)); ax.set_xticklabels(['spider\nlight 11', 'spider\nlight 111'])
    ax.set_title('C  Agent TL vs R by served signals'); ax.legend(fontsize=6.5, frameon=False, loc='upper right'); ax.grid(axis='y'); ax.set_axisbelow(True)
    fig.tight_layout(); save(fig, 'p7_spider')


def p8():
    R = 'w9_20261005/robust/report_robust.txt'; Gp = 'w9_20261005/robust/report_global.txt'; M = 'w9_20261005/mp/report_mp.txt'; r = rep(R); m = rep(M)
    blocks = [
        ('Reference: TSI on the fresh-policy panel (t9–t13 × s613–s913, 780–799)', [
            ('TSI as calibrated (W7-1)', get('w7_20261005/fpr/report_fpr.txt', 'TSI - R'), verdict('w7_20261005/fpr/report_fpr.txt', 'FRESH-POLICY REPLICATION VERDICT'), 'α .05')]),
        ('SPaT channel (fleet side)', [('latency 1 s', r.get('TSI_LAT1 - R'), None, 'descr.'), ('message loss 20%', r.get('TSI_LOSS20 - R'), None, 'descr.'),
                                       ('message loss 50%', r.get('TSI_LOSS50 - R'), None, 'descr.')]),
        ('Adapter sensing (light side)', [('detection 80%', r.get('TSI_DET80 - R'), None, 'descr.'), ('speed noise sd 1 m/s', r.get('TSI_SPN1 - R'), None, 'descr.')]),
        ('Simulator models', [('fuel model PHEMlight5 (vs R under it)', r.get('TSI_EM2 - R_EM2'), None, 'descr.'), ('car-following IDM (vs R under it)', r.get('TSI_IDM - R_IDM'), None, 'descr.')]),
        ('One adapter setting (1, 0.5) for every light', [('fresh-policy panel 1 (secondary)', rep(Gp).get('TSIG - R'), None, 'secondary'),
                                                         ('fresh-policy panel 2 (registered)', section(Gp, '-- (a)').get('TSIG - R'), verdict(Gp, 'CALIBRATION-FREE ADAPTER VERDICT'), 'α .05')]),
        ('MaxPressure signal (fleet-side service only, vs R under MP)', [('table service c2', m.get('C2_MP - R_MP'), None, 'descr.'),
                                                                        ('hybrid service (predicted to pass)', m.get('HYB_MP - R_MP'), verdict(M, 'MECHANISM PREDICTION'), 'α .05')])]
    for _, items in blocks:
        for i, (lab, d, v, note) in enumerate(items):
            if v is None and d:
                items[i] = (lab, d, 'reported', note)
    forest(blocks, 'p8_robust', 'Wave 9: robustness of the frozen TSI design and a published adaptive signal (95% intervals vs the no-SPaT fallback)',
           'fleet fuel vs R (%)', 'fleet time loss vs R (s/veh)', figsize=(7.2, 4.4))


if __name__ == '__main__':
    for fn in (p1, p2, p3, p4, p5, p6, p7, p8):
        try:
            fn()
        except Exception as e:
            print('FIGURE ERROR', fn.__name__, type(e).__name__, e)
