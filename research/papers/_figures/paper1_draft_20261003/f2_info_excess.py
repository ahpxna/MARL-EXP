"""F2  information vs excess split of a frozen receiver's change when its channel changes.  Convention: POSITIVE = WORSE for the
receiver (RI: test MSE change; C0: regret change; E3: minus the change in gain vs Z, % points).  Each bar is a waterfall: the
information segment (Bayes / matched-receiver floor change) from 0, then the excess segment; the diamond is the total, dots are
seeds' totals.
(a) RI linear-Gaussian age-role testbed (research/marl_budget/ri_age_role_20261002/results.json, 5 seeds per lambda): receiver
    trained on ages U{4..7}, deployed on U{0..3}; Bayes MSE recomputed with the formula of
    /Users/phanan/Documents/ChatGPT/CIG-AMF/research/catchup/ri_age_role_bayes_check_20261003.py (copied below, read-only).
(b) C0 exact (wake-1 g1_c0.json in research/marl_budget/e3_train_deploy_matrix_20261003/g1_g3_wake1/): frozen Z_ACT car, ACT -> L;
    floor = exact Bayes table Z*_L regret on the same panel; seeds 0-4 (FT, EXT, CUT) / 0-2 (A1-A6).
(c, d) E3 matched-receiver PROXY (the 'information' term = matched receiver on the new channel minus matched receiver on the old
    one): UP = K1-trained receiver K1 -> iid, DOWN = iid-trained receiver iid -> K1; every finished panel that has the three cells,
    paired by seed (matrix.json cells; test D 4601, fallback RELAY 4801/4901, emulation PLAIN 5101 from extra_data.json)."""
import json
import numpy as np
from common import *
fig = plt.figure(figsize=(13.5, 8.6)); gs = fig.add_gridspec(2, 2, width_ratios=[0.8, 1.2], hspace=0.5, wspace=0.18)
dump = {}
def wf(ax, x, a, b, w=0.36, tot_seeds=None):
    """waterfall: information bar (0 -> a) on the left half, excess bar (a -> a + b) on the right half, diamond = total."""
    h = w / 2
    ax.bar(x - h / 2, a, width=h, color=BLUE, edgecolor=SURF, linewidth=1.0, zorder=2)
    ax.bar(x + h / 2, b, width=h, bottom=a, color=ORANGE, edgecolor=SURF, linewidth=1.0, zorder=2)
    ax.plot([x - h, x + h], [a, a], color=INK2, lw=0.6, ls=':', zorder=3)
    if tot_seeds is not None:
        ax.scatter(np.full(len(tot_seeds), x + h / 2) + np.linspace(-h / 3, h / 3, len(tot_seeds)), tot_seeds, s=8, color=INK2, zorder=3, linewidths=0)
    ax.scatter([x + h / 2], [a + b], marker='D', s=30, color=INK, zorder=4, edgecolors=SURF, linewidths=0.8)
# ---------------- (a) RI
r, pv, rv = .98, .09, .0025; p = pv / (1 - r * r); ts = np.arange(16, 100_000 + 16)
vt = p + (1 - p) * (r ** (2 * (ts + 1)))
def window(a):
    out = []
    for d in range(a, a + 4):
        vold = p + (1 - p) * (r ** (2 * (ts - d + 1))); q = vt - (r ** (2 * d)) * vold * vold / (vold + rv); out.append(float(np.mean(2 * q / (1 + q))))
    return float(np.mean(out))
b_old, b_new = window(4), window(0)
RI = json.loads((MB / 'ri_age_role_20261002/results.json').read_text()); assert RI['source_sha256'] == sha_file(ROOT / 'scripts/RI_age_role_testbed.py')
ax = fig.add_subplot(gs[0, 0]); dump['RI'] = dict(bayes_old=b_old, bayes_new=b_new)
for i, lam in enumerate(RI['lams']):
    seeds = RI['res'][str(lam)]
    old = np.array([v['silent'] * (1 - v['plain']['4']) for v in seeds.values()]); new = np.array([v['silent'] * (1 - v['plain']['0']) for v in seeds.values()])
    tot = new - old; info = b_new - b_old; wf(ax, i, info, tot.mean() - info, tot_seeds=tot)
    dump['RI'][str(lam)] = dict(info=info, excess=float(tot.mean() - info), total=float(tot.mean()), total_seeds=tot.tolist(), frozen_old=float(old.mean()), frozen_new=float(new.mean()))
    ax.text(i + 0.09, max(tot.max(), 0) + 0.1, f'{tot.mean():+.2f}', ha='center', fontsize=8, color=INK)
ax.axhline(0, color=INK2, lw=0.8); ax.set_xticks(range(4), [f'λ = {l:g}' for l in RI['lams']]); ax.set_ylim(-0.65, 3.0)
ax.set_ylabel('Δ test MSE (fresher ages; + = worse)'); ax.set_title('(a) RI testbed: trained on ages 4–7, deployed on 0–3', loc='left', fontsize=9.5)
ax.text(0.02, 0.97, f'Bayes MSE {b_old:.3f} → {b_new:.3f} at every λ\n(information term {b_new - b_old:+.3f})', transform=ax.transAxes, va='top', fontsize=7.5, color=INK2)
# ---------------- (b) C0 (two scales: inside the trained phase range / support exit)
C0 = [r_ for r_ in json.loads((MB / 'e3_train_deploy_matrix_20261003/g1_g3_wake1/g1_c0.json').read_text()) if r_['kind'] == 'Z']
C = {r_['L']: r_ for r_ in C0}; dump['C0'] = {}
sub = gs[0, 1].subgridspec(1, 2, width_ratios=[5, 4], wspace=0.28)
for k, (order, title) in enumerate(((['FT', 'A6', 'A2', 'A1', 'CUT'], '(b) C0 exact: car trained on light ACT, light → L\n     phase lengths inside the trained range'),
                                    (['A4', 'A3', 'A5', 'EXT'], '     phases longer than trained\n     (support exit; note the scale)'))):
    ax = fig.add_subplot(sub[0, k])
    for i, L in enumerate(order):
        c = C[L]; tot = np.array(c['dexc_seeds']) + c['dfloor']; wf(ax, i, c['dfloor'], c['dexc'], w=0.5, tot_seeds=tot)
        dump['C0'][L] = dict(info=c['dfloor'], excess=c['dexc'], total=c['dtot'], total_seeds=tot.tolist(), n=c['n'])
        ax.text(i + 0.12, max(tot.max(), c['dfloor'], 0) + (0.25 if k == 0 else 1.5), f"{c['dtot']:+.2f}", ha='center', fontsize=7.5, color=INK)
    ax.axhline(0, color=INK2, lw=0.8); ax.set_xticks(range(len(order)), [f'{L}\n(n={C[L]["n"]})' for L in order])
    if k == 0: ax.set_ylabel('Δ regret vs ACT (+ = worse)'); ax.set_ylim(-3.7, 2.4)
    ax.set_title(title, loc='left', fontsize=9.5)
# ---------------- (c, d) E3 proxy
mat = json.loads((MB / 'e3_train_deploy_matrix_20261003/matrix.json').read_text())['cells']; X = json.loads((OUT / 'extra_data.json').read_text())['cells']
cell = {}
for c in mat: cell[(c['grid'], c['panel'], c['fam'], c['K'])] = dict(zip(c['seeds'], c['per_seed']))
for k, v in X.items():
    parts = k.split('|'); g, p_, fam, K = parts[:4]; arm = parts[4] if len(parts) > 4 else 'plain'
    if arm in ('plain', 'RELAY', 'PLAIN'): cell[(g, int(p_), fam, K)] = dict(zip(v['seeds'], v['per_seed']))
CAGE = {'3x3': 'relay6Cage_st', '4x4': 'relayCage_st'}
def split(g, p_, direction):
    ck1, cage = 'relayCK1_st', CAGE[g]
    need = [(ck1, 'K1'), (ck1, 'iid'), (cage, 'iid')] + ([(cage, 'K1')] if direction == 'DOWN' else [])
    if any((g, p_, f, K) not in cell for f, K in need): return None
    S = sorted(set.intersection(*[set(cell[(g, p_, f, K)]) for f, K in need]))
    G = lambda f, K: np.array([cell[(g, p_, f, K)][s] for s in S])
    if direction == 'UP':   # K1-trained receiver: K1 -> iid
        info = -(G(cage, 'iid') - G(ck1, 'K1')); exc = -(G(ck1, 'iid') - G(cage, 'iid'))
    else:                   # iid-trained receiver: iid -> K1
        info = -(G(ck1, 'K1') - G(cage, 'iid')); exc = -(G(cage, 'K1') - G(ck1, 'K1'))
    return S, info, exc
SRC = {4801: 'FB', 4901: 'FB', 5101: 'EMU', 4601: 'test D'}
for j, g in enumerate(('3x3', '4x4')):
    ax = fig.add_subplot(gs[1, j]); panels = sorted({k[1] for k in cell if k[0] == g}); xt = []; xl = []; x = 0; dump[f'E3_{g}'] = {}
    for p_ in panels:
        got = False
        for dname, off in (('UP', -0.2), ('DOWN', 0.2)):
            r_ = split(g, p_, dname)
            if r_ is None: continue
            S, info, exc = r_; wf(ax, x + off, info.mean(), exc.mean(), w=0.34, tot_seeds=info + exc); got = True
            xt.append(x + off); xl.append('U' if dname == 'UP' else 'D')
            dump[f'E3_{g}'][f'{p_}|{dname}'] = dict(seeds=S, info=float(info.mean()), excess=float(exc.mean()), total=float((info + exc).mean()),
                                                     info_seeds=info.tolist(), excess_seeds=exc.tolist())
        if got:
            ax.text(x, -0.13, f'{p_}' + (f'\n{SRC[p_]}' if p_ in SRC else ''), transform=ax.get_xaxis_transform(), ha='center', va='top', fontsize=7, color=INK)
            x += 1
    ax.axhline(0, color=INK2, lw=0.8); ax.set_xticks(xt, xl, fontsize=7); ax.tick_params(axis='x', length=0); ax.set_ylim(*((-1.6, 8.6) if g == '3x3' else (-1.2, 17.8)))
    ax.set_ylabel('−Δ gain vs Z (% points; + = worse)')
    ax.set_title(f'(c) E3 3x3, matched-receiver proxy, per panel' if g == '3x3' else '(d) E3 4x4, matched-receiver proxy, per panel', loc='left', fontsize=9.5)
from matplotlib.patches import Patch
from matplotlib.lines import Line2D
fig.legend(handles=[Patch(color=BLUE, label='information term (Bayes floor / matched receiver)'), Patch(color=ORANGE, label='excess (frozen receiver beyond the floor)'),
                    Line2D([], [], marker='D', color=INK, ls='', label='total change'), Line2D([], [], marker='o', color=INK2, ls='', ms=3, label='seeds (total)')],
           loc='upper center', ncol=4, bbox_to_anchor=(0.5, 0.995), fontsize=8.5)
fig.text(0.5, 0.445, 'E3: U = K1-trained receiver deployed K1 → iid (upgrade);  D = iid-trained receiver deployed iid → K1 (downgrade).\nPanel = first traffic seed of the 64-seed panel; FB = plain RELAY arm of the fallback panel; EMU = PLAIN arm of the emulation panel.',
         ha='center', fontsize=8, color=INK2)
save(fig, 'F2_information_vs_excess')
json.dump(dump, open(OUT / 'F2_data.json', 'w'), indent=1, default=float)
# consistency with wake-1 g1_marl.json
W1 = json.loads((MB / 'e3_train_deploy_matrix_20261003/g1_g3_wake1/g1_marl.json').read_text())
for name, (g, p_) in {'4x4 train-match': ('4x4', 4201), '3x3 train-match': ('3x3', 3201), '3x3 mixed-channel': ('3x3', 3801)}.items():
    V = np.array(W1[name]['per_seed']); d = dump[f'E3_{g}']
    print(name, 'wake-1 UP info/excess', -V[:, 4].mean().round(4), -V[:, 5].mean().round(4), '| F2', round(d[f'{p_}|UP']['info'], 4), round(d[f'{p_}|UP']['excess'], 4),
          '|| DOWN', -V[:, 7].mean().round(4), -V[:, 8].mean().round(4), '| F2', round(d[f'{p_}|DOWN']['info'], 4), round(d[f'{p_}|DOWN']['excess'], 4))
print('RI bayes', b_old, b_new)
