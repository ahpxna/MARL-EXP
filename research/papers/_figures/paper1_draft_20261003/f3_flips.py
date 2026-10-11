"""F3  decision-level cross-channel flips on IDENTICAL states (research/marl_budget/e3_crosschannel_flip_20261003/<grid>_s<s>/summary.json;
PROTOCOL_E3_CROSSCHANNEL_FLIP_20261003.md; Z drives, receivers are evaluated under each channel; acceptability = teacher A_0.25;
development episodes 901-904 x 8/16).  NF(A->B) = P(acceptable under A, not under B); PF the reverse.  NF(A->B) = PF(B->A) exactly,
so the downgrade column is the mirror image of the upgrade column (shown for completeness)."""
import json
import numpy as np
from common import *
D = MB / 'e3_crosschannel_flip_20261003'
RECV = {'3x3': [('relay6Cage_st', 'iid-trained\n(6Cage)'), ('relayCK1_st', 'K1-trained\n(CK1)'), ('relayCK2_st', 'K2-trained\n(CK2)'), ('relayMIX_st', 'MIX'), ('relayMIX2_st', 'MIX2')],
        '4x4': [('relayCage_st', 'iid-trained\n(Cage)'), ('relayCK1_st', 'K1-trained\n(CK1)')]}
SEEDS = {'3x3': range(5), '4x4': range(10)}
fig, axes = plt.subplots(2, 2, figsize=(12, 7.2), gridspec_kw=dict(width_ratios=[5, 2.6], hspace=0.55, wspace=0.22), sharey='row')
dump = {}; mirror_err = 0.0
for j, grid in enumerate(('3x3', '4x4')):
    S = {s: json.loads((D / f'{grid}_s{s}' / 'summary.json').read_text()) for s in SEEDS[grid]}
    for s in SEEDS[grid]: manifest(D / f'{grid}_s{s}')
    for i, (pair, lab) in enumerate((('const1->iid', 'upgrade: K = 1 → iid'), ('iid->const1', 'downgrade: iid → K = 1'))):
        ax = axes[i, j]
        for r, (fam, name) in enumerate(RECV[grid]):
            nf = np.array([S[s][fam]['pairs'][pair]['nf'] for s in SEEDS[grid]]); pf = np.array([S[s][fam]['pairs'][pair]['pf'] for s in SEEDS[grid]])
            inv = 'iid->const1' if pair == 'const1->iid' else 'const1->iid'
            mirror_err = max(mirror_err, float(np.max(np.abs(nf - np.array([S[s][fam]['pairs'][inv]['pf'] for s in SEEDS[grid]])))))
            for off, v, col, nm in ((-0.17, nf, ORANGE, 'NF'), (0.17, pf, BLUE, 'PF')):
                jit = np.linspace(-0.07, 0.07, len(v))
                ax.scatter(r + off + jit, v, s=14, color=col, alpha=0.55, linewidths=0, zorder=3)
                ax.plot([r + off - 0.12, r + off + 0.12], [v.mean(), v.mean()], color=col, lw=2.4, zorder=4, solid_capstyle='round')
            net = pf - nf
            ax.text(r, 0.198, f'net {net.mean():+.3f}\n{int((net < 0).sum())}/{len(net)} < 0', ha='center', fontsize=7, color=INK2)
            dump[f'{grid}|{fam}|{pair}'] = dict(nf_mean=float(nf.mean()), pf_mean=float(pf.mean()), net_mean=float(net.mean()), nf_seeds=nf.tolist(), pf_seeds=pf.tolist(),
                                               btc_mean=float(np.mean([S[s][fam]['pairs'][pair]['btc'] for s in SEEDS[grid]])))
        ax.set_xticks(range(len(RECV[grid])), [n for _, n in RECV[grid]], fontsize=8); ax.set_ylim(0, 0.225)
        ax.set_title(f'{grid}: {lab}  (seeds 0–{max(SEEDS[grid])})', loc='left', fontsize=9.5)
        if j == 0: ax.set_ylabel('share of decision states')
from matplotlib.lines import Line2D
fig.legend(handles=[Line2D([], [], color=ORANGE, lw=2.4, marker='o', ms=4, label='NF: acceptable before, not after (negative flip)'),
                    Line2D([], [], color=BLUE, lw=2.4, marker='o', ms=4, label='PF: not acceptable before, acceptable after (positive flip)')],
           loc='upper center', ncol=2, bbox_to_anchor=(0.5, 1.0), fontsize=8.5)
fig.text(0.01, -0.03, 'Same world states under both channels (Z drives; receivers are evaluated, not executed); acceptable = teacher A_0.25 on the full fresh view.  '
         'Dots = seeds, bar = mean.\nNF(A→B) = PF(B→A) exactly (max |difference| %.1e), so the downgrade row mirrors the upgrade row.' % mirror_err, fontsize=7, color=INK2)
save(fig, 'F3_crosschannel_flips')
json.dump(dump, open(OUT / 'F3_data.json', 'w'), indent=1)
for k, v in dump.items():
    print(f'{k:34s} NF {v["nf_mean"]:.3f} PF {v["pf_mean"]:.3f} net {v["net_mean"]:+.3f} BTC {v["btc_mean"]:.3f}')
print('mirror max err', mirror_err)
