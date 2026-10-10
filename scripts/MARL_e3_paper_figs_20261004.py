#!/usr/bin/env python3
"""Figures for the legacy-view paper (claim table research/papers/audits/PAPER_E3_LEGACY_VIEW_CLAIM_TABLE_20261004.md; 04/10/2026 wake 4).
Every number is READ from the reports that the claim table cites (no recomputation, so the paper's single CI rule is inherited):
  fig_e7_arms.pdf     E7 layout D and C: system / OLD / NEW gain vs ZTEAM with 95 % CIs per arm (w2/report_e7.txt), delivered bytes annotated
  fig_e13_forest.pdf  E13: per-OLD-agent gain vs ALLOLD with Bonferroni CIs, layouts D and C (w2/report_e13.json) — shows WHY per-agent NI fails
  fig_e12_coverage.pdf E12: view equality vs coverage contingency and failures by step (e12/report.json)
Output: research/papers/_tex/figs_e3_legacy/."""
import json, re
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

W = Path('research/marl_budget/e3_wave_20261003'); OUT = Path('research/papers/_tex/figs_e3_legacy'); OUT.mkdir(parents=True, exist_ok=True)
NUM = r'([+-]?\d+\.\d+)'


def e7():
    txt = (W / 'w2' / 'report_e7.txt').read_text().splitlines(); blocks = {}; lay = None
    for line in txt:
        m = re.match(r'-- E7 layout (\w)', line)
        if m:
            lay = m.group(1); blocks[lay] = []; continue
        if lay and ' | ' in line and not line.startswith('arm |'):
            parts = [p.strip() for p in line.split('|')]
            if len(parts) < 5:
                continue
            vals = []
            for p in parts[1:4]:
                mm = re.match(NUM + r' \[' + NUM + r', ' + NUM + r'\]', p)
                vals.append(tuple(float(x) for x in mm.groups()) if mm else None)
            if all(vals):
                blocks[lay].append((parts[0], vals, parts[4]))
    fig, axes = plt.subplots(1, 2, figsize=(11, 4.2), sharey=True)
    for ax, lay in zip(axes, ('D', 'C')):
        rows = blocks.get(lay, [])
        for k, (arm, vals, byt) in enumerate(rows):
            for j, (lab, col) in enumerate((('system', 'k'), ('OLD', 'tab:red'), ('NEW', 'tab:blue'))):
                p, lo, hi = vals[j]; y = k + (j - 1) * 0.22
                ax.errorbar(p, y, xerr=[[p - lo], [hi - p]], fmt='o', color=col, ms=3, capsize=2, label=lab if k == 0 else None)
        ax.set_yticks(range(len(rows))); ax.set_yticklabels([f'{a}  ({b} B/ep)' for a, _, b in rows], fontsize=7)
        ax.axvline(0, color='grey', lw=0.6); ax.set_title(f'E7 layout {lay}' + (' (primary)' if lay == 'D' else '')); ax.set_xlabel('gain vs ZTEAM (%)')
    axes[0].legend(fontsize=7, loc='lower right'); fig.tight_layout(); fig.savefig(OUT / 'fig_e7_arms.pdf'); plt.close(fig)
    return {k: len(v) for k, v in blocks.items()}


def e13():
    d = json.loads((W / 'w2' / 'report_e13.json').read_text())
    fig, axes = plt.subplots(1, 2, figsize=(9, 3.4), sharey=False)
    for ax, lay in zip(axes, ('D', 'C')):
        r = d[lay]['U2/EMU_OLD|E13-1']
        for k, (a, g, lo, hi) in enumerate(zip(r['agents'], r['gain'], r['lo'], r['hi'])):
            ax.errorbar(g, k, xerr=[[g - lo], [hi - g]], fmt='o', color='tab:red', ms=3, capsize=2)
        ax.set_yticks(range(len(r['agents']))); ax.set_yticklabels([f'agent {a}' for a in r['agents']], fontsize=7)
        ax.axvline(0, color='grey', lw=0.6); ax.axvline(-0.5, color='grey', lw=0.6, ls='--')
        ax.set_title(f'E13 layout {lay}: OLD agents, EMU vs all-OLD'); ax.set_xlabel('per-agent gain (%), Bonferroni 95 % CI')
    fig.tight_layout(); fig.savefig(OUT / 'fig_e13_forest.pdf'); plt.close(fig)


def e12():
    d = json.loads((W / 'e12' / 'report.json').read_text()); T = d['both']['T']
    fig, ax = plt.subplots(figsize=(4.2, 3.2))
    cells = [('covered\n& equal', T['cov_eq']), ('covered\n& different', T['cov_neq']), ('uncovered\n& equal', T['unc_eq']), ('uncovered\n& different', T['unc_neq'])]
    ax.bar(range(4), [max(c[1], 0.5) for c in cells], color=['tab:green', 'tab:red', 'tab:red', 'tab:green']); ax.set_yscale('log')
    for k, c in enumerate(cells):
        ax.text(k, max(c[1], 0.5) * 1.3, str(c[1]), ha='center', fontsize=8)
    ax.set_xticks(range(4)); ax.set_xticklabels([c[0] for c in cells], fontsize=7); ax.set_ylabel('OLD agent-steps (log)')
    ax.set_title('E12: emulated view = K1 view  ⇔  coverage', fontsize=9); fig.tight_layout(); fig.savefig(OUT / 'fig_e12_coverage.pdf'); plt.close(fig)


if __name__ == '__main__':
    print('E7 rows per layout', e7()); e13(); e12(); print('wrote', sorted(p.name for p in OUT.glob('*.pdf')))
