#!/usr/bin/env python3
"""Report for MARL_e3_zero_loss_truncation.py (direction (b), oracle diagnostic).  Read-only on COMPLETE run dirs.

Per actor and arm: bytes saved (1 - sum bytes / sum reference bytes), relative waiting change (sum queue / sum reference
queue - 1) with a paired bootstrap 95% CI over episodes (2000 resamples, seed 0), the share of episodes with IDENTICAL
waiting, and the first-divergence step.  For the lifetime arms (H = end, identical by construction): the share of steps
with a drop, packets dropped per step.  Veto analysis on the tail H = end run: at each step, the shortest stream the
CURRENT-step check alone accepts (from the recorded pass vector) against the one the lifetime check accepts; a veto is
a step where the current-step check would have allowed a shorter stream.
"""
from __future__ import annotations
import argparse, json
from pathlib import Path
import numpy as np


def boot(x, n=2000, seed=0):
    x = np.asarray(x, float); r = np.random.default_rng(seed)
    m = [x[r.integers(0, len(x), len(x))].mean() for _ in range(n)]
    return float(x.mean()), float(np.quantile(m, 0.025)), float(np.quantile(m, 0.975))


def main(a):
    root = Path(a.root); out = {}; lines = []
    for d in sorted(p for p in root.iterdir() if p.is_dir()):
        if not (d / 'manifest.json').exists():
            lines.append(f'{d.name}: not complete, skipped'); continue
        rows = json.loads((d / 'rows.json').read_text()); arms = list(rows[0]['arms'])
        res = dict(episodes=len(rows), ref_bytes_per_step=float(np.mean([np.mean(r['ref']['bytes']) for r in rows])), arms={})
        for arm in arms:
            qb = [r['arms'][arm]['queue_sum'] / r['ref']['queue_sum'] - 1 for r in rows]
            saved = 1 - sum(r['arms'][arm]['bytes_sum'] for r in rows) / sum(r['ref']['bytes_sum'] for r in rows)
            ident = float(np.mean([r['arms'][arm]['queue_sum'] == r['ref']['queue_sum'] for r in rows]))
            div = [r['arms'][arm]['first_divergence'] for r in rows]
            steps = [s for r in rows for s in r['arms'][arm]['steps']]
            drop = [(s['b0'] - s['bytes']) / 25.0 for s in steps]
            res['arms'][arm] = dict(bytes_saved=saved, waiting_change=boot(qb), identical_share=ident,
                                    first_divergence_median=(float(np.median([x for x in div if x is not None])) if any(x is not None for x in div) else None),
                                    step_drop_share=float(np.mean([x > 0 for x in drop])), packets_dropped_per_step=float(np.mean(drop)))
        if 'tail_Hend' in arms:
            ve, dl = [], []
            for r in rows:
                for s in r['arms']['tail_Hend']['steps']:
                    Lloc = next(L for L, ok in enumerate(s['pass0']) if ok) if any(s['pass0']) else s['L0']
                    Lend = s['bytes'] // 25 if s['bytes'] % 25 == 0 else None
                    if Lend is None:
                        continue
                    ve.append(Lloc < Lend); dl.append(Lend - Lloc)
            res['veto'] = dict(steps=len(ve), veto_share=float(np.mean(ve)), extra_packets_when_vetoed=float(np.mean([x for x in dl if x > 0])) if any(x > 0 for x in dl) else 0.0)
        out[d.name] = res
        lines.append(f'== {d.name}: {len(rows)} episodes, reference {res["ref_bytes_per_step"]:.0f} B/step')
        for arm, v in res['arms'].items():
            w = v['waiting_change']
            lines.append(f'  {arm:18s} bytes saved {v["bytes_saved"]:6.3f} | waiting {w[0]:+.4f} [{w[1]:+.4f}, {w[2]:+.4f}] | identical {v["identical_share"]:.2f} | '
                         f'steps with a drop {v["step_drop_share"]:.2f}, packets dropped/step {v["packets_dropped_per_step"]:.2f}' +
                         (f' | first divergence (median step) {v["first_divergence_median"]:.0f}' if v['first_divergence_median'] is not None else ''))
        if 'veto' in res:
            lines.append(f'  veto (tail): the current-step check alone would allow a shorter stream at {res["veto"]["veto_share"]:.3f} of {res["veto"]["steps"]} steps '
                         f'(by {res["veto"]["extra_packets_when_vetoed"]:.2f} packets when it does)')
    Path(a.out + '.json').write_text(json.dumps(out, indent=1)); Path(a.out + '.txt').write_text('\n'.join(lines) + '\n'); print('\n'.join(lines))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--root', default='research/marl_budget/e3_zero_loss_20260929'); p.add_argument('--out', default='research/marl_budget/e3_zero_loss_report_20260929')
    main(p.parse_args())
