#!/usr/bin/env python3
"""PROTOCOL_E3_CLOSED_LOOP_GUARD_20260928.md reading (read-only): original closed-loop panel vs its guarded rerun
(closed loop v6 --guard support) on the SAME actor, checkpoints, episodes and arguments.

Per actor and selector family (selector inits averaged per episode): waiting change vs the same actor's prefix in the
original run and in the guarded run (%, paired by episode), and guarded - original (percentage points); traffic-seed
cluster bootstrap (both loads of a seed together); edits per episode; bytes vs prefix; guarded steps per episode by
reason (t < t_min, |z| > z_max).  Self-checks (abort): both manifests COMPLETE; the prefix and mp2 rows are identical
in the two runs (the guard never touches them); the same episodes and selector inits in both.
Usage: MARL_e3_guard_compare.py --panel cl_v3_direct --actor DIR ... --out X.json
"""
from __future__ import annotations
import argparse, json, re, sys
from collections import defaultdict
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts.MARL_e3_panel_report import boot_cluster


def rows(d):
    man = json.loads((d / 'manifest.json').read_text())
    if man.get('status') != 'COMPLETE':
        raise SystemExit(f'SELF-CHECK FAIL: {d} not COMPLETE')
    return {(r['episode'], r['method']): r for r in json.loads((d / 'rows.json').read_text())}


def main(a):
    out = dict(panel=a.panel, actors={}); lines = []
    for A in map(Path, a.actor):
        O, G = rows(A / a.panel), rows(A / f'{a.panel}_v6g')
        if set(O) != set(G):
            raise SystemExit(f'SELF-CHECK FAIL: {A}: different (episode, method) sets')
        for k in O:
            if k[1] in ('prefix', 'mp2') and (O[k]['queue_sum'], O[k]['bytes']) != (G[k]['queue_sum'], G[k]['bytes']):
                raise SystemExit(f'SELF-CHECK FAIL: {A}: {k} differs between runs')
        eps = sorted({k[0] for k in O}); seed = {e: int(re.match(r'seed(\d+)_', e).group(1)) for e in eps}
        pq = {e: O[(e, 'prefix')]['queue_sum'] for e in eps}; pb = {e: O[(e, 'prefix')]['bytes'] for e in eps}
        fams = sorted({k[1].split('/')[0] for k in O if '/' in k[1]}); res = {}
        for f in fams:
            ms = sorted({k[1] for k in O if k[1].startswith(f + '/')})
            po = np.array([np.mean([100 * (O[(e, m)]['queue_sum'] - pq[e]) / pq[e] for m in ms]) for e in eps])
            pg = np.array([np.mean([100 * (G[(e, m)]['queue_sum'] - pq[e]) / pq[e] for m in ms]) for e in eps])
            cl = lambda v: {s: np.array([x for e, x in zip(eps, v) if seed[e] == s]) for s in sorted(set(seed.values()))}
            steps = [s for e in eps for m in ms for s in G[(e, m)]['steps']]
            n_ep = len(eps) * len(ms)
            res[f] = dict(original_pct=float(po.mean()), original_ci=boot_cluster(cl(po)), guarded_pct=float(pg.mean()), guarded_ci=boot_cluster(cl(pg)),
                          guarded_minus_original_pp=float((pg - po).mean()), guarded_minus_original_ci=boot_cluster(cl(pg - po)),
                          edits_original=float(np.mean([O[(e, m)]['edits'] for e in eps for m in ms])),
                          edits_guarded=float(np.mean([G[(e, m)]['edits'] for e in eps for m in ms])),
                          bytes_original=float(np.mean([O[(e, m)]['bytes'] - pb[e] for e in eps for m in ms])),
                          bytes_guarded=float(np.mean([G[(e, m)]['bytes'] - pb[e] for e in eps for m in ms])),
                          guarded_steps_per_episode=dict(t_lt_tmin=sum(s[2] == 't<t_min' for s in steps) / n_ep, z_gt_zmax=sum(s[2] == 'z>z_max' for s in steps) / n_ep),
                          wanted_edits_at_guarded_steps_per_episode=sum(s[5] for s in steps if s[1]) / n_ep, inits=len(ms), episodes=len(eps))
            r = res[f]
            lines.append(f"{A.parent.name}/{A.name} {a.panel} {f:13s} original {r['original_pct']:+.2f}% [{r['original_ci'][0]:+.2f},{r['original_ci'][1]:+.2f}] "
                         f"guarded {r['guarded_pct']:+.2f}% [{r['guarded_ci'][0]:+.2f},{r['guarded_ci'][1]:+.2f}] diff {r['guarded_minus_original_pp']:+.2f}pp "
                         f"[{r['guarded_minus_original_ci'][0]:+.2f},{r['guarded_minus_original_ci'][1]:+.2f}] | edits {r['edits_original']:.1f}->{r['edits_guarded']:.1f} "
                         f"| guarded steps/ep t<7 {r['guarded_steps_per_episode']['t_lt_tmin']:.1f} z>50 {r['guarded_steps_per_episode']['z_gt_zmax']:.1f}")
        out['actors'][str(A)] = res
    Path(a.out).write_text(json.dumps(out, indent=1)); print('\n'.join(lines), flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('--panel', required=True); p.add_argument('--actor', nargs='+', required=True)
    p.add_argument('--out', required=True); main(p.parse_args())
