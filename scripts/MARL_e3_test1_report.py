#!/usr/bin/env python3
"""Auditor's test 1 reading (read-only): the clean closed-loop baseline (selector v8, floored normaliser, closed loop
v6 --guard none, <actor>/cl_v8_direct) against the same actor's prefix in the same run, and next to the original
unguarded v2 sel_bid_resp (the same model recipe with the defective normaliser, <actor>/cl_v3_direct).
Per actor: waiting change vs the prefix (%, selector inits averaged per episode, paired by episode), traffic-seed
cluster bootstrap; v8 - original sel_bid_resp (pp); edits per episode; bytes vs the prefix; the largest |z| per step
(t < 7 and t >= 7).  Self-checks (abort): both manifests COMPLETE; prefix and mp2 rows identical in the two runs; same
episodes.  Evidence class: descriptive development (panel 901-916 was used before).
Usage: MARL_e3_test1_report.py --actor DIR... --out X.json
"""
from __future__ import annotations
import argparse, json, re, sys
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts.MARL_e3_panel_report import boot_cluster
from scripts.MARL_e3_guard_compare import rows


def fam(R, f, eps, pq):
    ms = sorted({k[1] for k in R if k[1].startswith(f + '/')})
    return ms, np.array([np.mean([100 * (R[(e, m)]['queue_sum'] - pq[e]) / pq[e] for m in ms]) for e in eps])


def main(a):
    out = {}; lines = []
    for A in map(Path, a.actor):
        N, O = rows(A / 'cl_v8_direct'), rows(A / 'cl_v3_direct')
        eps = sorted({k[0] for k in N})
        if eps != sorted({k[0] for k in O}):
            raise SystemExit(f'SELF-CHECK FAIL: {A}: different episodes')
        for e in eps:
            for m in ('prefix', 'mp2'):
                if (e, m) in N and (N[(e, m)]['queue_sum'], N[(e, m)]['bytes']) != (O[(e, m)]['queue_sum'], O[(e, m)]['bytes']):
                    raise SystemExit(f'SELF-CHECK FAIL: {A}: {e} {m} differs between runs')
        seed = {e: int(re.match(r'seed(\d+)_', e).group(1)) for e in eps}; pq = {e: N[(e, 'prefix')]['queue_sum'] for e in eps}
        cl = lambda v: {s: np.array([x for e, x in zip(eps, v) if seed[e] == s]) for s in sorted(set(seed.values()))}
        ms, vn = fam(N, 'legal_bid_resp', eps, pq); _, vo = fam(O, 'sel_bid_resp', eps, pq)
        steps = [s for e in eps for m in ms for s in N[(e, m)]['steps']]
        z_early = [s[3] for s in steps if s[0] < 7]; z_late = [s[3] for s in steps if s[0] >= 7]
        r = dict(v8_pct=float(vn.mean()), v8_ci=boot_cluster(cl(vn)), original_sel_bid_resp_pct=float(vo.mean()), original_ci=boot_cluster(cl(vo)),
                 v8_minus_original_pp=float((vn - vo).mean()), v8_minus_original_ci=boot_cluster(cl(vn - vo)),
                 edits=float(np.mean([N[(e, m)]['edits'] for e in eps for m in ms])),
                 bytes_vs_prefix=float(np.mean([N[(e, m)]['bytes'] - N[(e, 'prefix')]['bytes'] for e in eps for m in ms])),
                 worse_episode_share=float(np.mean(vn > 0)), max_abs_z_t_lt_7=float(np.max(z_early)), max_abs_z_t_ge_7=float(np.max(z_late)),
                 median_abs_z_t_ge_7=float(np.median(z_late)), inits=len(ms), episodes=len(eps))
        if 'mp2' in {k[1] for k in N}:
            _, vm = fam({(e, 'mp2/x'): N[(e, 'mp2')] for e in eps}, 'mp2', eps, pq); r['mp2_pct'] = float(vm.mean())
        out[str(A)] = r
        lines.append(f"{A.parent.name}/{A.name}: v8 legal_bid_resp vs prefix {r['v8_pct']:+.2f}% [{r['v8_ci'][0]:+.2f},{r['v8_ci'][1]:+.2f}] (worse in {r['worse_episode_share']:.2f} of episodes) "
                     f"| original sel_bid_resp {r['original_sel_bid_resp_pct']:+.2f}% | v8 - original {r['v8_minus_original_pp']:+.2f}pp [{r['v8_minus_original_ci'][0]:+.2f},{r['v8_minus_original_ci'][1]:+.2f}] "
                     f"| edits {r['edits']:.1f}/26, bytes +{r['bytes_vs_prefix']:.0f} | max|z| t<7 {r['max_abs_z_t_lt_7']:.0f}, t>=7 {r['max_abs_z_t_ge_7']:.0f} (median {r['median_abs_z_t_ge_7']:.1f})"
                     + (f" | mp2 {r['mp2_pct']:+.2f}%" if 'mp2_pct' in r else ''))
    Path(a.out).write_text(json.dumps(out, indent=1)); print('\n'.join(lines), flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('--actor', nargs='+', required=True); p.add_argument('--out', required=True)
    main(p.parse_args())
