#!/usr/bin/env python3
"""M4 stage 1 report (spider, M4-A3): M4-1 per DQN seed: RLK - FT city TL on DEV 100-109 (paired by seed; bootstrap over traffic, 2000 draws,
one-sided 95 % upper < 0); teleports / unfinished reported."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402
D = Path(__file__).resolve().parents[1] / 'research/city_sim/m4_20261004/spider/dev'; S = list(range(100, 110))
if __name__ == '__main__':
    rows = lambda t: {r['seed']: r for r in json.loads((D / f'{t}.json').read_text())['rows']}
    ft = rows('FT'); out = ['== M4 stage 1 (spider, period 2.0, LightRLK halting reward, 120 episodes): learned light vs FT, DEV 100-109, all-SUMO traffic']
    out.append(f"  FT: city TL {np.mean([ft[s]['timeloss'] for s in S]):.2f}, teleports {sum(ft[s]['teleports'] for s in S)}, unfinished {sum(ft[s]['unfinished'] for s in S)}"); ok = []
    for sd in (11, 111):
        r = rows(f'RLK_sp{sd}'); c = np.array([[r[s]['timeloss'] - ft[s]['timeloss'] for s in S]]); x = R.crossed(c, R.draws((1, len(S))))
        p = x[2] < 0; ok.append(p)
        out.append(f"  RLK_sp{sd} - FT city TL {x[0]:+.2f} [{x[1][0]:+.2f}, {x[1][1]:+.2f}] (upper {x[2]:+.2f}) -> {'PASS' if p else 'FAIL'} | teleports {sum(r[s]['teleports'] for s in S)}, unfinished {sum(r[s]['unfinished'] for s in S)}")
    out.append(f"  M4-1 (both seeds): {'PASS' if all(ok) else 'FAIL'}"); t = '\n'.join(out) + '\n'; (D.parent / 'report_m4_stage1.txt').write_text(t); print(t)
