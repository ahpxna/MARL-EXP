#!/usr/bin/env python3
"""F1 KSL-2 and G1 (PROTOCOL_CITY_F1_SALTLAKE_20261008): <dir> holds per-site rows FT_<site>, RLK<k>_<site> (CITY_m4s_tsi_eval, all SUMO
cars) on the DEV days.  KSL-2: FT teleports and unfinished = 0 on the first 3 DEV days.  G1 per site: RL - FT city time loss, crossed bootstrap
over light seed (11, 12) and day (B 2000, one-sided 95 % upper < 0 -> PASS).  Usage: CITY_sl_gate_report.py <dir> [alpha]"""
import json, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
from scripts.CITY_w6_validation import rows  # noqa: E402
from scripts.CITY_sl_build import days  # noqa: E402
D = Path(sys.argv[1]); ALPHA = float(sys.argv[2]) if len(sys.argv) > 2 else 0.05; Rt = rows(D); out = [f'== F1 light gate (DEV days, alpha {ALPHA})']; ok_all = {}
for site in ('400sX200w', 'stateXuniversity'):
    if f'FT_{site}' not in Rt:
        continue
    ft = Rt[f'FT_{site}']; S = [d.timetuple().tm_yday for d in days(site, 'dev') if d.timetuple().tm_yday in ft]   # smoke: the days run
    k2 = all(ft[s]['teleports'] == 0 and ft[s]['unfinished'] == 0 for s in S[:3])
    L = [k for k in (11, 12) if f'RLK{k}_{site}' in Rt]; d = np.array([[Rt[f'RLK{k}_{site}'][s]['timeloss'] - ft[s]['timeloss'] for s in S] for k in L])
    rng = np.random.default_rng(2026); bs = []
    for _ in range(2000):
        li = rng.integers(0, len(L), len(L)); si = rng.integers(0, len(S), len(S)); bs.append(d[np.ix_(li, si)].mean())
    up = float(np.percentile(bs, 100 * (1 - ALPHA))); g1 = up < 0; ok_all[site] = g1
    out.append(f'{site}: KSL-2 {"PASS" if k2 else "FAIL"}; FT city TL {np.mean([ft[s]["timeloss"] for s in S]):.2f}; '
               + '; '.join(f'RLK{k} {np.mean([Rt[f"RLK{k}_{site}"][s]["timeloss"] for s in S]):.2f}' for k in L)
               + f' | RL - FT {d.mean():+.2f} (upper {up:+.2f}); teleports/run RL {np.mean([Rt[f"RLK{k}_{site}"][s]["teleports"] for k in L for s in S]):.2f} -> G1 {"PASS" if g1 else "FAIL"}')
(D / 'report_gate.txt').write_text('\n'.join(out) + '\n'); (D / 'gate.json').write_text(json.dumps(ok_all)); print('\n'.join(out))
