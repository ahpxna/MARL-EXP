#!/usr/bin/env python3
"""W21-D report (PROTOCOL_CITY_WAVE21_20261015, Amendment W21-D): median (SERVEg50) vs 0.1 quantile (SERVEg) published on the Midtown map,
each against the shadow (= R) on the same cells; served-answer accounting by CITY_w10_diag.match with the KW21-C0 offsets (0, 0).
Usage: CITY_w21d_report.py <W21-C dir>"""
import json, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w10_diag as WD  # noqa: E402
from scripts.CITY_w6_validation import rows  # noqa: E402
D = Path(sys.argv[1]); Rt = rows(D); ST = WD.states(ROOT / 'research/city_sim/net/midtown_full.net.xml'); DAYS = [0, 1, 2, 3, 4]
FAM = {'AH': [34, 35, 36, 37, 38], 'B2D': [59, 60, 61, 62, 63]}; rng = np.random.default_rng(0)


def boot(M):
    bs = [M[np.ix_(rng.integers(0, M.shape[0], M.shape[0]), rng.integers(0, M.shape[1], M.shape[1]))].mean() for _ in range(2000)]
    return f'{M.mean():+.2f} [{np.percentile(bs, 2.5):+.2f}, {np.percentile(bs, 97.5):+.2f}]'


def diff(a, b, ks, m, pct=False):
    return boot(np.array([[100 * (Rt[f'{a}_t{k}'][s][m] / Rt[f'{b}_t{k}'][s][m] - 1) if pct else Rt[f'{a}_t{k}'][s][m] - Rt[f'{b}_t{k}'][s][m] for s in DAYS] for k in ks]))


def acct(tag, ks):
    E, K = [], []
    for k in ks:
        for s in DAYS:
            kd, p, r = WD.match(D / 'served' / f'{tag}_t{k}_served_s{s}.npz', D / 'rec' / f'{tag}_t{k}' / f'phases_s{s}.npz', ST); E.append(p - r); K.append(kd)
    e, kd = np.concatenate(E), np.concatenate(K)
    return f'MAE {np.mean(np.abs(e)):.2f} (ttg {np.mean(np.abs(e[kd == 0])):.2f}, ttr {np.mean(np.abs(e[kd == 1])):.2f}), bias ttr {np.mean(e[kd == 1]):+.2f}, ttg {np.mean(e[kd == 0]):+.2f}'


out = ['== W21-D: the published quantile on the Midtown map (fleet s1413, days 0-4; MT-E setting)']
for f, ks in FAM.items():
    out += [f'-- {f}',
            f'  q 0.1 (SERVEg) - shadow: agent TL {diff("SERVEg", "SHADOWg", ks, "timeloss_agent")} s/veh, agent fuel {diff("SERVEg", "SHADOWg", ks, "fuel_agent", True)} %, human TL {diff("SERVEg", "SHADOWg", ks, "timeloss_human")}',
            f'  q 0.5 (SERVEg50) - shadow: agent TL {diff("SERVEg50", "SHADOWg", ks, "timeloss_agent")} s/veh, agent fuel {diff("SERVEg50", "SHADOWg", ks, "fuel_agent", True)} %, human TL {diff("SERVEg50", "SHADOWg", ks, "timeloss_human")}',
            f'  q 0.5 - q 0.1: agent TL {diff("SERVEg50", "SERVEg", ks, "timeloss_agent")} s/veh, agent fuel {diff("SERVEg50", "SERVEg", ks, "fuel_agent", True)} %',
            f'  served answers q 0.1: {acct("SERVEg", ks)}', f'  served answers q 0.5: {acct("SERVEg50", ks)}']
(D / 'report_w21d.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
