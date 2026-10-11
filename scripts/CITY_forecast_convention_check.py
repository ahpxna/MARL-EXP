#!/usr/bin/env python3
"""Forecast timing-convention check (04/10/2026, C-70 item 1).  OFFLINE on recorded RL-H phase traces (m2b/traces, P[i] = phase observed at
time i + 1, spent[i] = getSpentDuration at time i + 1).  The CITY_spat_forecast formulas are applied with the TRUE duration G of the current
green occurrence in place of the quantile, so model error is removed and only the timing convention is tested:
  green link (served by the current green g):  ttr_formula = (G - spent) + OBS         vs  observed yellow onset - t
  other link during green g:                    ttg_formula = (G - spent) + YELLOW + OBS vs  observed green onset of the other green - t
  during yellow (spent s_y):                    ttg_formula = (YELLOW - s_y) + OBS      vs  observed green onset - t
G = number of observed seconds of the occurrence (the fit's run length).  Prints the error distribution (formula - observed) per branch."""
import sys
from collections import Counter
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_spat_forecast as FC  # noqa: E402

P0 = ROOT / 'research/city_sim/spat_pilot_20261004/m2b/traces'; OBS, Y = FC.OBS, FC.YELLOW
err = dict(ttr=Counter(), ttg_green=Counter(), ttg_yellow=Counter())
for f in sorted(P0.glob('rlh*_s*.npz')):
    z = np.load(f, allow_pickle=True); ids = [str(x) for x in z['ids']]; P, S = z['phases'], z['spent']; G = FC.greens_of(ids)
    for j, tid in enumerate(ids):
        col = P[:, j]; runs = FC.runs(col); gs = G[tid]
        for r_i, (ph, st, ln, complete) in enumerate(runs):
            if not complete or r_i + 2 >= len(runs):
                continue
            end_obs = st + ln                                    # index of the first non-ph observation -> observed time end_obs + 1
            if ph in gs:
                for i in range(st, st + ln):
                    t = i + 1; s = float(S[i, j])
                    err['ttr'][round((ln - s) + OBS - ((end_obs + 1) - t), 6)] += 1
                    nxt = runs[r_i + 2]                          # green -> yellow -> next green
                    err['ttg_green'][round((ln - s) + Y + OBS - ((nxt[1] + 1) - t), 6)] += 1
            else:
                for i in range(st, st + ln):
                    t = i + 1; s = float(S[i, j]); nxt = runs[r_i + 1]
                    err['ttg_yellow'][round((Y - s) + OBS - ((nxt[1] + 1) - t), 6)] += 1
for k, c in err.items():
    n = sum(c.values()); print(f'{k:11s} n {n}: formula - observed -> ' + ', '.join(f'{v:+g}: {100 * m / n:.2f} %' for v, m in c.most_common(5)))
