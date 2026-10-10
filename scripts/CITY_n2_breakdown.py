#!/usr/bin/env python3
"""X2 (CHATGPT_AUDITS_CROSSCHECK_20261005; audit M3_DEV_FAILURE §2): forecast error of age-only c2 vs the N2 state model on the N2 validation
episodes (TRAIN seeds 6-7 of n2_20261005/data/k<k>), query-weighted (fleet queries), split by event kind (ttr = green link, ttg = waiting),
realized horizon bucket, and the light's phase class at the query (green of the target / other green / yellow).  Offline; no simulation."""
import json, sys
from pathlib import Path
import numpy as np
import torch
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_n2_fit as NF  # noqa: E402
import scripts.CITY_spat_forecast as FC  # noqa: E402
import scripts.CITY_spat_forecast_c2 as C2  # noqa: E402
import scripts.CITY_spat_forecast_k as FK  # noqa: E402
D = ROOT / 'research/city_sim/n2_20261005'; B = ((0, 5), (5, 15), (15, 30), (30, 1e9))
if __name__ == '__main__':
    out = {}
    for k in (0, 1):
        d = torch.load(D / f'model/n2_k{k}.pt', weights_only=False); net = NF.QNet(d['d']); net.load_state_dict(d['state']); net.eval(); greens = d['greens']; ids = d['ids']
        fs = sorted((D / f'data/k{k}').glob('feat_s*.npz')); va = [f for f in fs if f.stem.endswith(('s6', 's7'))]; tr = [f for f in fs if f not in va]
        X, Y, W, K, M = NF.build(va, greens)
        with torch.no_grad():
            pv = net(torch.as_tensor(X)).numpy()
        T_age = C2.augment(FC.fit([str(f) for f in tr])); w = W - 0.25 + 1e-9; res = {}
        for qi, q in enumerate(NF.QS):
            F = FK.ForecastK(T_age, q)
            ea = np.array([(F.rem(ids[j], ph, s) + FK.OBS) if kind == 0 else F.ttg(ids[j], ph, s, {g}) for (fi, i, j, g, ph, s), kind in zip(M, K)])
            pc = np.array([0 if kind == 0 else (1 if ph in greens[ids[j]] else 2) for (fi, i, j, g, ph, s), kind in zip(M, K)])   # 0 target green now, 1 other green, 2 yellow
            for nm, e in (('age_only', ea - Y), ('state', pv[:, qi] - Y)):
                for kind in (0, 1):
                    for cls in (0, 1, 2):
                        for lo, hi in B:
                            m = (K == kind) & (pc == cls) & (Y >= lo) & (Y < hi)
                            if w[m].sum() > 1:
                                res.setdefault(f'q{q}', {}).setdefault(nm, {})[f'{"ttr" if kind == 0 else "ttg"}|{["target-green", "other-green", "yellow"][cls]}|{lo}-{hi:g}'] = \
                                    (round(float(w[m].sum())), round(float(np.average(np.abs(e[m]), weights=w[m])), 2), round(float(np.average(e[m], weights=w[m])), 2))
        out[f'k{k}'] = res
    (D / 'x2_breakdown.json').write_text(json.dumps(out, indent=1))
    for k, r in out.items():
        for q in r:
            print(f'== {k} {q}  (query weight, MAE, bias)  age-only | state')
            for cell in sorted(r[q]['age_only']):
                a = r[q]['age_only'][cell]; s = r[q]['state'].get(cell)
                print(f'  {cell:28s} w {a[0]:7d}  age MAE {a[1]:6.2f} bias {a[2]:+6.2f} | state MAE {s[1]:6.2f} bias {s[2]:+6.2f}')
