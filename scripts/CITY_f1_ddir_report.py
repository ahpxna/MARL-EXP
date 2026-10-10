#!/usr/bin/env python3
"""F1 D-dir report (PROTOCOL_CITY_F1 §1; written before the run): fleet contribution vs the σ* replay (C-61 S03_rep{k}) per delta; KD-1
(delta 0 == C-61 F0b_orc{k}, bit-identical); P-F1-0 asymmetry per magnitude; the q 0.05 rule (monotone improvement 0 -> -4 -> -8)."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402
from scripts.CITY_spatp_report import rows  # noqa: E402
B = Path(__file__).resolve().parents[1] / 'research/city_sim'; Dd = B / 'f1_20261004/ddir'; H = B / 'spat_pilot_20261004/m3_headroom'; S = [100, 101, 102, 103, 104]
DS = (-8, -4, -2, -1, 0, 1, 2, 4, 8)
if __name__ == '__main__':
    Rt, Rh = rows(Dd), rows(H); dr = R.draws((4, 5)); out = ['== F1 D-dir: exact oracle ttg shifted by delta (open-loop replay of RL-H:k with σ* cars), frozen R10; vs the σ* replay']
    kd = all(abs(Rt['F0b_dP0_k' + str(k)][s][q] - Rh[f'F0b_orc{k}'][s][q]) < 1e-9 for k in range(4) for s in S for q in ('fuel_agent', 'timeloss_agent', 'timeloss_human', 'timeloss'))
    out.append(f'  KD-1 delta 0 == C-61 rows: {"PASS" if kd else "FAIL"}'); res = {}
    for d in DS:
        F = [Rt[f'F0b_d{d:+d}_k{k}'.replace('+', 'P')] for k in range(4)]; B0 = [Rh[f'S03_rep{k}'] for k in range(4)]
        c = lambda key, pct: np.array([[100 * (f[s][key] / b[s][key] - 1) if pct else f[s][key] - b[s][key] for s in S] for f, b in zip(F, B0)])
        x = {k: R.crossed(c(k, k == 'fuel_agent'), dr) for k in ('fuel_agent', 'timeloss_agent', 'timeloss_human', 'timeloss')}; res[d] = x
        tel = np.mean([f[s]['teleports'] for f in F for s in S])
        out.append(f"  delta {d:+d} s: agent fuel % {x['fuel_agent'][0]:+.2f} [{x['fuel_agent'][1][0]:+.2f}, {x['fuel_agent'][1][1]:+.2f}] | agent TL {x['timeloss_agent'][0]:+.2f} | "
                   f"human TL {x['timeloss_human'][0]:+.2f} | city TL {x['timeloss'][0]:+.2f} | teleports/run {tel:.2f}")
    asym = {m: res[m]['fuel_agent'][0] > res[-m]['fuel_agent'][0] for m in (1, 2, 4, 8)}
    out.append(f'  P-F1-0 asymmetry (fuel at +m worse than at -m) per m: {asym} -> {"HOLDS" if all(asym.values()) else "FAILS"}')
    mono = res[-8]['fuel_agent'][0] < res[-4]['fuel_agent'][0] < res[0]['fuel_agent'][0]
    out.append(f'  q 0.05 rule (fuel improves monotonically 0 -> -4 -> -8): {"TRIGGERED: add q 0.05" if mono else "not triggered"}')
    t = '\n'.join(out) + '\n'; (Dd.parent / 'report_f1_ddir.txt').write_text(t); print(t); sys.exit(0 if kd else 1)
