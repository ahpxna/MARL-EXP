#!/usr/bin/env python3
"""M4 stage 4a report (Amendment M4-A6; written before the stage-4a panel).  spider 1000-1019, lights RLK_sp11 / sp111, fleet = the rule.
R = stage-3 labelled rows (F0_RLK<k>_labelled == σ*, KM4-3c); WCK5 = commitment fleet rows; WCK5sh = WCK-5 light with SPaT none (rule == σ*).
M3-1 agent fuel % WCK5 vs R (NEGATIVE REPLICATED iff one-sided lower > 0; positive iff upper < 0); M3-4clean = WCK5sh - R; M3-3clean = WCK5 - WCK5sh."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402
from scripts.CITY_spatp_report import rows  # noqa: E402
import scripts.CITY_m2_report as M2  # noqa: E402
SP = Path(__file__).resolve().parents[1] / 'research/city_sim/m4_20261004/spider'; S = list(range(1000, 1020)); K = (11, 111); M2.S = S
if __name__ == '__main__':
    A, B = rows(SP / 's4/eval'), rows(SP / 's3/eval'); dr = R.draws((len(K), len(S))); cube, fm, txt = M2.cube, M2.fm, M2.txt
    W = [A[f'WCK5_RLK{k}'] for k in K]; Sh = [A[f'WCK5sh_RLK{k}'] for k in K]; Rr = [B[f'F0_RLK{k}_labelled'] for k in K]
    out = ['== M4 stage 4a (spider 1000-1019): fixed-window commitment W = 5 on RLK, frozen rule fleet; vs R (no SPaT, rule = σ*)']
    m1 = fm(cube(W, Rr, 'fuel_agent', True), dr); v = 'NEGATIVE REPLICATED' if m1[3] > 0 else ('POSITIVE (contradicts grid4; not a claim)' if m1[2] < 0 else 'NOT SHOWN BETTER')
    out.append(f'  M3-1 agent fuel % {txt(m1)} (lo {m1[3]:+.2f}, up {m1[2]:+.2f}) -> {v}')
    for k_, nm in (('timeloss', 'city'), ('timeloss_agent', 'agent'), ('timeloss_human', 'human')):
        x = fm(cube(W, Rr, k_, False), dr); out.append(f'  M3-2 {nm} TL {txt(x)} (up {x[2]:+.2f})')
    lc = fm(cube(Sh, Rr, 'fuel_agent', True), dr); lct = fm(cube(Sh, Rr, 'timeloss', False), dr); fc = fm(cube(W, Sh, 'fuel_agent', True), dr)
    named = lc[3] > 0 and fc[2] < 0
    out.append(f'  M3-4clean light cost: agent fuel % {txt(lc)} (lo {lc[3]:+.2f}), city TL {txt(lct)} | M3-3clean fleet contribution: agent fuel % {txt(fc)} (up {fc[2]:+.2f}) -> reason {"NAMED" if named else "NOT established"}')
    sc = [json.loads((SP / f's4/eval/WCK5_RLK{k}_wck.json').read_text())['per_seed'] for k in K]; ps = [x for c in sc for x in c.values()]
    bad_e = sum(v_ for x in ps for k_, v_ in x['exec_err'].items() if float(k_) != 0); bad_o = sum(v_ for x in ps for k_, v_ in x['onset_err'].items() if float(k_) != 0)
    out.append(f'  commitments {sum(x["commits"] for x in ps)}, green-end errors {bad_e}, onset errors {bad_o}, wrong-green onsets {sum(x["onset_wrong_green"] for x in ps)}; '
               f'valid SPaT share {sum(x["spat_valid"] for x in ps) / max(1, sum(x["spat_total"] for x in ps)):.3f}')
    tel = {t: np.mean([r['teleports'] for r in A[t].values()]) for t in A}; out.append(f'  teleports/run: {tel}')
    t = '\n'.join(out) + '\n'; (SP / 'report_m4_s4a.txt').write_text(t); print(t)
