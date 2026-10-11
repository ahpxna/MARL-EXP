#!/usr/bin/env python3
"""M4 stage 2a report (spider DEV 100-109): the rule GLOSA-L∘σ* (tag GLOSALS) vs always-SUMO (a, R8 endpoint via a_pass) and vs σ* (b);
plain GLOSA descriptive; P-M4-2a (human TL) reported."""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402
from scripts.CITY_spatp_report import rows, cmp, a_pass, fmt  # noqa: E402
D = Path(__file__).resolve().parents[1] / 'research/city_sim/m4_20261004/spider'; S = list(range(100, 110))
if __name__ == '__main__':
    Rt = rows(D / 's2a'); dr = R.draws((1, len(S))); out = ['== M4 stage 2a (spider DEV 100-109): rule GLOSA-L∘σ*']
    xa = cmp([Rt['GLOSALS']], Rt['OFF_FT'], S, dr); ok, tel, tel0 = a_pass(xa, [Rt['GLOSALS']], Rt['OFF_FT'], S); xb = cmp([Rt['GLOSALS']], Rt['S0.3_FT'], S, dr)
    okb = xb['fuel'][2] < 0 and xb['tl'][2] < 0.5 and xb['hu'][2] < 0.5
    out += [f'  (a) vs always-SUMO: {fmt(xa)}; teleports {tel:.2f} ({tel0:.2f}) -> {"PASS" if ok else "FAIL"}', f'  (b) vs σ*: {fmt(xb)} -> {"PASS" if okb else "FAIL"}',
            f'  plain GLOSA vs σ*: {fmt(cmp([Rt["GLOSA_FT"]], Rt["S0.3_FT"], S, dr))}', f'  σ* vs always-SUMO: {fmt(cmp([Rt["S0.3_FT"]], Rt["OFF_FT"], S, dr))}']
    t = '\n'.join(out) + '\n'; (D / 'report_m4_s2a.txt').write_text(t); print(t)
