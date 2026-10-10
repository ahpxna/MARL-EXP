#!/usr/bin/env python3
"""R9 report (Amendment R9; written before any R9 evaluation).  Dirs under research/city_sim/spat_pilot_20261004/lane_d:
  pilot    eval_select (SELECT 100-104): ESLD_s1 vs always-SUMO (a), σ* (b), GLOSA-L∘σ* = GLOSALS (d''): fuel upper < 0 AND agent TL upper
           < +0.5 AND human TL upper < +0.5 AND teleports <= base + 1.  GATE = (a) AND (d'') -> eval_select/GATE_PASS.
  confirm  eval_450 (fresh 450-469, only if GATE_PASS): pooled ESLD_s2..s5 (fleet-seed x traffic): (a), (b), (d''); per-seed (d'').
M1 rule: (a), (b) and (d'') on the confirmation.  Fuel primary; the training J is never used."""
import sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402
from scripts.CITY_spatp_report import rows, cmp, a_pass, fmt, labels  # noqa: E402

D = Path(__file__).resolve().parents[1] / 'research/city_sim/spat_pilot_20261004/lane_d'
NEW = list(range(450, 470))


def dpp(x, F, base, seeds):
    tel = np.mean([f[s]['teleports'] for f in F for s in seeds]); tel0 = np.mean([base[s]['teleports'] for s in seeds])
    return x['fuel'][2] < 0 and x['tl'][2] < 0.5 and x['hu'][2] < 0.5 and tel <= tel0 + 1, tel, tel0


def main(stage):
    sub, seeds = ('eval_select', R.SEL) if stage == 'pilot' else ('eval_450', NEW)
    Rt = rows(D / sub); off, sst, gl = Rt['OFF_FT'], Rt['S0.3_FT'], Rt['GLOSALS']
    F = [Rt['ESLD_s1']] if stage == 'pilot' else [Rt[f'ESLD_s{s}'] for s in (2, 3, 4, 5)]; dr = R.draws((len(F), len(seeds)))
    out = [f'== R9 {stage}: GLOSA-LD∘σ* (learned, 4-parameter search), FT, traffic {seeds[0]}-{seeds[-1]}',
           f'  GLOSA-L∘σ* (rule) vs σ*: {fmt(cmp([gl], sst, seeds, R.draws((1, len(seeds)))))}']
    xa = cmp(F, off, seeds, dr); ok, tel, tel0 = a_pass(xa, F, off, seeds); xb = cmp(F, sst, seeds, dr); okb = xb['fuel'][2] < 0 and xb['tl'][2] < 0.5 and xb['hu'][2] < 0.5
    xd = cmp(F, gl, seeds, dr); okd, tl1, tl0 = dpp(xd, F, gl, seeds)
    out += [f'  (a) vs always-SUMO: {fmt(xa)}; teleports {tel:.2f} ({tel0:.2f}) -> {"PASS" if ok else "FAIL"}',
            f'  (b) vs σ* 0.3: {fmt(xb)} -> {"PASS" if okb else "FAIL"}',
            f"  (d'') vs GLOSA-L∘σ*: {fmt(xd)}; teleports {tl1:.2f} ({tl0:.2f}) -> {'PASS' if okd else 'FAIL'}"]
    labels(out, '  σ labels', F, Rt, seeds)
    if stage == 'pilot':
        out.append(f'R9 PILOT GATE ((a) AND (d\'\')): {"PASS" if (ok and okd) else "FAIL"}')
        if ok and okd:
            (D / sub / 'GATE_PASS').write_text('1\n')
    else:
        per = [dpp(cmp([f], gl, seeds, R.draws((1, len(seeds)))), [f], gl, seeds)[0] for f in F]
        out.append(f"  per-seed (d''): {per}")
        out.append(f'  M1 RULE ((a), (b), (d\'\') on the confirmation): {"MET" if (ok and okb and okd) else "NOT MET"}')
    txt = '\n'.join(out) + '\n'; (D / f'report_lane_d_{stage}.txt').write_text(txt); print(txt)


if __name__ == '__main__':
    main(sys.argv[1])
