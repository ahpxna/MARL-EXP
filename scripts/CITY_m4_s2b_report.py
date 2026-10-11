#!/usr/bin/env python3
"""M4 stage 2b report (PROTOCOL_CITY_M4_ARTERIAL_20261004 Amendment M4-A4; written before any 2b evaluation).  The R9 rule of
CITY_lane_d_report.py applied on the spider network:
  pilot    spider/s2b/eval_dev (DEV 100-109): ESLD_s1 vs always-SUMO (a, a_pass) and vs GLOSA-L∘σ* = GLOSALS (d''): fuel upper < 0 AND agent
           TL upper < +0.5 AND human TL upper < +0.5 AND teleports <= rule + 1.  GATE = (a) AND (d'') -> eval_dev/GATE_PASS.
  confirm  spider/s2b/eval_1000 (fresh 1000-1019, only if GATE_PASS): pooled ESLD_s2..s5 (crossed): (a), (b) vs σ* 0.3, (d''); per-seed (d'').
M1-spider: (a), (b) and (d'') on the confirmation."""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402
from scripts.CITY_spatp_report import rows, cmp, a_pass, fmt, labels  # noqa: E402
from scripts.CITY_lane_d_report import dpp  # noqa: E402

D = Path(__file__).resolve().parents[1] / 'research/city_sim/m4_20261004/spider/s2b'
DEV, NEW = list(range(100, 110)), list(range(1000, 1020))


def main(stage):
    sub, seeds = ('eval_dev', DEV) if stage == 'pilot' else ('eval_1000', NEW)
    Rt = rows(D / sub); off, sst, gl = Rt['OFF_FT'], Rt['S0.3_FT'], Rt['GLOSALS']
    F = [Rt['ESLD_s1']] if stage == 'pilot' else [Rt[f'ESLD_s{s}'] for s in (2, 3, 4, 5)]; dr = R.draws((len(F), len(seeds)))
    out = [f'== M4 2b {stage} (spider): GLOSA-LD∘σ* (R9 4-parameter search), FT, traffic {seeds[0]}-{seeds[-1]}',
           f'  GLOSA-L∘σ* (rule) vs σ*: {fmt(cmp([gl], sst, seeds, R.draws((1, len(seeds)))))}']
    xa = cmp(F, off, seeds, dr); ok, tel, tel0 = a_pass(xa, F, off, seeds); xb = cmp(F, sst, seeds, dr); okb = xb['fuel'][2] < 0 and xb['tl'][2] < 0.5 and xb['hu'][2] < 0.5
    xd = cmp(F, gl, seeds, dr); okd, tl1, tl0 = dpp(xd, F, gl, seeds)
    out += [f'  (a) vs always-SUMO: {fmt(xa)}; teleports {tel:.2f} ({tel0:.2f}) -> {"PASS" if ok else "FAIL"}',
            f'  (b) vs σ* 0.3: {fmt(xb)} -> {"PASS" if okb else "FAIL"}',
            f"  (d'') vs GLOSA-L∘σ*: {fmt(xd)}; teleports {tl1:.2f} ({tl0:.2f}) -> {'PASS' if okd else 'FAIL'}"]
    labels(out, '  σ labels', F, Rt, seeds)
    if stage == 'pilot':
        out.append(f'M4 2b PILOT GATE ((a) AND (d\'\')): {"PASS" if (ok and okd) else "FAIL"}')
        if ok and okd:
            (D / sub / 'GATE_PASS').write_text('1\n')
    else:
        per = [dpp(cmp([f], gl, seeds, R.draws((1, len(seeds)))), [f], gl, seeds)[0] for f in F]
        out.append(f"  per-seed (d''): {per}")
        out.append(f'  M1-SPIDER ((a), (b), (d\'\') on the confirmation): {"MET" if (ok and okb and okd) else "NOT MET"}')
    txt = '\n'.join(out) + '\n'; (D / f'report_m4_s2b_{stage}.txt').write_text(txt); print(txt)


if __name__ == '__main__':
    main(sys.argv[1])
