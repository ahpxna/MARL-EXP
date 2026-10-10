#!/usr/bin/env python3
"""R8 report (Amendment R8; written before any R8 evaluation).  Dirs under research/city_sim/spat_pilot_20261004/lane:
  dev      eval_dev: GLOSA-L∘σ* (tag GLOSALS) on the development teleport seeds 100, 420, 424, 425, 426; P8-1 = fleet teleports 0 on every
           seed (compared with GLOSA∘σ* rows in sbase/eval_select and sbase/eval_420).
  confirm  eval_430: fresh traffic 430-449: GLOSALS (a) vs always-SUMO (a_pass of the B pilot), (b) vs σ* (fuel upper < 0, agent TL upper
           < +0.5, human TL upper < +0.5) = P8-2; P8-3 fuel point <= -6 % vs σ*; σ labels; descriptive rows GLOSAL_FT (0.5 base, lane-aware),
           GLOSAS (σ* base, no lane awareness), GLOSA_FT (plain) vs σ*, with teleports per fleet."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402
from scripts.CITY_spatp_report import rows, cmp, a_pass, fmt, labels  # noqa: E402

P = Path(__file__).resolve().parents[1] / 'research/city_sim/spat_pilot_20261004'; D = P / 'lane'
DEV = [100, 420, 424, 425, 426]; NEW = list(range(430, 450))


def main(stage):
    out = []
    if stage == 'dev':
        L = rows(D / 'eval_dev')['GLOSALS']; G = {**rows(P / 'sbase/eval_select')['GLOSAS'], **rows(P / 'sbase/eval_420')['GLOSAS']}
        out.append('== R8 dev: fleet teleports per seed, GLOSA-L∘σ* vs GLOSA∘σ* (development seeds)')
        for s in DEV:
            out.append(f'  {s}: GLOSA-L∘σ* {L[s]["teleports"]} (agent TL {L[s]["timeloss_agent"]:.2f}, fuel {L[s]["fuel_agent"]:.0f})   '
                       f'GLOSA∘σ* {G[s]["teleports"]} (agent TL {G[s]["timeloss_agent"]:.2f}, fuel {G[s]["fuel_agent"]:.0f})')
        out.append(f'  P8-1: {"HOLDS" if all(L[s]["teleports"] == 0 for s in DEV) else "FAILS"}')
    else:
        Rt = rows(D / 'eval_430'); seeds = NEW; dr = R.draws((1, len(seeds))); off, sst = Rt['OFF_FT'], Rt['S0.3_FT']; F = [Rt['GLOSALS']]
        out.append('== R8 confirmation: GLOSA-L∘σ* (fixed rule), FT, fresh traffic 430-449')
        xa = cmp(F, off, seeds, dr); ok, tel, tel0 = a_pass(xa, F, off, seeds); xb = cmp(F, sst, seeds, dr)
        okb = xb['fuel'][2] < 0 and xb['tl'][2] < 0.5 and xb['hu'][2] < 0.5
        out += [f'  (a) vs always-SUMO: {fmt(xa)}; teleports {tel:.2f} ({tel0:.2f}) -> {"PASS" if ok else "FAIL"}',
                f'  (b) vs σ* 0.3: {fmt(xb)} -> {"PASS" if okb else "FAIL"}']
        labels(out, '  σ labels', F, Rt, seeds)
        for t in ('GLOSAL_FT', 'GLOSAS', 'GLOSA_FT'):
            out.append(f'  descriptive {t} vs σ*: {fmt(cmp([Rt[t]], sst, seeds, dr))}; teleports/run {np.mean([Rt[t][s]["teleports"] for s in seeds]):.2f}')
        out.append(f'  teleports/run: GLOSALS {np.mean([Rt["GLOSALS"][s]["teleports"] for s in seeds]):.2f}, σ* {np.mean([sst[s]["teleports"] for s in seeds]):.2f}, '
                   f'always-SUMO {np.mean([off[s]["teleports"] for s in seeds]):.2f}')
        out.append(f'  P8-2: {"HOLDS" if (ok and okb) else "FAILS"} ((a) {"PASS" if ok else "FAIL"}, (b) {"PASS" if okb else "FAIL"}); '
                   f'P8-3: {"HOLDS" if xb["fuel"][0] <= -6 else "FAILS"} (fuel point {xb["fuel"][0]:+.2f} %)')
    txt = '\n'.join(out) + '\n'; (D / f'report_lane_{stage}.txt').write_text(txt); print(txt)


if __name__ == '__main__':
    main(sys.argv[1])
