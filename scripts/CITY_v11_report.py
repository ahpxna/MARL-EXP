#!/usr/bin/env python3
"""R10 report (Amendment R10; written before any R10 evaluation).  Dirs under research/city_sim/spat_pilot_20261004/fleets_v11:
  pilot    eval_select (SELECT 100-104): per seed L11_s13 / L11_s113: (a) vs always-SUMO, (b) vs σ*, (d'') vs GLOSA-L∘σ* (GLOSALS);
           GATE: >= 1 pilot seed passes (a) AND (d'') -> eval_select/GATE_PASS.
  confirm  eval_450 (fresh 450-469, only if GATE_PASS): pooled L11_s213..s513: (a), (b), (d''); per-seed (d''); M1 rule.
Fuel primary; rewards are never used."""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402
from scripts.CITY_spatp_report import rows, cmp, a_pass, fmt, labels  # noqa: E402
from scripts.CITY_lane_d_report import dpp  # noqa: E402

D = Path(__file__).resolve().parents[1] / 'research/city_sim/spat_pilot_20261004/fleets_v11'; NEW = list(range(450, 470))


def block(out, name, F, Rt, seeds):
    off, sst, gl = Rt['OFF_FT'], Rt['S0.3_FT'], Rt['GLOSALS']; dr = R.draws((len(F), len(seeds)))
    xa = cmp(F, off, seeds, dr); ok, tel, tel0 = a_pass(xa, F, off, seeds); xb = cmp(F, sst, seeds, dr); okb = xb['fuel'][2] < 0 and xb['tl'][2] < 0.5 and xb['hu'][2] < 0.5
    xd = cmp(F, gl, seeds, dr); okd, t1, t0 = dpp(xd, F, gl, seeds)
    out += [f'  {name} (a) vs always-SUMO: {fmt(xa)}; teleports {tel:.2f} ({tel0:.2f}) -> {"PASS" if ok else "FAIL"}',
            f'  {name} (b) vs σ*: {fmt(xb)} -> {"PASS" if okb else "FAIL"}',
            f"  {name} (d'') vs GLOSA-L∘σ*: {fmt(xd)}; teleports {t1:.2f} ({t0:.2f}) -> {'PASS' if okd else 'FAIL'}"]
    labels(out, f'  {name} σ labels', F, Rt, seeds)
    return ok, okb, okd


def main(stage):
    out = []
    if stage == 'pilot':
        Rt = rows(D / 'eval_select'); seeds = R.SEL; out.append('== R10 pilot (PPO residual on GLOSA-L∘σ*), FT, SELECT 100-104'); gate = False
        for sd in (13, 113):
            k = f'L11_s{sd}'
            if k not in Rt:
                out.append(f'  {k}: MISSING'); continue
            ok, _, okd = block(out, k, [Rt[k]], Rt, seeds); gate |= ok and okd
        out.append(f'R10 PILOT GATE: {"PASS" if gate else "FAIL"}')
        if gate:
            (D / 'eval_select' / 'GATE_PASS').write_text('1\n')
    else:
        Rt = rows(D / 'eval_450'); seeds = NEW; F = [Rt[f'L11_s{s}'] for s in (213, 313, 413, 513)]
        out.append('== R10 confirmation (pooled seeds 213-513), FT, fresh 450-469')
        ok, okb, okd = block(out, 'L11_s213-513', F, Rt, seeds)
        out.append(f"  per-seed (d''): {[dpp(cmp([f], Rt['GLOSALS'], seeds, R.draws((1, len(seeds)))), [f], Rt['GLOSALS'], seeds)[0] for f in F]}")
        out.append(f'  M1 RULE: {"MET" if (ok and okb and okd) else "NOT MET"}')
    txt = '\n'.join(out) + '\n'; (D / f'report_v11_{stage}.txt').write_text(txt); print(txt)


if __name__ == '__main__':
    main(sys.argv[1])
