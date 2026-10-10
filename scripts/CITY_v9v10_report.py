#!/usr/bin/env python3
"""v9 report (PROTOCOL_CITY_SPAT_PILOT_20261004 Amendments R4 / R5; generic for v9 and v10 by --version; written before any evaluation).
  pilot    eval dir research/city_sim/spat_pilot_20261004/v9_select (SELECT 100-104, FT): per pilot seed (13, 113): (a) vs always-SUMO,
           (b) vs σ* = 0.3, (d) vs the base controller IC:GLOSA [human TL superiority, fuel NI +1 %, agent TL NI +0.5]; GATE = >= 1 pilot
           seed passes (a) -> writes GATE_PASS.  (b), (d) descriptive in the pilot.
  confirm  eval dir .../v9_confirm (420-429; only if GATE_PASS): pooled over seeds 213-513 (fleet-seed x traffic): (a), (b), (d) as verdicts;
           per-seed (a); σ labels (three-state, descriptive).
Fuel is the primary endpoint; no 'fuel OR TL' rule; training rewards are never used."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402
from scripts.CITY_spatp_report import rows, cmp, a_pass, fmt, labels  # noqa: E402

D = Path(__file__).resolve().parents[1] / 'research/city_sim/spat_pilot_20261004'


def d_pass(x):
    return x['hu'][2] < 0 and x['fuel'][2] < 1.0 and x['tl'][2] < 0.5


def report(stage, ver='9'):
    d = D / (f'v{ver}_select' if stage == 'pilot' else f'v{ver}_confirm'); Rt = rows(d)
    seeds = R.SEL if stage == 'pilot' else list(range(420, 430)); off, sst, base = Rt['OFF_FT'], Rt['S0.3_FT'], Rt['IC_FT']
    out = [f'== v{ver} {stage}: residual on IC-GLOSA, reward A-group, FT, traffic {seeds[0]}-{seeds[-1]}']
    xb0 = cmp([base], off, seeds, R.draws((1, len(seeds)))); out.append(f'  base IC-GLOSA vs always-SUMO: {fmt(xb0)}')
    if stage == 'pilot':
        gate = False
        for sd in (13, 113):
            k = f'R{ver}_s{sd}'
            if k not in Rt:
                out.append(f'  {k}: MISSING'); continue
            dr = R.draws((1, len(seeds))); xa = cmp([Rt[k]], off, seeds, dr); ok, tel, tel0 = a_pass(xa, [Rt[k]], off, seeds); gate |= ok
            xb, xd = cmp([Rt[k]], sst, seeds, dr), cmp([Rt[k]], base, seeds, dr)
            out += [f'  {k} (a) vs always-SUMO: {fmt(xa)}; teleports {tel:.1f} ({tel0:.1f}) -> {"PASS" if ok else "FAIL"}',
                    f'      (b, descriptive) vs σ* 0.3: {fmt(xb)}', f'      (d, descriptive) vs base: {fmt(xd)} -> {"would pass" if d_pass(xd) else "would fail"}']
            labels(out, f'      σ labels {k}', [Rt[k]], Rt, seeds)
        out.append(f'V{ver} PILOT GATE (>= 1 pilot seed passes (a)): {"PASS" if gate else "FAIL"}')
        if gate:
            (d / 'GATE_PASS').write_text('1\n')
    else:
        F = [Rt[f'R{ver}_s{s}'] for s in (213, 313, 413, 513)]; dr = R.draws((4, len(seeds)))
        xa = cmp(F, off, seeds, dr); ok, tel, tel0 = a_pass(xa, F, off, seeds); per = [a_pass(cmp([f], off, seeds, R.draws((1, len(seeds)))), [f], off, seeds) for f in F]
        okt = all(p[1] <= p[2] + 1 for p in per); xb = cmp(F, sst, seeds, dr); xd = cmp(F, base, seeds, dr)
        okb = xb['fuel'][2] < 0 and xb['tl'][2] < 0.5 and xb['hu'][2] < 0.5
        out += [f'  (a) pooled vs always-SUMO: {fmt(xa)} -> {"SUPPORTED" if ok and okt else "NOT SUPPORTED"}; per-seed (a) {[bool(p[0]) for p in per]}',
                f'  (b) pooled vs σ* 0.3: {fmt(xb)} -> {"SUPPORTED" if okb else "NOT SUPPORTED"}',
                f'  (d) pooled vs base IC-GLOSA: {fmt(xd)} -> {"SUPPORTED" if d_pass(xd) else "NOT SUPPORTED"}']
        labels(out, '  σ labels pooled', F, Rt, seeds)
    txt = '\n'.join(out) + '\n'; (D / f'report_v{ver}_{stage}.txt').write_text(txt); print(txt)


if __name__ == '__main__':
    report(sys.argv[1], sys.argv[2] if len(sys.argv) > 2 else '9')
