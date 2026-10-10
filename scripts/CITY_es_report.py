#!/usr/bin/env python3
"""R6 report (Amendment R6; written before any R6 evaluation).  pilot: dir es/eval_select (SELECT): theta*_s1 vs always-SUMO (a), σ* (b),
theta0 = heuristic GLOSA (d': agent TL superiority + fuel NI +1 %); GATE (a).  confirm: dir es/eval_confirm (420-429, only if GATE_PASS):
pooled over search seeds 2-5 (fleet-seed x traffic): (a), (b), (d').  Fuel primary; training J never used."""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402
from scripts.CITY_spatp_report import rows, cmp, a_pass, fmt, labels  # noqa: E402

D = Path(__file__).resolve().parents[1] / 'research/city_sim/spat_pilot_20261004/es'


def dp(x):
    return x['tl'][2] < 0 and x['fuel'][2] < 1.0


def main(stage):
    d = D / ('eval_select' if stage == 'pilot' else 'eval_confirm'); Rt = rows(d); seeds = R.SEL if stage == 'pilot' else list(range(420, 430))
    off, sst, g0 = Rt['OFF_FT'], Rt['S0.3_FT'], Rt['GLOSA_FT']; out = [f'== R6 {stage} (parametric GLOSA by policy search), FT, traffic {seeds[0]}-{seeds[-1]}']
    out.append(f'  theta0 (heuristic GLOSA) vs always-SUMO: {fmt(cmp([g0], off, seeds, R.draws((1, len(seeds)))))}')
    if stage == 'pilot':
        F = [Rt['ES_s1']]; dr = R.draws((1, len(seeds)))
    else:
        F = [Rt[f'ES_s{s}'] for s in (2, 3, 4, 5)]; dr = R.draws((4, len(seeds)))
    xa = cmp(F, off, seeds, dr); ok, tel, tel0 = a_pass(xa, F, off, seeds); xb = cmp(F, sst, seeds, dr); xd = cmp(F, g0, seeds, dr)
    okb = xb['fuel'][2] < 0 and xb['tl'][2] < 0.5 and xb['hu'][2] < 0.5
    out += [f'  (a) vs always-SUMO: {fmt(xa)}; teleports {tel:.1f} ({tel0:.1f}) -> {"PASS" if ok else "FAIL"}',
            f'  (b) vs σ* 0.3: {fmt(xb)} -> {"PASS" if okb else "FAIL"}', f'  (d\') vs theta0: {fmt(xd)} -> {"PASS" if dp(xd) else "FAIL"}']
    if stage != 'pilot':
        per = [a_pass(cmp([f], off, seeds, R.draws((1, len(seeds)))), [f], off, seeds)[0] for f in F]; out.append(f'  per-seed (a): {per}')
    labels(out, '  σ labels', F, Rt, seeds)
    if stage == 'pilot':
        out.append(f'R6 PILOT GATE: {"PASS" if ok else "FAIL"}')
        if ok:
            (d / 'GATE_PASS').write_text('1\n')
    txt = '\n'.join(out) + '\n'; (D / f'report_es_{stage}.txt').write_text(txt); print(txt)


if __name__ == '__main__':
    main(sys.argv[1])
