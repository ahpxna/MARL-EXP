#!/usr/bin/env python3
"""R7 report (Amendment R7; written before any R7 evaluation).  Dirs under research/city_sim/spat_pilot_20261004/sbase:
  a        R7a, the fixed rule GLOSA∘σ* (tag GLOSAS): on SELECT (eval_select) and 420-429 (eval_420): P7-1 = (b) vs σ* (fuel upper < 0,
           agent TL upper < +0.5, human TL upper < +0.5); P7-2 = (a) vs always-SUMO on 420-429 (a_pass of the B pilot).  No gate.
  pilot    R7b search seed 1 (tag ES_s1, on the σ* base) on SELECT: (a), (b), (d') vs GLOSA∘σ* (agent TL upper < 0 AND fuel upper < +1 %);
           GATE (a) -> eval_select/GATE_PASS.
  confirm  420-429 (only if GATE_PASS): pooled search seeds 2-5 (fleet-seed x traffic): (a), (b), (d'); per-seed (a).
Fuel primary; the training J is never used."""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402
from scripts.CITY_spatp_report import rows, cmp, a_pass, fmt, labels  # noqa: E402

D = Path(__file__).resolve().parents[1] / 'research/city_sim/spat_pilot_20261004/sbase'
NEW = list(range(420, 430))


def bp(x):
    return x['fuel'][2] < 0 and x['tl'][2] < 0.5 and x['hu'][2] < 0.5


def dp(x):
    return x['tl'][2] < 0 and x['fuel'][2] < 1.0


def block(out, name, F, Rt, seeds, dr, dref=None):
    off, sst = Rt['OFF_FT'], Rt['S0.3_FT']; xa = cmp(F, off, seeds, dr); ok, tel, tel0 = a_pass(xa, F, off, seeds); xb = cmp(F, sst, seeds, dr)
    out += [f'  {name} (a) vs always-SUMO: {fmt(xa)}; teleports {tel:.1f} ({tel0:.1f}) -> {"PASS" if ok else "FAIL"}',
            f'  {name} (b) vs σ* 0.3: {fmt(xb)} -> {"PASS" if bp(xb) else "FAIL"}']
    if dref is not None:
        xd = cmp(F, dref, seeds, dr); out.append(f"  {name} (d') vs GLOSA∘σ*: {fmt(xd)} -> {'PASS' if dp(xd) else 'FAIL'}")
    labels(out, f'  {name} σ labels', F, Rt, seeds)
    return ok, bp(xb)


def main(stage):
    out = []
    if stage == 'a':
        for sub, seeds in (('eval_select', R.SEL), ('eval_420', NEW)):
            Rt = rows(D / sub); out.append(f'== R7a GLOSA∘σ* (fixed rule, σ* base), FT, traffic {seeds[0]}-{seeds[-1]}')
            ok, okb = block(out, 'GLOSA∘σ*', [Rt['GLOSAS']], Rt, seeds, R.draws((1, len(seeds))))
            if 'GLOSA_FT' in Rt:
                out.append(f'  plain GLOSA (σ 0.5 base) vs σ*: {fmt(cmp([Rt["GLOSA_FT"]], Rt["S0.3_FT"], seeds, R.draws((1, len(seeds)))))}')
            out.append(f'  P7-1 ({sub}): {"HOLDS" if okb else "FAILS"}' + (f'; P7-2: {"HOLDS" if ok else "FAILS"}' if sub == 'eval_420' else ''))
    elif stage == 'pilot':
        Rt = rows(D / 'eval_select'); seeds = R.SEL; out.append('== R7b pilot (search seed 1 on the σ* base), FT, SELECT 100-104')
        ok, _ = block(out, 'ES_s1', [Rt['ES_s1']], Rt, seeds, R.draws((1, len(seeds))), Rt['GLOSAS'])
        out.append(f'R7b PILOT GATE: {"PASS" if ok else "FAIL"}')
        if ok:
            (D / 'eval_select' / 'GATE_PASS').write_text('1\n')
    else:
        Rt = rows(D / 'eval_420'); seeds = NEW; F = [Rt[f'ES_s{s}'] for s in (2, 3, 4, 5)]
        out.append('== R7b confirmation (search seeds 2-5 pooled, σ* base), FT, 420-429')
        block(out, 'ES_s2-5', F, Rt, seeds, R.draws((4, len(seeds))), Rt['GLOSAS'])
        out.append(f'  per-seed (a): {[a_pass(cmp([f], Rt["OFF_FT"], seeds, R.draws((1, len(seeds)))), [f], Rt["OFF_FT"], seeds)[0] for f in F]}')
    txt = '\n'.join(out) + '\n'; (D / f'report_sbase_{stage}.txt').write_text(txt); print(txt)


if __name__ == '__main__':
    main(sys.argv[1])
