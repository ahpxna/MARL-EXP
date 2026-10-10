#!/usr/bin/env python3
"""F1-B reports (PROTOCOL_CITY_F1B_20261004; written before any B1 / B2 run).  DEV 550-564, lights t4..t8, fleets 213/313/413/513 (trained
under t4/t5/t6/t7), crossed [light 5, fleet 4, traffic 15], R.crossed 2 000 draws.
  b1  dir f1b_20261004/b1: R_t<l> (no SPaT), RULEo_t<l> / RULEn_t<l> (zero residual, old fcc / new fc2, F1-A1 tables), Ao_s<f>_on_t<l> / An_s<f>_on_t<l>
      (FROZEN F1-A1 fleets, old / new provider).  Reported: An - Ao (paired), Ao vs R, An vs R, RULEn - RULEo, changed-input share.  Never a gate.
  b2  dir f1b_20261004/b2 (+ R and Ao rows from b1): Bn_s<f>_on_t<l> (F1-B fleets, fc2 with the F1-B prep tables), RULEb_t<l> (zero residual, fc2,
      F1-B tables).  DEV GATE (= F1 §3): Bn vs R agent fuel upper < 0; city / agent / human TL upper < +0.5; teleports <= R + 0.1; unfinished
      <= R.  Reported: RULEb vs R, Bn vs RULEb, Bn - Ao (new pipeline vs old, paired by seed / light / traffic)."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402
from scripts.CITY_spatp_report import rows  # noqa: E402
D = Path(__file__).resolve().parents[1] / 'research/city_sim/f1b_20261004'; S = list(range(550, 565)); LT = (4, 5, 6, 7, 8); FL = (213, 313, 413, 513)
KK = (('fuel_agent', True), ('timeloss', False), ('timeloss_agent', False), ('timeloss_human', False))


def cube(Rt, A, B, key, pct, fl=FL):
    return np.array([[[100 * (Rt[A(l, f)][s][key] / Rt[B(l, f)][s][key] - 1) if pct else Rt[A(l, f)][s][key] - Rt[B(l, f)][s][key] for s in S] for f in fl] for l in LT])


def line(name, Rt, A, B, fl=FL):
    dr = R.draws((len(LT), len(fl), len(S))); res = {k: R.crossed(cube(Rt, A, B, k, p, fl), dr) for k, p in KK}
    f = lambda k: f"{res[k][0]:+.2f} [{res[k][1][0]:+.2f}, {res[k][1][1]:+.2f}] (up {res[k][2]:+.2f})"
    return res, f"  {name}: agent fuel % {f('fuel_agent')} | city TL {f('timeloss')} | agent TL {f('timeloss_agent')} | human TL {f('timeloss_human')}"


def need(Rt, tags):
    bad = [t for t in tags if t not in Rt or sorted(Rt[t]) != S]
    if bad:
        sys.exit(f'INCOMPLETE {bad[:6]}')


def changed(d, tags):
    xs = [json.loads((d / f'{t}_f1.json').read_text()) for t in tags]; return sum(x.get('changed', 0) for x in xs), sum(x['total'] for x in xs)


if __name__ == '__main__':
    st = sys.argv[1]; b1 = rows(D / 'b1'); Rb = lambda l, f: f'R_t{l}'
    if st == 'b1':
        need(b1, [f'R_t{l}' for l in LT] + [f'RULE{v}_t{l}' for v in 'on' for l in LT] + [f'A{v}_s{f}_on_t{l}' for v in 'on' for f in FL for l in LT])
        out = ['== F1-B B1 diagnostic (DEV 550-564): FROZEN F1-A1 fleets, old (fcc) vs new (fc2) provider, same tables / q; never a gate']
        out.append(line('An - Ao (paired: the direct effect of the input fix)', b1, lambda l, f: f'An_s{f}_on_t{l}', lambda l, f: f'Ao_s{f}_on_t{l}')[1])
        out.append(line('Ao vs R (old provider)', b1, lambda l, f: f'Ao_s{f}_on_t{l}', Rb)[1]); out.append(line('An vs R (new provider)', b1, lambda l, f: f'An_s{f}_on_t{l}', Rb)[1])
        out.append(line('RULEn - RULEo', b1, lambda l, f: f'RULEn_t{l}', lambda l, f: f'RULEo_t{l}', fl=(0,))[1])
        for v in 'on':
            c, n = changed(D / 'b1', [f'A{v}_s{f}_on_t{l}' for f in FL for l in LT]); out.append(f'  fleet SPaT calls with a changed input ({"old" if v == "o" else "new"} arm): {c} / {n} = {100 * c / max(1, n):.2f} %')
        name = 'report_f1b_b1.txt'
    else:
        b2 = rows(D / 'b2'); Rt = {**b1, **b2}
        need(Rt, [f'R_t{l}' for l in LT] + [f'RULEb_t{l}' for l in LT] + [f'Bn_s{f}_on_t{l}' for f in FL for l in LT] + [f'Ao_s{f}_on_t{l}' for f in FL for l in LT])
        out = ['== F1-B B2 DEV (550-564): F1-B fleets (new pipeline, provider c2) crossed over t4-t8; vs R (no SPaT, fleet = σ*)']
        res, ln = line('F1-B vs R', Rt, lambda l, f: f'Bn_s{f}_on_t{l}', Rb)
        tel = np.mean([Rt[f'Bn_s{f}_on_t{l}'][s]['teleports'] for f in FL for l in LT for s in S]); tel0 = np.mean([Rt[f'R_t{l}'][s]['teleports'] for l in LT for s in S])
        unf = np.mean([Rt[f'Bn_s{f}_on_t{l}'][s]['unfinished'] for f in FL for l in LT for s in S]); unf0 = np.mean([Rt[f'R_t{l}'][s]['unfinished'] for l in LT for s in S])
        ok = res['fuel_agent'][2] < 0 and all(res[k][2] < 0.5 for k in ('timeloss', 'timeloss_agent', 'timeloss_human')) and tel <= tel0 + 0.1 and unf <= unf0
        out.append(ln + f' | tele {tel:.2f} ({tel0:.2f}) unf/run {unf:.2f} ({unf0:.2f})')
        out.append(line('RULE (zero residual, c2, F1-B tables) vs R [reported]', Rt, lambda l, f: f'RULEb_t{l}', Rb, fl=(0,))[1])
        out.append(line('F1-B vs RULE [reported]', Rt, lambda l, f: f'Bn_s{f}_on_t{l}', lambda l, f: f'RULEb_t{l}')[1])
        out.append(line('F1-B - F1-A1(old provider) [new pipeline vs old, paired]', Rt, lambda l, f: f'Bn_s{f}_on_t{l}', lambda l, f: f'Ao_s{f}_on_t{l}')[1])
        c, n = changed(D / 'b2', [f'Bn_s{f}_on_t{l}' for f in FL for l in LT]); out.append(f'  fleet SPaT calls where c2 differs from c (F1-B arm): {c} / {n} = {100 * c / max(1, n):.2f} %')
        out.append(f'  F1-B DEV GATE -> {"PASS: freeze and register B3 separately" if ok else "FAIL: F1-B stops (one decision, registered)"}'); name = 'report_f1b_b2.txt'
    t = '\n'.join(out) + '\n'; (D / name).write_text(t); print(t)
