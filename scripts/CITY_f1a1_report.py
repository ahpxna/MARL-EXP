#!/usr/bin/env python3
"""F1-A1 confirmation report (Amendment F1-A1; written before any F1-A1 run).  Rows in f1a1_20261004/eval (CITY_eval_f1):
  R_t<t>            light RL-H:t, --spat-arm none, fleet L11_s13 (falls back to σ*)
  RULE_t<t>         RULE0 (zero residual) with the corrected provider of light t at the locked q
  F1s_s<f>_on_t<t>  F1-scratch trained under one light (f = 213 / 313 / 413 / 513 under t4 / t5 / t6 / t7), evaluated under light t
Cube F1s[light 5, fleet 4, traffic 20] - R[light, traffic]; crossed bootstrap (R.crossed, 2 000 draws).  GATE (= §3): agent fuel upper < 0;
city / agent / human TL upper < +0.5; teleports mean <= R + 0.1; unfinished <= R.  Reported, never gated: RULE vs R, F1s vs RULE, own-light
cells vs cross-light cells.  Usage: CITY_f1a1_report.py [--dir D --seeds ...] (defaults: the registered panel)."""
import argparse, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402
from scripts.CITY_spatp_report import rows  # noqa: E402
ROOT = Path(__file__).resolve().parents[1]; LIGHTS = (4, 5, 6, 7, 8); FLEETS = ((213, 4), (313, 5), (413, 6), (513, 7))
KEYS = (('fuel_agent', True), ('timeloss', False), ('timeloss_agent', False), ('timeloss_human', False))


def cube(Rt, tag, base, S):
    """tag(l, f) -> row tag; base(l) -> base tag.  Returns {key: array[light, fleet, traffic]} of differences."""
    out = {}
    for key, pct in KEYS:
        out[key] = np.array([[[100 * (Rt[tag(l, f)][s][key] / Rt[base(l)][s][key] - 1) if pct else Rt[tag(l, f)][s][key] - Rt[base(l)][s][key]
                               for s in S] for f in FLEETS] for l in LIGHTS]) if tag(LIGHTS[0], FLEETS[0]) is not None else None
    return out


def line(name, C, dr, extra=''):
    res = {k: R.crossed(C[k], dr) for k, _ in KEYS}
    f = lambda k: f"{res[k][0]:+.2f} [{res[k][1][0]:+.2f}, {res[k][1][1]:+.2f}] (up {res[k][2]:+.2f})"
    return res, f"  {name}: agent fuel % {f('fuel_agent')} | city TL {f('timeloss')} | agent TL {f('timeloss_agent')} | human TL {f('timeloss_human')}{extra}"


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--dir', default=str(ROOT / 'research/city_sim/f1a1_20261004/eval'))
    ap.add_argument('--seeds', type=int, nargs='+', default=list(range(530, 550))); ap.add_argument('--out-name', default='report_f1a1.txt')
    a = ap.parse_args(); S = a.seeds; Rt = rows(Path(a.dir))
    need = [f'R_t{l}' for l in LIGHTS] + [f'RULE_t{l}' for l in LIGHTS] + [f'F1s_s{f}_on_t{l}' for f, _ in FLEETS for l in LIGHTS]
    bad = [t for t in need if t not in Rt or sorted(Rt[t]) != sorted(S)]
    if bad:
        sys.exit(f'INCOMPLETE {bad}')
    out = [f'== F1-A1 confirmation: F1-scratch (4 fleets) x 5 new lights t4-t8 x traffic {S[0]}-{S[-1]}, crossed; vs R (no SPaT, fleet = σ*)']
    F = cube(Rt, lambda l, f: f'F1s_s{f[0]}_on_t{l}', lambda l: f'R_t{l}', S); dr = R.draws((len(LIGHTS), len(FLEETS), len(S)))
    tel = np.mean([Rt[f'F1s_s{f}_on_t{l}'][s]['teleports'] for f, _ in FLEETS for l in LIGHTS for s in S]); tel0 = np.mean([Rt[f'R_t{l}'][s]['teleports'] for l in LIGHTS for s in S])
    unf = np.mean([Rt[f'F1s_s{f}_on_t{l}'][s]['unfinished'] for f, _ in FLEETS for l in LIGHTS for s in S]); unf0 = np.mean([Rt[f'R_t{l}'][s]['unfinished'] for l in LIGHTS for s in S])
    res, ln = line('F1-scratch vs R', F, dr, f' | tele {tel:.2f} ({tel0:.2f}) unf/run {unf:.2f} ({unf0:.2f})'); out.append(ln)
    ok = res['fuel_agent'][2] < 0 and all(res[k][2] < 0.5 for k in ('timeloss', 'timeloss_agent', 'timeloss_human')) and tel <= tel0 + 0.1 and unf <= unf0
    one = R.draws((len(LIGHTS), 1, len(S)))
    RU = {k: np.array([[[100 * (Rt[f'RULE_t{l}'][s][k] / Rt[f'R_t{l}'][s][k] - 1) if p else Rt[f'RULE_t{l}'][s][k] - Rt[f'R_t{l}'][s][k] for s in S]] for l in LIGHTS]) for k, p in KEYS}
    out.append(line('RULE (zero residual) vs R [reported]', RU, one)[1])
    FR = {k: np.array([[[100 * (Rt[f'F1s_s{f}_on_t{l}'][s][k] / Rt[f'RULE_t{l}'][s][k] - 1) if p else Rt[f'F1s_s{f}_on_t{l}'][s][k] - Rt[f'RULE_t{l}'][s][k]
                         for s in S] for f, _ in FLEETS] for l in LIGHTS]) for k, p in KEYS}
    out.append(line('F1-scratch vs RULE [reported]', FR, dr)[1])
    own = [(LIGHTS.index(t), i) for i, (_, t) in enumerate(FLEETS)]; cross = [(li, fi) for li in range(len(LIGHTS)) for fi in range(len(FLEETS)) if (li, fi) not in own]
    for nm, cells in (('own-light cells', own), ('cross-light cells', cross)):
        v = {k: np.mean([F[k][li, fi].mean() for li, fi in cells]) for k, _ in KEYS}
        out.append(f'  {nm} (n {len(cells)}) [reported, point only]: agent fuel % {v["fuel_agent"]:+.2f} | city TL {v["timeloss"]:+.2f} | agent TL {v["timeloss_agent"]:+.2f} | human TL {v["timeloss_human"]:+.2f}')
    per = {f'{f}@t{t}': round(float(F['fuel_agent'][LIGHTS.index(l), i].mean()), 2) for i, (f, t) in enumerate(FLEETS) for l in LIGHTS if l == t}
    out.append(f'  own-light fuel % per fleet: {per}')
    out.append(f'  F1-A1 GATE -> {"CONFIRMED" if ok else "NOT CONFIRMED"}'); txt = '\n'.join(out) + '\n'; (Path(a.dir).parent / a.out_name).write_text(txt); print(txt)
