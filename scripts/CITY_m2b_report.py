#!/usr/bin/env python3
"""M2b report (Amendment M2b; written before any M2b panel evaluation).  Dir research/city_sim/spat_pilot_20261004/m2b/eval, fresh traffic
490-509, pairs k = 0..3 (RL-H:k with F0a theta_s{k+2} / F0b L11_s{213+100k}); crossed bootstrap over (pair, traffic), 2000 draws.
  M2b-1 forecast validity (m2b/validation.jsonl, offline, SELECT held-out): median |error| >= 5 s and coverage in [0.7, 0.9] -> P-M2b-1
  M2b-2 F0 - σ* under RL-H per arm (none / fc50 / fc20); DiD vs FT on agent fuel %: KEPT if upper < +1, LOST if lower > +1
  M2b-3 harm: agent or human TL upper >= +0.5, or fuel lower > 0, vs σ* under RL-H
  M2b-4 commanded vehicle-seconds per arm (sidecars)
  M2b-5 system: city TL and city fuel % of each arm vs OFF and vs σ* under RL-H
P-M2b-2: fc50 LOST for both fleets.  P-M2b-3: fc20 no harm and fuel point in (-3, 0]."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402
from scripts.CITY_spatp_report import rows  # noqa: E402

B = Path(__file__).resolve().parents[1] / 'research/city_sim/spat_pilot_20261004/m2b'; D = B / 'eval'; S = list(range(490, 510)); K = (0, 1, 2, 3)
FS = dict(F0a=[f's{k + 2}' for k in K], F0b=[f's{213 + 100 * k}' for k in K]); ARMS = ('none', 'fc50', 'fc20')


def cube(F, Bs, key, pct):
    return np.array([[100 * (f[s][key] / b[s][key] - 1) if pct else f[s][key] - b[s][key] for s in S] for f, b in zip(F, Bs)])


def fm(c, dr):
    v = np.array([c[np.ix_(*ix)].mean() for ix in dr]); return float(c.mean()), np.percentile(v, [2.5, 97.5]), float(np.percentile(v, 95)), float(np.percentile(v, 5))


def txt(x):
    return f'{x[0]:+.2f} [{x[1][0]:+.2f}, {x[1][1]:+.2f}]'


def main():
    out = ['== M2b: valid causal forecast for the learned light RL-H, frozen fleets; fresh traffic 490-509 (4 paired light-fleet seeds)']
    V = [json.loads(l) for l in (B / 'validation.jsonl').read_text().splitlines() if l.strip()]
    ok1 = all(v['med_abs'] >= 5 for v in V) and all(0.7 <= v['coverage_10_90'] <= 0.9 for v in V)
    for v in sorted(V, key=lambda x: x['light']):
        out.append(f"  M2b-1 RL-H:{v['light']}: n {v['n']}, median |err| {v['med_abs']:.1f} s, MAE {v['mae']:.2f}, bias {v['bias']:+.2f}, [q10,q90] coverage {v['coverage_10_90']:.3f}, "
                   f"per-group median |err| {v['per_group_med_abs']['min']:.0f}-{v['per_group_med_abs']['max']:.0f} s")
    out.append(f'  P-M2b-1 (median |err| >= 5 s AND coverage in [0.7, 0.9]): {"HOLDS" if ok1 else "FAILS"}')
    Rt = rows(D); dr = R.draws((4, len(S)))
    offL1, sL1 = [Rt[f'OFF_RLH{k}'] for k in K], [Rt[f'S03_RLH{k}'] for k in K]; sL0 = [Rt['S03_FT']] * 4
    a = fm(cube(offL1, [Rt['OFF_FT']] * 4, 'timeloss', False), dr); out.append(f'  light upgrade RL-H - FT (OFF cars): city TL {txt(a)}')
    p2, p3 = True, True
    for fl, seeds in FS.items():
        F0 = [Rt[f'{fl}_FT_{s}'] for s in seeds]; c0 = cube(F0, sL0, 'fuel_agent', True)
        out.append(f'  {fl} under FT vs σ*: fuel % {txt(fm(c0, dr))}, agent TL {txt(fm(cube(F0, sL0, "timeloss_agent", False), dr))}')
        for arm in ARMS:
            F1 = [Rt[f'{fl}_RLH{k}_{arm}'] for k in K]
            f1 = fm(cube(F1, sL1, 'fuel_agent', True), dr); ta = fm(cube(F1, sL1, 'timeloss_agent', False), dr); th = fm(cube(F1, sL1, 'timeloss_human', False), dr)
            dd = fm(cube(F1, sL1, 'fuel_agent', True) - c0, dr); verdict = 'LOST' if dd[3] > 1 else ('KEPT' if dd[2] < 1 else 'not separated')
            harm = ta[2] >= 0.5 or th[2] >= 0.5 or f1[3] > 0
            sc = [json.loads((D / f'{fl}_RLH{k}_{arm}_m2b.json').read_text()) for k in K]; cmd = sum(x['commanded'] for x in sc)
            cityTL = fm(cube(F1, sL1, 'timeloss', False), dr); cityF = fm(cube(F1, sL1, 'fuel', True), dr); cityOFF = fm(cube(F1, offL1, 'timeloss', False), dr)
            out.append(f'  M2b-2 {fl} RL-H {arm:5s} vs σ*: fuel % {txt(f1)}, agent TL {txt(ta)} (upper {ta[2]:+.2f}), human TL {txt(th)} (upper {th[2]:+.2f}); '
                       f'DiD fuel {txt(dd)} (lower {dd[3]:+.2f}, upper {dd[2]:+.2f}) -> {verdict}; harm: {"YES" if harm else "no"}')
            out.append(f'        M2b-4 commanded vehicle-seconds {cmd} (valid SPaT calls {sum(x["valid"] for x in sc)} / {sum(x["total"] for x in sc)}); '
                       f'M2b-5 city TL vs σ* {txt(cityTL)}, city fuel % vs σ* {txt(cityF)}, city TL vs OFF {txt(cityOFF)}')
            if arm == 'fc50':
                p2 &= verdict == 'LOST'
            if arm == 'fc20':
                p3 &= (not harm) and -3 < f1[0] <= 0
    out += [f'  P-M2b-2 (fc50 LOST for both fleets): {"HOLDS" if p2 else "FAILS"}', f'  P-M2b-3 (fc20 no harm, fuel point in (-3, 0]): {"HOLDS" if p3 else "FAILS"}']
    tel = {t: np.mean([r['teleports'] for r in Rt[t].values()]) for t in Rt}; unf = sum(r['unfinished'] for t in Rt for r in Rt[t].values())
    out.append(f'  rows {len(Rt)}; teleports/run max {max(tel.values()):.2f} ({max(tel, key=tel.get)}); unfinished total {unf}')
    t = '\n'.join(out) + '\n'; (B / 'report_m2b.txt').write_text(t); print(t)


if __name__ == '__main__':
    main()
