#!/usr/bin/env python3
"""M2 report (PROTOCOL_CITY_M2_COMPAT_20261004; written before any M2 evaluation).  Dir research/city_sim/spat_pilot_20261004/m2/eval,
fresh traffic 470-489.  Pairs k = 0..3: RL-H:k with fleet seed k (F0a theta_s{k+2}, F0b L11_s{213+100k}); under FT the fleets use the
same seeds and OFF / σ* are single rows.  Crossed bootstrap over (pair, traffic), 2000 draws.
  M2-A  light upgrade RL-H - FT with SUMO cars (OFF, σ*): city TL, city fuel %
  M2-B  fleet benefit F0 - σ* under FT and under RL-H (naive / labelled): agent fuel %, agent TL, human TL
  M2-C  DiD D = [F0 - σ*]_RL-H - [F0 - σ*]_FT on agent fuel %: LOST if lower > +1, KEPT if upper < +1, else not separated
  M2-D  SPaT calls with valid SPaT (sidecars)
  M2-E  harm under RL-H: F0 - σ* agent / human TL upper < +0.5"""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402
from scripts.CITY_spatp_report import rows  # noqa: E402

D = Path(__file__).resolve().parents[1] / 'research/city_sim/spat_pilot_20261004/m2/eval'; S = list(range(470, 490)); K = (0, 1, 2, 3)
FS = dict(F0a=[f's{k + 2}' for k in K], F0b=[f's{213 + 100 * k}' for k in K])


def cube(F, B, key, pct):
    return np.array([[100 * (f[s][key] / b[s][key] - 1) if pct else f[s][key] - b[s][key] for s in S] for f, b in zip(F, B)])


def fm(c, dr):
    p, ci, up = R.crossed(c, dr); lo = float(np.percentile([c[np.ix_(*ix)].mean() for ix in dr], 5))
    return p, ci, up, lo


def txt(x):
    return f'{x[0]:+.2f} [{x[1][0]:+.2f}, {x[1][1]:+.2f}]'


def main():
    Rt = rows(D); dr = R.draws((4, len(S))); out = ['== M2: light upgrade FT -> RL-H with the confirmed fleets frozen; fresh traffic 470-489']
    offL1, sL1 = [Rt[f'OFF_RLH{k}'] for k in K], [Rt[f'S03_RLH{k}'] for k in K]; offL0, sL0 = [Rt['OFF_FT']] * 4, [Rt['S03_FT']] * 4
    for nm, L1, L0 in (('SUMO cars σ 0.5', offL1, offL0), ('SUMO cars σ* 0.3', sL1, sL0)):
        a = fm(cube(L1, L0, 'timeloss', False), dr); f = fm(cube(L1, L0, 'fuel', True), dr)
        out.append(f'  M2-A RL-H - FT, {nm}: city TL {txt(a)} (upper {a[2]:+.2f}); city fuel % {txt(f)}')
    a = fm(cube(offL1, offL0, 'timeloss', False), dr); upgrade_ok = a[2] < 0
    out.append(f'  M2-A verdict: the upgrade is {"BENEFICIAL" if upgrade_ok else "NOT beneficial"} on city TL with σ 0.5 cars (P-M2-1 {"HOLDS" if upgrade_ok else "FAILS"})')
    pred2 = True
    for fl, seeds in FS.items():
        F0 = [Rt[f'{fl}_FT_{s}'] for s in seeds]
        b0 = {k: fm(cube(F0, sL0, *k), dr) for k in (('fuel_agent', True), ('timeloss_agent', False), ('timeloss_human', False))}
        out.append(f'  M2-B {fl} under FT vs σ*: fuel % {txt(b0[("fuel_agent", True)])}, agent TL {txt(b0[("timeloss_agent", False)])}, human TL {txt(b0[("timeloss_human", False)])}')
        for arm in ('naive', 'labelled'):
            F1 = [Rt[f'{fl}_RLH{k}_{arm}'] for k in K]
            b1 = {k: fm(cube(F1, sL1, *k), dr) for k in (('fuel_agent', True), ('timeloss_agent', False), ('timeloss_human', False))}
            dd = fm(cube(F1, sL1, 'fuel_agent', True) - cube(F0, sL0, 'fuel_agent', True), dr)
            verdict = 'LOST' if dd[3] > 1 else ('KEPT' if dd[2] < 1 else 'not separated')
            harm = b1[('timeloss_agent', False)][2] < 0.5 and b1[('timeloss_human', False)][2] < 0.5
            sp = [json.loads((D / f'{fl}_RLH{k}_{arm}_spat.json').read_text()) for k in K]; share = sum(x['valid'] for x in sp) / max(1, sum(x['total'] for x in sp))
            ident = all(abs(F1[i][s][q] - sL1[i][s][q]) < 1e-9 for i in range(4) for s in S for q in ('fuel_agent', 'timeloss_agent', 'timeloss_human'))
            out.append(f'  M2-B {fl} under RL-H {arm:8s} vs σ*: fuel % {txt(b1[("fuel_agent", True)])}, agent TL {txt(b1[("timeloss_agent", False)])} '
                       f'(upper {b1[("timeloss_agent", False)][2]:+.2f}), human TL {txt(b1[("timeloss_human", False)])} (upper {b1[("timeloss_human", False)][2]:+.2f})'
                       f'{"  [rows IDENTICAL to σ*]" if ident else ""}')
            out.append(f'  M2-C {fl} {arm:8s}: DiD fuel % {txt(dd)} (one-sided lower {dd[3]:+.2f}, upper {dd[2]:+.2f}) -> benefit {verdict}; '
                       f'M2-D valid SPaT share {share:.4f} ({sum(x["valid"] for x in sp)} / {sum(x["total"] for x in sp)}); M2-E no harm: {"YES" if harm else "NO"}')
            if arm == 'labelled':
                pred2 &= ident and verdict == 'LOST' and harm
    out.append(f'  P-M2-2 (labelled: collapse to σ*, benefit LOST, no harm, both fleets): {"HOLDS" if pred2 else "FAILS"}')
    tel = {t: np.mean([r['teleports'] for r in Rt[t].values()]) for t in Rt}; unf = sum(r['unfinished'] for t in Rt for r in Rt[t].values())
    out.append(f'  teleports/run max over rows {max(tel.values()):.2f} ({max(tel, key=tel.get)}); unfinished total {unf}')
    t = '\n'.join(out) + '\n'; (D.parent / 'report_m2.txt').write_text(t); print(t)


if __name__ == '__main__':
    main()
