#!/usr/bin/env python3
"""M4 stage 3 report (Amendment M4-A5; written before any stage-3 run) = CITY_m2_report on spider: dir spider/s3/eval, fresh 1000-1019,
lights RLK_sp11 / RLK_sp111 (pairs), F0 = the rule GLOSA-L∘σ* (one fleet).  M2-A..E with the M2 code (cube, fm; crossed over light x traffic)."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402
from scripts.CITY_spatp_report import rows  # noqa: E402
import scripts.CITY_m2_report as M2  # noqa: E402

D = Path(__file__).resolve().parents[1] / 'research/city_sim/m4_20261004/spider/s3/eval'; S = list(range(1000, 1020)); K = (11, 111)
M2.S = S


def main():
    Rt = rows(D); dr = R.draws((len(K), len(S))); out = ['== M4 stage 3 (spider): light upgrade FT -> RLK with the rule fleet frozen; fresh traffic 1000-1019']
    need = ['OFF_FT', 'S03_FT', 'F0_FT'] + [f'{x}_RLK{k}' for k in K for x in ('OFF', 'S03')] + [f'F0_RLK{k}_{a}' for k in K for a in ('naive', 'labelled')]
    bad = [t for t in need if t not in Rt or sorted(Rt[t]) != S]
    if bad:
        sys.exit(f'INCOMPLETE {bad}')
    cube, fm, txt = M2.cube, M2.fm, M2.txt
    offL1, sL1 = [Rt[f'OFF_RLK{k}'] for k in K], [Rt[f'S03_RLK{k}'] for k in K]; offL0, sL0 = [Rt['OFF_FT']] * len(K), [Rt['S03_FT']] * len(K)
    for nm, L1, L0 in (('SUMO cars σ 0.5', offL1, offL0), ('SUMO cars σ* 0.3', sL1, sL0)):
        a = fm(cube(L1, L0, 'timeloss', False), dr); f = fm(cube(L1, L0, 'fuel', True), dr)
        out.append(f'  M2-A RLK - FT, {nm}: city TL {txt(a)} (upper {a[2]:+.2f}); city fuel % {txt(f)}')
    a = fm(cube(offL1, offL0, 'timeloss', False), dr); upgrade_ok = a[2] < 0
    out.append(f'  M2-A verdict: the upgrade is {"BENEFICIAL" if upgrade_ok else "NOT beneficial"} on city TL with σ 0.5 cars (P-M4-3-1 {"HOLDS" if upgrade_ok else "FAILS"})')
    F0 = [Rt['F0_FT']] * len(K); KK = (('fuel_agent', True), ('timeloss_agent', False), ('timeloss_human', False))
    b0 = {k: fm(cube(F0, sL0, *k), dr) for k in KK}
    out.append(f'  M2-B rule under FT vs σ*: fuel % {txt(b0[KK[0]])}, agent TL {txt(b0[KK[1]])}, human TL {txt(b0[KK[2]])}')
    preds = {}
    for arm in ('naive', 'labelled'):
        F1 = [Rt[f'F0_RLK{k}_{arm}'] for k in K]; b1 = {k: fm(cube(F1, sL1, *k), dr) for k in KK}
        dd = fm(cube(F1, sL1, 'fuel_agent', True) - cube(F0, sL0, 'fuel_agent', True), dr)
        verdict = 'LOST' if dd[3] > 1 else ('KEPT' if dd[2] < 1 else 'not separated'); harm_free = b1[KK[1]][2] < 0.5 and b1[KK[2]][2] < 0.5
        sp = [json.loads((D / f'F0_RLK{k}_{arm}_spat.json').read_text()) for k in K]; share = sum(x['valid'] for x in sp) / max(1, sum(x['total'] for x in sp))
        ident = all(abs(F1[i][s][q] - sL1[i][s][q]) < 1e-9 for i in range(len(K)) for s in S for q in ('fuel_agent', 'timeloss_agent', 'timeloss_human'))
        out.append(f'  M2-B rule under RLK {arm:8s} vs σ*: fuel % {txt(b1[KK[0]])}, agent TL {txt(b1[KK[1]])} (upper {b1[KK[1]][2]:+.2f}), human TL {txt(b1[KK[2]])} '
                   f'(upper {b1[KK[2]][2]:+.2f}){"  [rows IDENTICAL to σ*]" if ident else ""}')
        out.append(f'  M2-C {arm:8s}: DiD fuel % {txt(dd)} (one-sided lower {dd[3]:+.2f}, upper {dd[2]:+.2f}) -> benefit {verdict}; M2-D valid SPaT share {share:.4f} '
                   f'({sum(x["valid"] for x in sp)} / {sum(x["total"] for x in sp)}); M2-E no harm: {"YES" if harm_free else "NO"}')
        preds[arm] = (ident, verdict, harm_free)
    i, v, h = preds['labelled']; out.append(f'  P-M4-3-2 (labelled: identical to σ*, LOST, no harm): {"HOLDS" if (i and v == "LOST" and h) else "FAILS"}')
    i, v, h = preds['naive']; out.append(f'  P-M4-3-3 (naive: LOST): {"HOLDS" if v == "LOST" else "FAILS"}; naive harm-free: {"YES" if h else "NO (harm)"}')
    tel = {t: np.mean([r['teleports'] for r in Rt[t].values()]) for t in Rt}; unf = sum(r['unfinished'] for t in Rt for r in Rt[t].values())
    out.append(f'  teleports/run max over rows {max(tel.values()):.2f} ({max(tel, key=tel.get)}); unfinished total {unf}')
    t = '\n'.join(out) + '\n'; (D.parent / 'report_m4_s3.txt').write_text(t); print(t)


if __name__ == '__main__':
    main()
