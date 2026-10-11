#!/usr/bin/env python3
"""M4 stage 3 complete report (PROTOCOL_CITY_M4_STAGE3_20261004; written before any new stage-3 run).  Panel spider 1000-1019.
3a rows (C-81, spider/s3/eval): F0_FT, S03_FT, S03_RLK<k>, F0_RLK<k>_labelled / _naive.  New rows (spider/s3b/eval): F0_RLK<k>_fcast (3b);
F1_s<f>_on_<k> (3c, L1/F1, crossed), F1_s<f>_FT (3c, L0/F1, program SPaT).
3b: M2-B / C / D / E with the M2 code (cube, fm; crossed over light x traffic).  3c (descriptive): [F1 - σ*]_L1 crossed [light, fleet, traffic],
[F1 - σ*]_L0 [1, fleet, traffic], D_adapt = [F1 - σ*]_L1 - [F0 - σ*]_L1,fcast, D_rev = [F1 - σ*]_L0 - [F0 - σ*]_L0, own vs cross cells; the F1 §3
limits are shown, never gated."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402
from scripts.CITY_spatp_report import rows  # noqa: E402
import scripts.CITY_m2_report as M2  # noqa: E402
SP = Path(__file__).resolve().parents[1] / 'research/city_sim/m4_20261004/spider'; S = list(range(1000, 1020)); K = (11, 111); FL = ((213, 11), (313, 11), (413, 111), (513, 111))
KK = (('fuel_agent', True), ('timeloss', False), ('timeloss_agent', False), ('timeloss_human', False))


def ci(c, dr):
    p, c2, up = R.crossed(c, dr); lo = float(np.percentile([c[np.ix_(*ix)].mean() for ix in dr], 5)); return p, c2, up, lo


def f(x):
    return f'{x[0]:+.2f} [{x[1][0]:+.2f}, {x[1][1]:+.2f}] (lo {x[3]:+.2f}, up {x[2]:+.2f})'


if __name__ == '__main__':
    BD = Path(sys.argv[sys.argv.index('--bdir') + 1]) if '--bdir' in sys.argv else SP / 's3b/eval'   # test hook: a synthetic s3b/eval directory
    A, B = rows(SP / 's3/eval'), rows(BD); M2.S = S; q = json.loads(((BD / 'locked.json') if '--bdir' in sys.argv else (SP / 's3b/prov/locked.json')).read_text())
    out = [f'== M4 stage 3 (complete): spider 1000-1019; forecast-K closed-loop, locked q {q["q"]} ({"feasible" if q["feasible"] else "INFEASIBLE"} on DEV)']
    need = [f'F0_RLK{k}_fcast' for k in K] + [f'F1_s{f_}_on_{k}' for f_, _ in FL for k in K] + [f'F1_s{f_}_FT' for f_, _ in FL]
    bad = [t for t in need if t not in B or sorted(B[t]) != S]
    if bad:
        sys.exit(f'INCOMPLETE {bad}')
    # ---- 3b (M2 code, cube [light 2, traffic 20])
    dr2 = R.draws((len(K), len(S))); sL0 = [A['S03_FT']] * 2; sL1 = [A[f'S03_RLK{k}'] for k in K]; F0 = [A['F0_FT']] * 2
    Fc = [B[f'F0_RLK{k}_fcast'] for k in K]
    b0 = M2.fm(M2.cube(F0, sL0, 'fuel_agent', True), dr2); b1 = {k_: M2.fm(M2.cube(Fc, sL1, k_, p), dr2) for k_, p in KK}
    dd = M2.fm(M2.cube(Fc, sL1, 'fuel_agent', True) - M2.cube(F0, sL0, 'fuel_agent', True), dr2)
    verdict = 'LOST' if dd[3] > 1 else ('KEPT' if dd[2] < 1 else 'not separated'); harm_free = b1['timeloss_agent'][2] < 0.5 and b1['timeloss_human'][2] < 0.5
    side = [json.loads((BD / f'F0_RLK{k}_fcast_f1k.json').read_text()) for k in K]; src = [json.loads((BD / f'F0_RLK{k}_fcast_s3.json').read_text())['sources'] for k in K]
    tot = sum(x['total'] for x in side); val = sum(x['valid'] for x in side); amb = sum(x.get('unavailable:ambiguous-end', 0) for x in src)
    out += [f'  3b L0/F0 (FT) vs σ*: fuel % {M2.txt(b0)}',
            f'  3b L1/F0 forecast vs σ*: fuel % {M2.txt(b1["fuel_agent"])} | agent TL {M2.txt(b1["timeloss_agent"])} (up {b1["timeloss_agent"][2]:+.2f}) | human TL '
            f'{M2.txt(b1["timeloss_human"])} (up {b1["timeloss_human"][2]:+.2f}) | city TL {M2.txt(b1["timeloss"])}',
            f'  3b M2-C DiD fuel % {M2.txt(dd)} (lo {dd[3]:+.2f}, up {dd[2]:+.2f}) -> benefit {verdict}; M2-E no harm: {"YES" if harm_free else "NO"}; '
            f'M2-D valid share {val / max(1, tot):.3f} ({val} / {tot}), ambiguous-end {amb}',
            f'  P-S3-1 (LOST): {"HOLDS" if verdict == "LOST" else "FAILS"}']
    fq = SP / 'report_m4_s3b_forecast_quality.json'
    if fq.exists():
        out.append(f'  3b forecast quality (DEV closed-loop traces, locked q): {fq.read_text().strip()}')
    # ---- 3c (descriptive)
    dr3 = R.draws((len(K), len(FL), len(S)))
    c1 = {k_: np.array([[[100 * (B[f'F1_s{f_}_on_{k}'][s][k_] / A[f'S03_RLK{k}'][s][k_] - 1) if p else B[f'F1_s{f_}_on_{k}'][s][k_] - A[f'S03_RLK{k}'][s][k_] for s in S] for f_, _ in FL] for k in K]) for k_, p in KK}
    c0 = {k_: np.array([[[100 * (B[f'F1_s{f_}_FT'][s][k_] / A['S03_FT'][s][k_] - 1) if p else B[f'F1_s{f_}_FT'][s][k_] - A['S03_FT'][s][k_] for s in S] for f_, _ in FL]]) for k_, p in KK}
    f0c = np.array([[[100 * (B[f'F0_RLK{k}_fcast'][s]['fuel_agent'] / A[f'S03_RLK{k}'][s]['fuel_agent'] - 1) for s in S]] * len(FL) for k in K])
    f0L0 = np.array([[[100 * (A['F0_FT'][s]['fuel_agent'] / A['S03_FT'][s]['fuel_agent'] - 1) for s in S]] * len(FL)])
    tel = np.mean([B[f'F1_s{f_}_on_{k}'][s]['teleports'] for f_, _ in FL for k in K for s in S]); tel0 = np.mean([A[f'S03_RLK{k}'][s]['teleports'] for k in K for s in S])
    lim = lambda c: all(ci(c[k_], dr3 if c is c1 else R.draws((1, len(FL), len(S))))[2] < 0.5 for k_ in ('timeloss', 'timeloss_agent', 'timeloss_human'))
    out.append('  3c (DESCRIPTIVE matrix cells; not a method test; grid4 F1-A1 failed, C-85)')
    out.append(f'  3c L1/F1 vs σ* (crossed 2 x 4 x 20): fuel % {f(ci(c1["fuel_agent"], dr3))} | city TL {f(ci(c1["timeloss"], dr3))} | agent TL {f(ci(c1["timeloss_agent"], dr3))} | '
               f'human TL {f(ci(c1["timeloss_human"], dr3))} | tele {tel:.2f} ({tel0:.2f}) | F1 §3 TL limits shown: {"within" if lim(c1) else "NOT within"}')
    d1 = R.draws((1, len(FL), len(S)))
    out.append(f'  3c L0/F1 vs σ* (FT, program SPaT): fuel % {f(ci(c0["fuel_agent"], d1))} | agent TL {f(ci(c0["timeloss_agent"], d1))} | human TL {f(ci(c0["timeloss_human"], d1))}')
    out.append(f'  3c D_adapt = [F1-σ*]_L1 - [F0-σ*]_L1,fcast: fuel % {f(ci(c1["fuel_agent"] - f0c, dr3))}')
    out.append(f'  3c D_rev = [F1-σ*]_L0 - [F0-σ*]_L0: fuel % {f(ci(c0["fuel_agent"] - f0L0, d1))}  (P-S3-4: D_rev > 0)')
    own = [(K.index(t), i) for i, (_, t) in enumerate(FL)]; cross = [(li, fi) for li in range(len(K)) for fi in range(len(FL)) if (li, fi) not in own]
    for nm, cells in (('own-light', own), ('cross-light', cross)):
        out.append(f'  3c {nm} cells (n {len(cells)}) [point]: fuel % {np.mean([c1["fuel_agent"][c].mean() for c in cells]):+.2f}, agent TL {np.mean([c1["timeloss_agent"][c].mean() for c in cells]):+.2f}')
    t = '\n'.join(out) + '\n'; (BD.parent / ('report_fake.txt' if '--bdir' in sys.argv else 'x')).write_text(t) if '--bdir' in sys.argv else (SP / 'report_m4_s3full.txt').write_text(t); print(t)
