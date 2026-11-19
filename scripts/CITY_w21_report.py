#!/usr/bin/env python3
"""W21 report (PROTOCOL_CITY_WAVE21_20261015).
  a <dir>  W21-A, the W20 pair in the W17 field-matched world.  Rows <dir>/gate (OFF_t0_h, GATE_t<k>_h) and <dir>/conf (R / SV with the
           fuel-by-mode logger).  Checks: every row tagged w17_world (the world wrapper ran); KM13-1b (fuel-by-mode total within 2 %).
           G21-A0[f]: GATE - OFF city time loss upper < 0 (95 %); a family that fails is excluded from D21-A1.
           D21-A1[f], f in AH, SRL, RDQ, RMP (alpha 0.05/4): DiD agents' time loss (SV - R)_f - (SV - R)_RWV, lower bound > 0.
           Descriptive (95 %): SV - R per family with the M3 limits; mechanism (mean green, served-lane halting under R / SV); the W20
           (Krauss world) SV - R alongside, not paired (other world, lights and fleets).
  b <dir>  W21-B, the pair on the full Midtown map (MT-E setting).  Rows <dir>/MTW_*.json.  G21-B0 and KW21-B1 come from the job
           (<dir>/gate.txt, <dir>/kw21_b1.txt).  D21-B1 (alpha 0.05): DiD agents' time loss (SV - R)_thr - (SV - R)_B2D, lower bound > 0.
           Descriptive (95 %): SV - R per family with the M3 limits; mechanism; threshold lights alone - ACT.
Crossed bootstrap of CITY_w6_report_v2 (lights, fleets, traffic seeds / days resampled; B = 2000; the DiD resamples each family's lights
separately with fleets and traffic shared).  W21_SMOKE=1: slot 0, one fleet, one seed / day.   Usage: CITY_w21_report.py a|b <dir>"""
import json, os, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w6_report_v2 as V  # noqa: E402
from scripts.CITY_w6_validation import rows  # noqa: E402

MODE, D = sys.argv[1], Path(sys.argv[2]); SM = os.environ.get('W21_SMOKE') == '1'; SFX = '_smoke' if SM else ''
K = lambda p, a: (lambda l, f: f'{p}{a}_t{l}_{f}')  # noqa: E731


def mech(Rt, key, L, F, S):
    return tuple(float(np.mean([Rt[key(l, f)][s][m] for l in L for f in F for s in S])) for m in ('green_mean', 'mean_halting'))


def pair_block(Rt, L, F, S, pfx, out, q=95.0):
    r = V.paired(Rt, K(pfx, 'SV'), K(pfx, 'R'), L, F, S, q=q)
    ok, tl = V.limits(r, V.tele(Rt, K(pfx, 'SV'), L, F, S), V.tele(Rt, K(pfx, 'R'), L, F, S))
    m = {a: mech(Rt, K(pfx, a), L, F, S) for a in ('R', 'SV')}
    out += [V.line(f'SV - R ({q:.0f} %)', r), f'  {tl}; every limit met: {ok}',
            '  mechanism (mean green s / served-lane halting): ' + ', '.join(f'{a} {v[0]:.2f} / {v[1]:.2f}' for a, v in m.items())
            + f'; mean green SV vs R {100 * (m["SV"][0] / m["R"][0] - 1):+.1f} %']
    return dict(SV_R=r, meets=ok, mech=m)


if MODE == 'a':
    K0 = {'AH': 34, 'SRL': 84, 'RDQ': 89, 'RMP': 94, 'RWV': 99}; THR = ['AH', 'SRL', 'RDQ', 'RMP']
    KEEP = os.environ.get('W21_FAMS', ' '.join(K0)).split()
    SL = (0,) if SM else (0, 1, 2, 3, 4); FS = ('s2213',) if SM else ('s2213', 's2313', 's2413', 's2513')
    S = [860] if SM else list(range(1420, 1440)); Q1 = 100 - 5 / 4
    L = lambda f: tuple(K0[f] + j for j in SL)  # noqa: E731
    Rt = rows(D / 'conf'); G = rows(D / 'gate')
    for key, rr in list(Rt.items()) + list(G.items()):
        for s, r in rr.items():
            if not r.get('w17_world'):
                sys.exit(f'W21-A FAIL: row {key} seed {s} not tagged w17_world')
    for key, rr in Rt.items():
        for s, r in rr.items():
            if not 0.98 <= r['modes_ratio_all'] <= 1.02:
                sys.exit(f'KM13-1b FAIL {key} seed {s}: {r["modes_ratio_all"]}')
    for f in K0:
        for k in L(f):
            G[f'OFFG_t{k}_h'] = G['OFF_t0_h']
    W20 = json.loads((ROOT / 'research/city_sim/w20_20261009/w20.json').read_text())
    out = [f'== W21-A: the W20 pair in the W17 field-matched world (lights {SL}, fleets {FS}, fresh {S[0]}-{S[-1]})',
           'rows tagged w17_world: PASS; KM13-1b PASS']
    gone = [f for f in K0 if f not in KEEP]
    if gone:
        out.append(f'EXCLUDED as degenerate (a green never completed in the traces; registered rule): {gone}')
    res, gate_ok = {}, {}
    for f in [x for x in K0 if x in KEEP]:
        g = V.paired(G, K('', 'GATE'), K('', 'OFFG'), L(f), ('h',), S); gate_ok[f] = g['timeloss']['up'] < 0
        out += [f'-- {f} (lights t{L(f)[0]}-t{L(f)[-1]})', V.line('light gate GATE - FT, every driver field-matched (95 %)', g),
                f'  G21-A0[{f}]: {"PASS" if gate_ok[f] else "FAIL (excluded from D21-A1)"}']
        e = dict(gate=g['timeloss'], G21_A0=gate_ok[f]); e.update(pair_block(Rt, L(f), FS, S, '', out))
        w = W20.get(f, {}).get('SV-R', {}).get('H4', {}).get('timeloss_agent')
        if w:
            out.append(f'  W20, Krauss world (other lights and fleets; not paired): SV - R agent TL {w["point"]:+.2f} [{w["lo2"]:+.2f}, {w["hi2"]:+.2f}]')
        res[f] = e
    for f in THR:
        if f not in res:
            continue
        if not (gate_ok.get(f) and gate_ok.get('RWV')):
            res[f]['D21_A1'] = None; out.append(f'-- D21-A1[{f}]: not computable (G21-A0 failed for {f} or RWV, or RWV excluded)'); continue
        dd = V.did(Rt, K('', 'SV'), K('', 'R'), L(f), K('', 'SV'), K('', 'R'), L('RWV'), FS, S, q=Q1); d1 = dd['timeloss_agent']['low'] > 0
        res[f]['did_vs_RWV'] = dd; res[f]['D21_A1'] = d1
        out += [f'-- D21-A1[{f}]', V.line(f'DiD (SV - R)_{f} - (SV - R)_RWV ({Q1:.2f} %; "low" = lower bound)', dd)
                + f' | agent TL lower {dd["timeloss_agent"]["low"]:+.2f}',
                f'  D21-A1[{f}] publication harms this representation more than the threshold-free control, with field-matched drivers: '
                + ('SHOWN' if d1 else 'NOT SHOWN')]
    (D / f'report_w21a{SFX}.txt').write_text('\n'.join(out) + '\n'); (D / f'w21a{SFX}.json').write_text(json.dumps(res, indent=1, default=float))
elif MODE == 'b':
    THRF = os.environ.get('W21_THR', 'AH'); K0 = {'AH': 34, 'RMP': 94, 'B2D': 59}
    SL = (0,) if SM else (0, 1, 2, 3, 4); FS = ('s1413',) if SM else ('s1413', 's1513', 's1613', 's1713'); S = [0] if SM else [0, 1, 2, 3, 4]
    L = lambda f: tuple(K0[f] + j for j in SL)  # noqa: E731
    Rt = rows(D)
    out = [f'== W21-B: the pair on the full Midtown map (MT-E setting: two-green signals learned, the rest actuated; Krauss drivers; random demand)',
           f'threshold family {THRF}, control B2D; lights {SL}, fleets {FS}, days {S}']
    gtxt = (D / 'gate.txt').read_text().strip() if (D / 'gate.txt').exists() else 'gate.txt missing'
    out.append(gtxt)
    lg = np.array([[Rt[f'MTW_LGar_t{k}'][s]['timeloss'] - Rt['MTW_ACT'][s]['timeloss'] for s in S] for k in L(THRF)])
    rng = np.random.default_rng(0)
    bs = [lg[np.ix_(rng.integers(0, lg.shape[0], lg.shape[0]), rng.integers(0, lg.shape[1], lg.shape[1]))].mean() for _ in range(2000)]
    out.append(f'  {THRF} lights alone - ACT, city time loss (all human; lights x days bootstrap, descriptive): {lg.mean():+.2f} '
               f'[{np.percentile(bs, 2.5):+.2f}, {np.percentile(bs, 97.5):+.2f}] s/veh')
    res = dict(thr=THRF, gate=gtxt, lg_minus_act=float(lg.mean()))
    for f in (THRF, 'B2D'):
        out.append(f'-- {f} (lights t{L(f)[0]}-t{L(f)[-1]})'); res[f] = pair_block(Rt, L(f), FS, S, 'MTW_', out)
    dd = V.did(Rt, K('MTW_', 'SV'), K('MTW_', 'R'), L(THRF), K('MTW_', 'SV'), K('MTW_', 'R'), L('B2D'), FS, S, q=95.0)
    d1 = dd['timeloss_agent']['low'] > 0; res['did_vs_B2D'] = dd; res['D21_B1'] = d1
    out += ['-- D21-B1', V.line(f'DiD (SV - R)_{THRF} - (SV - R)_B2D (95 %; "low" = lower bound)', dd) + f' | agent TL lower {dd["timeloss_agent"]["low"]:+.2f}',
            f'  D21-B1 publication harms the stop-thresholded family more than the control on the real street map: {"SHOWN" if d1 else "NOT SHOWN"}']
    kw = D / 'kw21_b1.txt'; out.append(kw.read_text().strip() if kw.exists() else 'KW21-B1: not run (smoke)')
    (D / f'report_w21b{SFX}.txt').write_text('\n'.join(out) + '\n'); (D / f'w21b{SFX}.json').write_text(json.dumps(res, indent=1, default=float))
else:
    sys.exit('usage: CITY_w21_report.py a|b <dir>')
print('\n'.join(out))
