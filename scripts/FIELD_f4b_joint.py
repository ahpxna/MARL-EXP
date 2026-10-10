#!/usr/bin/env python3
"""W17-0 / FIELD F4b (PROTOCOL_CITY_WAVE17_20261008; PROTOCOL_FIELD A4): one IDM calibrated jointly on car following (spacing NRMSE on F4's
train pairs) and stop approaches (E_C2 on 60 % of F4's free approaches, split by sha1(key)), with SUMO itself (F4's harness, imported).
  J = NRMSE + 0.5 * E_C2,  E_C2 = mean_i (|log d_sim/d_meas| + |log t_sim/t_meas| + |log a_sim/a_meas|) / 3 (braking distance, time, peak decel).
  IDM parameters accel, decel, tau, minGap, delta in [2, 8], maxSpeed (car following only; C2 uses the entry speed).  Nelder-Mead from the F4
  IDM calibration (delta 4) + 3 seeded starts, <= 150 evaluations each.  Test report for joint IDM, F4 IDM, Krauss default / calibrated.
  Gate G17-0: joint test E_C2 < Krauss default and < F4 IDM, and joint test NRMSE <= F4 IDM + 0.05.
Outputs research/field_data/results/f4b_joint.json, f4b_report.txt, and research/city_sim/w17_20261008/human.json (world vType; no maxSpeed).
W_SMOKE=1: F4's smoke subsets, 3 evaluations, 1 start."""
import hashlib, importlib.util, json, os, sys
from pathlib import Path
import numpy as np
from scipy.optimize import minimize
ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('f4', ROOT / 'scripts/FIELD_f4_calib.py'); F4 = importlib.util.module_from_spec(spec); spec.loader.exec_module(F4)
SM = os.environ.get('W_SMOKE') == '1'; OUT = F4.OUT; sfx = '_smoke' if SM else ''
C = json.loads((OUT / f'f4_calib{sfx}.json').read_text()) if (OUT / f'f4_calib{sfx}.json').exists() else json.loads((OUT / 'f4_calib.json').read_text())
drop = set(C.get('kf42_dropped', [])); TR = [p for p in F4.TR if p['key'] not in drop]; TE = [p for p in F4.TE if p['key'] not in drop]
Z = np.load(OUT / 'f4_pairs.npz', allow_pickle=True); APP = []
for q in Z['free']:
    if np.min(q['v']) < 0.5:
        st = F4.approach_stats_raw(np.array(q['v']), np.array(q['x']))
        if st['v_e'] >= 5.0:
            APP.append((q['key'], st))
ATR = [s for k, s in APP if int(hashlib.sha1(k.encode()).hexdigest(), 16) % 10 < 6]; ATE = [s for k, s in APP if int(hashlib.sha1(k.encode()).hexdigest(), 16) % 10 >= 6]
if SM:
    TR, TE, ATR, ATE = TR[:10], TE[:10], ATR[:5], ATE[:5]
BND = dict(F4.BND, delta=(2.0, 8.0)); KS = ['accel', 'decel', 'tau', 'minGap', 'delta', 'maxSpeed']


def e_c2(model, th, A, sigma=0.0):
    F4.FREE = A; S = F4.run_approaches(model, th, sigma)
    eps = 1e-3; L = [(abs(np.log(max(s['dist'], eps) / max(q['dist'], eps))) + abs(np.log(max(s['time'], eps) / max(q['time'], eps)))
                      + abs(np.log(max(s['peak_dec'], eps) / max(q['peak_dec'], eps)))) / 3 for s, q in zip(S, A)]
    med = {k: float(np.median([s[k] for s in S])) for k in ('dist', 'time', 'peak_dec')}
    return float(np.mean(L)), med


def to_th(z):
    return {k: BND[k][0] + (BND[k][1] - BND[k][0]) / (1 + np.exp(-zz)) for k, zz in zip(KS, z)}


def to_z(th):
    return np.array([np.log((th[k] - BND[k][0]) / (BND[k][1] - th[k])) for k in KS])


def J(th):
    return F4.nrmse(TR, F4.run_pairs(TR, 'IDM', th)[0]) + 0.5 * e_c2('IDM', th, ATR)[0]


start = dict(C['IDM']['th'], delta=4.0); starts = [to_z(start)]; rng = np.random.default_rng(0)
for _ in range(1 if SM else 3):
    starts.append(to_z(start) + rng.normal(0, 0.7, len(KS)))
best = None; hist = []
for z0 in starts:
    r = minimize(lambda z: J(to_th(z)), z0, method='Nelder-Mead', options=dict(maxfev=3 if SM else 150, xatol=1e-3, fatol=1e-5))
    hist.append(dict(fun=float(r.fun), th=to_th(r.x), nfev=int(r.nfev))); print('start done', hist[-1], flush=True)
    if best is None or r.fun < best[0]:
        best = (float(r.fun), to_th(r.x))
TJ = best[1]; out = [f'== W17-0 joint IDM calibration (train J {best[0]:.4f}); pairs train {len(TR)} test {len(TE)}; approaches train {len(ATR)} test {len(ATE)}',
                     'joint IDM: ' + ', '.join(f'{k} {v:.3g}' for k, v in TJ.items())]
meas = {k: float(np.median([q[k] for q in ATE])) for k in ('dist', 'time', 'peak_dec')}
out.append(f'measured test approaches: dist {meas["dist"]:.1f} m, time {meas["time"]:.1f} s, peak {meas["peak_dec"]:.2f} m/s2')
res = {}
for nm, model, th in (('joint IDM', 'IDM', TJ), ('F4 IDM', 'IDM', C['IDM']['th']), ('Krauss default', 'Krauss', F4.DEF['Krauss']), ('Krauss calibrated', 'Krauss', C['Krauss']['th'])):
    nr = F4.nrmse(TE, F4.run_pairs(TE, model, th)[0]); ec, med = e_c2(model, th, ATE); res[nm] = dict(nrmse=nr, e_c2=ec, med=med)
    out.append(f'{nm}: test NRMSE {nr:.4f}; test E_C2 {ec:.3f}; approach medians dist {med["dist"]:.1f} m, time {med["time"]:.1f} s, peak {med["peak_dec"]:.2f}')
g = res['joint IDM']['e_c2'] < res['Krauss default']['e_c2'] and res['joint IDM']['e_c2'] < res['F4 IDM']['e_c2'] and res['joint IDM']['nrmse'] <= res['F4 IDM']['nrmse'] + 0.05
out.append(f'G17-0: {"PASS" if g else "FAIL"}')
(OUT / f'f4b_joint{sfx}.json').write_text(json.dumps(dict(best=best, starts=hist, test=res, gate=g), indent=1, default=float))
(OUT / f'f4b_report{sfx}.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
if not SM:
    W = ROOT / 'research/city_sim/w17_20261008'; W.mkdir(parents=True, exist_ok=True)
    (W / 'human.json').write_text(json.dumps(dict(carFollowModel='IDM', **{k: round(float(TJ[k]), 4) for k in ('accel', 'decel', 'tau', 'minGap', 'delta')}, gate=g), indent=1))
