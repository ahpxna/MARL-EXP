#!/usr/bin/env python3
"""F4 C1 / C2 (PROTOCOL_FIELD_F2_F3T_F4_20261008, Amendment A1): Krauss vs IDM against NGSIM Peachtree, simulated by SUMO itself.
C1  every pair runs on its own straight 4-km single-lane edge in ONE libsumo simulation (step 0.1 s): the leader (length 5 m) is placed
    at the measured gap ahead, speedMode 0, setSpeed to its forward-difference smoothed speed each step (so its position reproduces the
    measured one, KF4-2'); the follower drives the model under test (sigma 0) from its measured speed.  Error = simulated minus measured
    gap; pooled NRMSE = sqrt(sum e^2 / sum g^2).  Calibration on the train pairs: Nelder-Mead on logit-transformed bounded parameters,
    starts = SUMO defaults + 5 seeded random starts, <= 150 evaluations each; evaluation of defaults and the calibrated sets on the test
    pairs, follower-clustered bootstrap (B 2000) of NRMSE(Krauss) - NRMSE(IDM).
C2  free approaches to a stop: from the last speed maximum in the 30 s before the stop (entry speed v_e) to v < 0.5 m/s: distance, time,
    peak deceleration; SUMO: one vehicle per measured approach, entering at v_e 600 m upstream of a <stop> (same lane logic as a red),
    same statistics, for each model (defaults and calibrated, sigma 0, and Krauss sigma 0.5 averaged over 5 seeds); desired speed
    (maxSpeed, IDM's v0) = the measured entry speed, so that neither model accelerates before braking.
Usage: CITY python FIELD_f4_calib.py [calib|eval]   W_SMOKE=1: 10 train / 10 test pairs, 3 evaluations, 5 approaches."""
import hashlib, json, os, subprocess, sys, tempfile
from pathlib import Path
import numpy as np
from scipy.optimize import minimize
ROOT = Path(__file__).resolve().parents[1]; F = ROOT / 'research/field_data'; OUT = F / 'results'
sys.path.insert(0, str(ROOT / 'external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools'))
import libsumo as ls  # noqa: E402
SM = os.environ.get('W_SMOKE') == '1'; BIN = ROOT / 'external_envs/city_runtime/bin'
Z = np.load(OUT / 'f4_pairs.npz', allow_pickle=True); P = list(Z['pairs']); SPL = list(Z['split'])
TR = [p for p, s in zip(P, SPL) if s == 'train']; TE = [p for p, s in zip(P, SPL) if s == 'test']
DEF = dict(Krauss=dict(accel=2.6, decel=4.5, tau=1.0, minGap=2.5), IDM=dict(accel=2.6, decel=4.5, tau=1.0, minGap=2.5, maxSpeed=19.44))
BND = dict(accel=(0.5, 5), decel=(1, 9), tau=(0.3, 3), minGap=(0.5, 5), maxSpeed=(8, 25))
TMP = Path(tempfile.mkdtemp(prefix='f4_', dir=str(OUT)))


def build_net(n, name, length=4000.0):
    nod = TMP / f'{name}.nod.xml'; edg = TMP / f'{name}.edg.xml'; net = TMP / f'{name}.net.xml'
    if net.exists():
        return net
    nod.write_text('<nodes>\n' + ''.join(f'<node id="a{i}" x="0" y="{20 * i}"/><node id="b{i}" x="{length}" y="{20 * i}"/>\n' for i in range(n)) + '</nodes>\n')
    edg.write_text('<edges>\n' + ''.join(f'<edge id="e{i}" from="a{i}" to="b{i}" numLanes="1" speed="30"/>\n' for i in range(n)) + '</edges>\n')
    subprocess.run([str(BIN / 'netconvert'), '-n', str(nod), '-e', str(edg), '-o', str(net), '--no-turnarounds', '--no-warnings'], check=True)
    return net


def vtype(model, th, sigma=0.0, vid='fol'):
    a = ' '.join(f'{k}="{v:.6g}"' for k, v in th.items() if k != 'maxSpeed')
    ms = th.get('maxSpeed', 30.0)
    return f'<vType id="{vid}" carFollowModel="{model}" {a} maxSpeed="{ms:.6g}" sigma="{sigma}" length="5" speedFactor="1" speedDev="0"/>'


def run_pairs(pairs, model, th):
    net = build_net(len(pairs) if SM else max(len(TR), len(TE)), f'pairs{len(pairs) if SM else max(len(TR), len(TE))}')
    rou = TMP / 'pairs.rou.xml'; X0 = 100.0
    vs = [vtype(model, th), '<vType id="lead" carFollowModel="Krauss" accel="50" decel="50" emergencyDecel="50" sigma="0" length="5" maxSpeed="40" minGap="0"/>']
    for i, p in enumerate(pairs):
        g0 = p['gap'][0]
        vf0 = min(max(0.0, p['vf'][0]), th.get('maxSpeed', 30.0))       # a calibrated IDM v0 below the measured speed caps the start (counted)
        vs.append(f'<vehicle id="F{i}" type="fol" depart="0" departPos="{X0:.3f}" departSpeed="{vf0:.3f}" insertionChecks="none"><route edges="e{i}"/></vehicle>')
        vs.append(f'<vehicle id="L{i}" type="lead" depart="0" departPos="{X0 + g0 + 5.0:.3f}" departSpeed="{max(0.0, p["vl"][0]):.3f}" insertionChecks="none"><route edges="e{i}"/></vehicle>')
    rou.write_text('<routes>\n' + '\n'.join(vs) + '\n</routes>\n')
    ls.start(['sumo', '-n', str(net), '-r', str(rou), '--step-length', '0.1', '--collision.action', 'none', '--no-warnings', '--no-step-log',
              '--default.action-step-length', '0.1', '--begin', '0'])
    ls.simulationStep()
    T = max(len(p['gap']) for p in pairs); err = [[] for _ in pairs]; lerr = [[] for _ in pairs]
    for i in range(len(pairs)):
        ls.vehicle.setSpeedMode(f'L{i}', 0)
    for t in range(T - 1):
        for i, p in enumerate(pairs):
            if t < len(p['gap']) - 1:
                ls.vehicle.setSpeed(f'L{i}', max(0.0, p['vl'][t]))
        ls.simulationStep()
        for i, p in enumerate(pairs):
            if t < len(p['gap']) - 1:
                xf = ls.vehicle.getLanePosition(f'F{i}'); xl = ls.vehicle.getLanePosition(f'L{i}')
                err[i].append((xl - 5.0 - xf) - p['gap'][t + 1])
                lerr[i].append((xl - (X0 + p['gap'][0] + 5.0)) - (p['yl'][t + 1] - p['yl'][0]))
    ls.close()
    return [np.asarray(e) for e in err], [float(np.sqrt(np.mean(np.square(e)))) for e in lerr]


def nrmse(pairs, errs, idx=None):
    idx = range(len(pairs)) if idx is None else idx
    num = sum(float(np.sum(errs[i] ** 2)) for i in idx); den = sum(float(np.sum(np.square(pairs[i]['gap'][1:]))) for i in idx)
    return float(np.sqrt(num / den))


def to_th(model, z):
    ks = list(DEF[model]); return {k: BND[k][0] + (BND[k][1] - BND[k][0]) / (1 + np.exp(-zz)) for k, zz in zip(ks, z)}


def to_z(model, th):
    return np.array([np.log((th[k] - BND[k][0]) / (BND[k][1] - th[k])) for k in DEF[model]])


def calib(model):
    best = None; hist = []; nev = 3 if SM else 150; starts = [to_z(model, DEF[model])]
    rng = np.random.default_rng(0)
    for s in range(1 if SM else 5):
        starts.append(rng.normal(0, 1.0, len(DEF[model])))
    for z0 in starts:
        f = lambda z: nrmse(TR, run_pairs(TR, model, to_th(model, z))[0])  # noqa: E731
        r = minimize(f, z0, method='Nelder-Mead', options=dict(maxfev=nev, xatol=1e-3, fatol=1e-5))
        hist.append(dict(start=[float(v) for v in z0], fun=float(r.fun), th=to_th(model, r.x), nfev=int(r.nfev)))
        print(model, 'start done', hist[-1], flush=True)
        if best is None or r.fun < best[0]:
            best = (float(r.fun), to_th(model, r.x))
    return best, hist


def approach_stats(t, v, x):
    return approach_stats_raw(v, x)


def approach_stats_raw(v, x):
    s = int(np.argmax(v < 0.5)); lo = max(0, s - 300); w = v[lo:s + 1]
    j = lo + int(np.nonzero(w >= w.max() - 0.1)[0][-1])                  # end of the last speed plateau before the stop = braking onset
    a = np.diff(v[j:s + 1]) / 0.1 if s > j else np.array([0.0])
    return dict(v_e=float(v[j]), dist=float(x[s] - x[j]), time=float((s - j) * 0.1), peak_dec=float(-a.min()))


FREE = []
for q in Z['free']:
    if np.min(q['v']) < 0.5:
        st = approach_stats_raw(np.array(q['v']), np.array(q['x']))
        if st['v_e'] >= 5.0:
            FREE.append(st)
if SM:
    TR, TE, FREE = TR[:10], TE[:10], FREE[:5]


def run_approaches(model, th, sigma=0.0, seed=0):
    net = build_net(len(FREE), f'appr{len(FREE)}', 2000.0); rou = TMP / 'appr.rou.xml'; vs = []
    for i, q in enumerate(FREE):                                       # desired speed = the measured entry speed (both models; IDM's v0 too)
        vs.append(vtype(model, {**th, 'maxSpeed': q['v_e']}, sigma, vid=f'T{i}'))
        vs.append(f'<vehicle id="A{i}" type="T{i}" depart="0" departPos="400" departSpeed="{q["v_e"]:.3f}" insertionChecks="none">'
                  f'<route edges="e{i}"/><stop lane="e{i}_0" endPos="1000" duration="5"/></vehicle>')
    rou.write_text('<routes>\n' + '\n'.join(vs) + '\n</routes>\n')
    ls.start(['sumo', '-n', str(net), '-r', str(rou), '--step-length', '0.1', '--no-warnings', '--no-step-log', '--seed', str(seed),
              '--default.action-step-length', '0.1'])
    tr = {i: ([], []) for i in range(len(FREE))}
    for _ in range(1000):
        ls.simulationStep()
        for i in range(len(FREE)):
            vid = f'A{i}'
            if vid in ls.vehicle.getIDList():
                tr[i][0].append(ls.vehicle.getSpeed(vid)); tr[i][1].append(ls.vehicle.getLanePosition(vid))
    ls.close()
    return [approach_stats(None, np.array(v), np.array(x)) for v, x in tr.values()]


if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'calib'; sfx = '_smoke' if SM else ''
    if cmd == 'calib':
        res = {}
        _, l1 = run_pairs(TR, 'Krauss', DEF['Krauss']); _, l2 = run_pairs(TE, 'Krauss', DEF['Krauss'])
        drop = [p['key'] for p, r in zip(TR, l1) if r >= 0.5] + [p['key'] for p, r in zip(TE, l2) if r >= 0.5]
        print(f"KF4-2' leader RMS >= 0.5 m: train {sum(r >= 0.5 for r in l1)} / {len(TR)}, test {sum(r >= 0.5 for r in l2)} / {len(TE)} -> dropped", flush=True)
        TR[:] = [p for p in TR if p['key'] not in drop]; TE[:] = [p for p in TE if p['key'] not in drop]; res['kf42_dropped'] = drop
        for m in ('Krauss', 'IDM'):
            e, lrms = run_pairs(TR, m, DEF[m])
            best, hist = calib(m); res[m] = dict(best_train_nrmse=best[0], th=best[1], starts=hist, default_train_nrmse=nrmse(TR, e))
        (OUT / f'f4_calib{sfx}.json').write_text(json.dumps(res, indent=1, default=float)); print(json.dumps({m: (res[m]['default_train_nrmse'], res[m]['best_train_nrmse'], res[m]['th']) for m in ('Krauss', 'IDM')}, default=float))
    else:
        C = json.loads((OUT / f'f4_calib{sfx}.json').read_text()); out = ['== F4 Krauss vs IDM on NGSIM Peachtree (SUMO 1.27.1, step 0.1 s, sigma 0)']
        TR[:] = [p for p in TR if p['key'] not in C['kf42_dropped']]; TE[:] = [p for p in TE if p['key'] not in C['kf42_dropped']]
        out.append(f"KF4-2': {len(C['kf42_dropped'])} pairs dropped (scripted leader RMS >= 0.5 m); train {len(TR)}, test {len(TE)} pairs, {len({p['fol'] for p in TE})} test followers")
        E = {}
        for m in ('Krauss', 'IDM'):
            for tag, th in (('default', DEF[m]), ('calibrated', C[m]['th'])):
                e, lrms = run_pairs(TE, m, th); E[(m, tag)] = e
                out.append(f'C1 {m} {tag}: test NRMSE {nrmse(TE, e):.4f} (train {C[m]["default_train_nrmse"] if tag == "default" else C[m]["best_train_nrmse"]:.4f}); '
                           f'params {", ".join(f"{k} {v:.3g}" for k, v in th.items())}; leader RMS max {max(lrms):.3f} m')
        fol = sorted({p['fol'] for p in TE}); byf = {f: [i for i, p in enumerate(TE) if p['fol'] == f] for f in fol}; rng = np.random.default_rng(2026)
        for tag in ('default', 'calibrated'):
            obs = nrmse(TE, E[('Krauss', tag)]) - nrmse(TE, E[('IDM', tag)]); bs = []
            for _ in range(200 if SM else 2000):
                idx = [i for f in rng.choice(fol, len(fol)) for i in byf[f]]
                bs.append(nrmse(TE, E[('Krauss', tag)], idx) - nrmse(TE, E[('IDM', tag)], idx))
            lo, hi = np.percentile(bs, [2.5, 97.5])
            out.append(f'C1 NRMSE(Krauss) - NRMSE(IDM), {tag}: {obs:+.4f} [{lo:+.4f}, {hi:+.4f}] (follower bootstrap) -> '
                       f'{"IDM closer" if lo > 0 else ("Krauss closer" if hi < 0 else "no difference detected")}')
        meas = [dict(v_e=q['v_e'], dist=q['dist'], time=q['time'], peak_dec=q['peak_dec']) for q in FREE]
        def summ(L):
            return {k: (float(np.median([x[k] for x in L])), float(np.percentile([x[k] for x in L], 25)), float(np.percentile([x[k] for x in L], 75))) for k in ('dist', 'time', 'peak_dec')}
        out.append(f'C2 measured free approaches (n {len(FREE)}): ' + '; '.join(f'{k} median {v[0]:.2f} [IQR {v[1]:.2f}, {v[2]:.2f}]' for k, v in summ(meas).items()))
        for m in ('Krauss', 'IDM'):
            for tag, th in (('default', DEF[m]), ('calibrated', C[m]['th'])):
                S = run_approaches(m, th)
                d = [s['dist'] - q['dist'] for s, q in zip(S, meas)]
                out.append(f'C2 SUMO {m} {tag}: ' + '; '.join(f'{k} median {v[0]:.2f}' for k, v in summ(S).items()) + f'; median dist error {np.median(d):+.1f} m')
        S = [run_approaches('Krauss', DEF['Krauss'], 0.5, sd) for sd in range(5)]
        S = [dict(v_e=0, dist=float(np.mean([s[i]['dist'] for s in S])), time=float(np.mean([s[i]['time'] for s in S])), peak_dec=float(np.mean([s[i]['peak_dec'] for s in S]))) for i in range(len(FREE))]
        out.append('C2 SUMO Krauss default sigma 0.5 (mean of 5 seeds): ' + '; '.join(f'{k} median {v[0]:.2f}' for k, v in summ(S).items()))
        (OUT / f'f4_report{sfx}.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
