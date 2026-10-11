#!/usr/bin/env python3
"""Wave-6 reports (PROTOCOL_CITY_WAVE6_20261005).  Every M3-limit verdict checks fuel, the three time losses, teleports AND unfinished.
Paired cubes use CITY_wave2_report_v2's draws (light, fleet, traffic resampled); unpaired light sets (LCD, M2-L) resample each arm's lights
separately with fleets and traffic paired.  Usage: CITY_w6_report.py dca | h45 | m2l | lcd | sp3"""
import json, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_wave2_report_v2 as RR  # noqa: E402
from scripts.CITY_w6_validation import rows, require_panel  # noqa: E402
W = ROOT / 'research/city_sim/w6_20261005'; KK = (('fuel_agent', True), ('timeloss', False), ('timeloss_agent', False), ('timeloss_human', False))
GS = list(range(760, 780)); FL = ('s213', 's313', 's413', 's513'); LT = (4, 5, 6, 7, 8); B = 2000
import os  # noqa: E402
if os.environ.get('W6_SMOKE'):                                     # pipeline smoke: one light, one fleet, one seed, smoke directory
    W = Path(os.environ['W6_SMOKE']); GS = [int(os.environ.get('W6_SMOKE_SEED', '760'))]; FL = ('s213',); LT = (4,)


def stat(v, point, q):
    return dict(point=float(point), lo2=float(np.percentile(v, 2.5)), hi2=float(np.percentile(v, 97.5)), up=float(np.percentile(v, q)), low=float(np.percentile(v, 100 - q)))


def paired(Rt, a, b, L, F, S, q=95.0):
    """a(l, f) / b(l, f) -> row keys; cube [L, F, S] of a - b."""
    require_panel(Rt, [key(l, f) for key in (a, b) for l in L for f in F], S)
    r = {}
    for k, pct in KK:
        c = np.array([[[100 * (Rt[a(l, f)][s][k] / Rt[b(l, f)][s][k] - 1) if pct else Rt[a(l, f)][s][k] - Rt[b(l, f)][s][k] for s in S] for f in F] for l in L])
        dr = RR.draws(c.shape); v = np.array([c[np.ix_(*ix)].mean() for ix in dr]); r[k] = stat(v, c.mean(), q)
    return r


def cube(Rt, key, L, F, S, k):
    require_panel(Rt, [key(l, f) for l in L for f in F], S, metrics=(k,))
    return np.array([[[Rt[key(l, f)][s][k] for s in S] for f in F] for l in L], float)


def unpaired(Rt, ka, La, kb, Lb, F, S, q=95.0, seed=0, metrics=None):
    """mean over arm A's cells minus arm B's (fuel: ratio of means - 1, %); lights resampled per arm, fleets / traffic shared."""
    rng = np.random.default_rng(seed); r = {}
    idx = [(rng.integers(0, len(La), len(La)), rng.integers(0, len(Lb), len(Lb)), rng.integers(0, len(F), len(F)), rng.integers(0, len(S), len(S))) for _ in range(B)]
    for k, pct in (KK if metrics is None else [x for x in KK if x[0] in metrics]):
        A, Bc = cube(Rt, ka, La, F, S, k), cube(Rt, kb, Lb, F, S, k)
        f = (lambda x, y: 100 * (x / y - 1)) if pct else (lambda x, y: x - y)
        v = np.array([f(A[np.ix_(ia, jf, js)].mean(), Bc[np.ix_(ib, jf, js)].mean()) for ia, ib, jf, js in idx]); r[k] = stat(v, f(A.mean(), Bc.mean()), q)
    return r


def did(Rt, a1, r1, L1, a0, r0, L0, F, S, q=95.0, seed=0):
    """(A1 - R1 under L1) - (A0 - R0 under L0); per-light benefits, lights resampled per set, fleets / traffic shared."""
    rng = np.random.default_rng(seed); r = {}
    idx = [(rng.integers(0, len(L1), len(L1)), rng.integers(0, len(L0), len(L0)), rng.integers(0, len(F), len(F)), rng.integers(0, len(S), len(S))) for _ in range(B)]
    for k, pct in KK:
        g = (lambda x, y: 100 * (x / y - 1)) if pct else (lambda x, y: x - y)
        b1 = g(cube(Rt, a1, L1, F, S, k), cube(Rt, r1, L1, F, S, k)); b0 = g(cube(Rt, a0, L0, F, S, k), cube(Rt, r0, L0, F, S, k))
        v = np.array([b1[np.ix_(i1, jf, js)].mean() - b0[np.ix_(i0, jf, js)].mean() for i1, i0, jf, js in idx]); r[k] = stat(v, b1.mean() - b0.mean(), q)
    return r


def tele(Rt, key, L, F, S):
    t = [Rt[key(l, f)][s]['teleports'] for l in L for f in F for s in S]; u = [Rt[key(l, f)][s]['unfinished'] for l in L for f in F for s in S]
    return float(np.mean(t)), float(np.mean(u))


def line(n, r):
    return f'  {n}: ' + ' | '.join(f'{k} {v["point"]:+.2f} [{v["lo2"]:+.2f}, {v["hi2"]:+.2f}] (up {v["up"]:+.2f})' for k, v in r.items())


def limits(r, ta, tb):
    ok = r['fuel_agent']['up'] < 0 and all(r[q]['up'] < 0.5 for q in ('timeloss', 'timeloss_agent', 'timeloss_human')) and ta[0] <= tb[0] + 0.1 and ta[1] <= tb[1]
    return ok, f'teleports/run {ta[0]:.3f} vs {tb[0]:.3f}, unfinished/run {ta[1]:.3f} vs {tb[1]:.3f}'


def complete(Rt, keys):
    miss = [k for k in keys if k not in Rt]; bad = [k for k in keys if k in Rt and sorted(Rt[k]) != sorted(GS)]
    if bad: raise ValueError(f'SEED MISMATCH: {bad}')
    return miss, bad


def dca():
    D = W / 'dca'; Rt = rows(D / 'conf'); out = ['== W6-1 DCA (lights t4-t8 x fleets s213-s513 x traffic 760-779; DC-Ada affine adapter vs TSI-2 physical adapter, matched budget 44)']
    keys = [f'{a}_t{l}_{f}' for a in ('R', 'TSI2', 'DCA') for l in LT for f in FL]; miss, _ = complete(Rt, keys)
    if miss:
        print('INCOMPLETE', miss[:5], len(miss)); sys.exit(1)
    if any(sorted(Rt[k]) != GS for k in keys):
        print('SEED MISMATCH'); sys.exit(1)
    K = lambda a: (lambda l, f: f'{a}_t{l}_{f}')
    for a in ('TSI2', 'DCA'):
        r = paired(Rt, K(a), K('R'), LT, FL, GS); ok, tl = limits(r, tele(Rt, K(a), LT, FL, GS), tele(Rt, K('R'), LT, FL, GS))
        out += [line(f'{a} - R', r), f'  {a}: all M3 limits (incl. teleports, unfinished): {ok}; {tl}']
    d = paired(Rt, K('TSI2'), K('DCA'), LT, FL, GS); out.append(line('TSI2 - DCA', d)); f, t = d['fuel_agent'], d['timeloss_agent']
    order = 'TSI better' if (f['up'] <= 0 and t['up'] <= 0 and (f['up'] < 0 or t['up'] < 0)) else ('DCA better' if (f['low'] >= 0 and t['low'] >= 0 and (f['low'] > 0 or t['low'] > 0)) else 'no ordering')
    out.append(f'  W6-1 (b) ordering on agent fuel and agent TL (one-sided 95 %): {order}')
    th = {l: json.loads((D / 'tune' / f'dca_t{l}.json').read_text()) for l in LT}
    out.append('  DCA tuning: ' + '; '.join(f't{l} rollouts {th[l]["rollouts"]} accepted {sum(1 for x in th[l]["log"] if x.get("accepted"))}/4' for l in LT))
    print('\n'.join(out)); (D / 'report_dca.txt').write_text('\n'.join(out) + '\n')


def h45():
    D = W / 'h45'; Rt = rows(D / 'conf'); out = ['== W6-2 / W6-3 H4 (fine-tune + std / value reset) and H5 (Lagrangian on agent TL) (t4-t8 x 4 fleets x 760-779)']
    FP = (('s213', 't4'), ('s313', 't5'), ('s413', 't6'), ('s513', 't7')); F = (0,) if os.environ.get('W6_SMOKE') else tuple(range(4))
    K = lambda a: (lambda l, i: f'{a}_t{l}_{FP[i][0]}_{FP[i][1]}' if a != 'R' else f'R_t{l}_{FP[i][0]}')
    keys = [K(a)(l, i) for a in ('R', 'F1B', 'H4', 'H5') for l in LT for i in F]; miss, _ = complete(Rt, keys)
    if miss:
        print('INCOMPLETE', miss[:5], len(miss)); sys.exit(1)
    for a in ('F1B', 'H4', 'H5'):
        r = paired(Rt, K(a), K('R'), LT, F, GS); ok, tl = limits(r, tele(Rt, K(a), LT, F, GS), tele(Rt, K('R'), LT, F, GS))
        out += [line(f'{a} - R', r), f'  {a}: all M3 limits: {ok}; {tl}']
    for a in ('H4', 'H5'):
        out.append(line(f'{a} - F1B', paired(Rt, K(a), K('F1B'), LT, F, GS)))
    print('\n'.join(out)); (D / 'report_h45.txt').write_text('\n'.join(out) + '\n')


def m2l():
    D = W / 'm2l'; Rt = rows(D / 'conf'); st = json.loads((D / 'stage0.json').read_text()); L1 = tuple(st['lights']); fam = st['family']
    if os.environ.get('W6_SMOKE'):
        L1 = L1[:1]
    FP = (('s213', 't4'), ('s313', 't5'), ('s413', 't6'), ('s513', 't7')); F = (0,) if os.environ.get('W6_SMOKE') else tuple(range(4))
    out = [f'== W6-5 M2-L (L0 = RL-H t4-t8, F0 = F1-B fleets, L1 = {fam} {list(L1)} [{st["label"]}]; traffic 760-779)']
    k0 = lambda a: (lambda l, i: f'{a}_L0t{l}_{FP[i][0]}'); k1 = lambda a: (lambda l, i: f'{a}_L1{l}_{FP[i][0]}')
    keys = [k0(a)(l, i) for a in ('R0', 'F0c') for l in LT for i in F] + [k1(a)(l, i) for a in ('R1', 'F0n', 'F0r') for l in L1 for i in F]; miss, _ = complete(Rt, keys)
    if miss:
        print('INCOMPLETE', miss[:5], len(miss)); sys.exit(1)
    b0 = paired(Rt, k0('F0c'), k0('R0'), LT, F, GS); out.append(line('B0 = F0c - R0 (under L0)', b0))
    b0ok, b0counts = limits(b0, tele(Rt, k0('F0c'), LT, F, GS), tele(Rt, k0('R0'), LT, F, GS))
    out.append(f'  Baseline fleet useful under L0 (all limits): {b0ok}; {b0counts}')
    upgrade = unpaired(Rt, k1('R1'), L1, k0('R0'), LT, F, GS)
    out += [line('Fresh-panel L1 - L0 baseline', upgrade), f'  Fresh-panel city-TL upgrade: {upgrade["timeloss"]["up"] < 0}; selected DEV label is provisional']
    for a in ('F0n', 'F0r'):
        r = paired(Rt, k1(a), k1('R1'), L1, F, GS); ok, tl = limits(r, tele(Rt, k1(a), L1, F, GS), tele(Rt, k1('R1'), L1, F, GS))
        out += [line(f'B1 {a} - R1 (under L1)', r), f'  {a}: all M3 limits vs R1: {ok}; {tl}']
        if a == 'F0n':
            rh = paired(Rt, k1(a), k1('R1'), L1, F, GS, q=97.5)
            harm = rh['fuel_agent']['low'] > 0 or rh['timeloss_agent']['low'] > 0.5
        else:
            info_ok = ok
    dn = did(Rt, k1('F0n'), k1('R1'), L1, k0('F0c'), k0('R0'), LT, F, GS); dr_ = did(Rt, k1('F0r'), k1('R1'), L1, k0('F0c'), k0('R0'), LT, F, GS)
    out += [line('DiD naive (B1n - B0)', dn), line('DiD refit (B1r - B0)', dr_)]
    out.append(f'  W6-5 LOSS (DiD naive fuel lower > 0): {dn["fuel_agent"]["low"] > 0}; HARM (two endpoints, Bonferroni): {harm}; INFORMATION UPDATE SUFFICES: {info_ok}')
    print('\n'.join(out)); (D / 'report_m2l.txt').write_text('\n'.join(out) + '\n')


def lcd():
    D = W / 'lcd'; out = ['== W6-4 LCD (learned committed-duration light, exact SPaT)']; g = json.loads((D / 'gate.json').read_text()); out.append('  DEV gate: ' + json.dumps(g))
    if not g['pass']:
        out.append('  W6-4: DEV GATE FAILED -> no confirmation (registered)'); print('\n'.join(out)); (D / 'report_lcd.txt').write_text('\n'.join(out) + '\n'); return
    Rt = rows(D / 'conf'); J = (0, 1); F = FL
    ka = lambda l, f: f'LCDF_j{l}_{f}'; kr = lambda l, f: f'R_t{l}_{f}'
    r = unpaired(Rt, ka, J, kr, LT, F, GS); ok, tl = limits(r, tele(Rt, ka, J, F, GS), tele(Rt, kr, LT, F, GS))
    out += [line('LCDF - R (lights unpaired)', r), f'  W6-4 all M3 limits: {ok}; {tl}']
    ra = unpaired(Rt, lambda l, f: f'LCDA_j{l}', J, lambda l, f: f'RLHA_t{l}', LT, ('x',), GS, metrics=('timeloss',)); out.append(line('LCD alone - RL-H alone (SUMO cars)', ra))
    sidecars = [D / 'conf' / f'LCDF_j{j}_{f}_n8.json' for j in J for f in F]
    for p in sidecars:
        d = json.loads(p.read_text()); assert d['checked'] > 0 and d['mism'] == 0, (p, d)
        assert sorted(x['seed'] for x in d['kn8_1']) == sorted(GS), p
    print('\n'.join(out)); (D / 'report_lcd.txt').write_text('\n'.join(out) + '\n')


def sp3():
    D = W / 'sp3'; Rt = rows(D / 'conf'); S = list(range(1150, 1170)); L = (11, 111); F = ('rule',)
    if os.environ.get('W6_SMOKE'):
        S, L = GS, (11,)
    out = ['== W6-6 SPIDER-3 (third and last attempt; direct-cells-only service + adapter; lights RLK11 / RLK111 x rule fleet x fresh 1150-1169)']
    ch = json.loads((D / 'tune' / 'choice.json').read_text()); out.append('  per-light (A, B): ' + ', '.join(f'RLK{k} ({ch[str(k)]["choice"]})' for k in L))
    K = lambda a: (lambda l, f: f'{a}_{l}')
    for a in ('TSIK3', 'SVC3', 'ADPK3'):
        r = paired(Rt, K(a), K('R'), L, F, S, q=98.75); out.append(line(f'{a} - R', r).replace('(up', '(up98.75'))
        if a == 'TSIK3':
            ok, tl = limits(r, tele(Rt, K(a), L, F, S), tele(Rt, K('R'), L, F, S)); verdict = ok; out.append(f'  {tl}')
    st = [json.loads((D / 'conf' / f'{a}_{l}_tk.json').read_text()) for a in ('TSIK3','SVC3') for l in L]
    for d in st:
        p = d['provider']; assert p['exc'] == 0 and p['valid'] > 0, p
        checks = d['realized_checks']; assert sorted(c['seed'] for c in checks) == sorted(S), checks
        assert sum(c['checked'] for c in checks) > 0 and sum(c['mismatches'] for c in checks) == 0, checks
    out.append('  provider counters: ' + '; '.join(json.dumps(x.get('provider', {})) for x in st))
    out.append(f'  SECOND-SETTING REPLICATION VERDICT (attempt 3, alpha 0.0125 one-sided): {"PASS" if verdict else "FAIL"}')
    print('\n'.join(out)); (D / 'report_sp3.txt').write_text('\n'.join(out) + '\n')


if __name__ == '__main__':
    dict(dca=dca, h45=h45, m2l=m2l, lcd=lcd, sp3=sp3)[sys.argv[1]]()
