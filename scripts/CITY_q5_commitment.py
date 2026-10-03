#!/usr/bin/env python3
"""Q5 (research/city_sim/PROTOCOL_CITY_Q5_COMMITMENT_20261002.md, written 19:2x EDT 02/10/2026): honest [minEnd, maxEnd]
commitment windows.  Queue model of one intersection (approaches A, B); lights ADAPT (w = inf), COMMIT(w), REVISE1, FIXED;
light objective = mean delay per vehicle; probe cars on A with C0 dynamics (scripts/CITY_c0_testbed.py v3, imported):
PRIVILEGED (regret 0), RULE (no SPaT), WINDOW (uses the published window).  Car metric = regret of WINDOW.
Usage: CITY_q5_commitment.py --out DIR [--smoke] [--workers 2]"""
from __future__ import annotations
import argparse, hashlib, importlib.util, json, time
from collections import deque
from multiprocessing import Pool
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]; C0P = ROOT / 'scripts' / 'CITY_c0_testbed.py'
spec = importlib.util.spec_from_file_location('c0', C0P); c0 = importlib.util.module_from_spec(spec); spec.loader.exec_module(c0)
T, XM, ACC = c0.T, c0.XM, c0.ACC
GMIN, GMAX, ALLRED, H = 10, 60, 4, 7200
WS = [0, 2, 5, 10, 20, 40]; DEMANDS = [(0.20, 0.15), (0.25, 0.20), (0.30, 0.25)]


def simulate(kind, w, lam, seed, split=None, delta=2, cslope=2):
    rng = np.random.default_rng([seed, int(lam[0] * 100), int(lam[1] * 100)]); q = [deque(), deque()]; delays = []
    gA = np.zeros(H + T + 4, bool); lo = np.zeros(H + T + 4, np.int32); hi = np.zeros(H + T + 4, np.int32)
    cur, t0, allred, nxt = 0, 0, 0, 1

    def plan(t, cur):
        if kind == 'FIXED':
            d = split[cur]; return d, d
        if kind == 'ADAPT':
            return GMIN, GMAX
        D = int(np.clip(GMIN + cslope * len(q[cur]), GMIN, GMAX)); return max(GMIN, D - w // 2), max(GMIN, D + (w - w // 2))
    wlo, whi = plan(0, 0); revised = False
    for t in range(H + T + 4):
        for k in (0, 1):
            if t < H and rng.random() < lam[k]:
                q[k].append(t)
        if allred > 0:
            allred -= 1; gA[t] = False
            if nxt == 0:                                   # A starts next: window = remaining all-red
                lo[t] = hi[t] = allred + 1
            else:                                          # B starts next, then A: A's green after B's whole phase
                lo[t] = allred + 1 + GMIN + ALLRED; hi[t] = allred + 1 + GMAX + ALLRED
            if allred == 0:
                cur, t0 = nxt, t + 1; wlo, whi = plan(t + 1, cur); revised = False
            continue
        spent = t - t0 + 1
        if q[cur] and rng.random() < 0.5:
            delays.append(t - q[cur].popleft())
        if kind == 'REVISE1' and not revised and spent >= max(1, wlo // 2):
            D = int(np.clip(spent + cslope * len(q[cur]), GMIN, GMAX)); wlo = whi = max(D, spent + 1); revised = True
        gap = len(q[cur]) == 0 and len(q[1 - cur]) > 0
        cond = gap if delta == 'gap' else (len(q[1 - cur]) >= len(q[cur]) + delta or gap)
        if kind == 'FIXED':
            sw = spent >= whi
        else:
            sw = spent >= whi or (spent >= wlo and cond)
        gA[t] = cur == 0
        rem_lo, rem_hi = max(0, wlo - spent), max(0, whi - spent)
        if cur == 0:
            lo[t], hi[t] = rem_lo + 1, rem_hi + 1
        else:
            lo[t], hi[t] = rem_lo + 1 + ALLRED, rem_hi + 1 + ALLRED
        if sw:
            allred, nxt = ALLRED, 1 - cur
    waiting = [H + T + 4 - a for k in (0, 1) for a in q[k]]
    return dict(delay=float(np.mean(delays + waiting)), served=len(delays), censored=len(waiting)), gA, lo, hi


def car_panel(gA, lo, hi, n, seed):
    rng = np.random.default_rng(seed); ts = rng.integers(600, H - 300, n)
    G = np.stack([gA[s:s + T + 2] for s in ts]); LO = np.stack([lo[s:s + T + 2] for s in ts]); HI = np.stack([hi[s:s + T + 2] for s in ts])
    x0 = -rng.integers(150, 251, n); v0 = rng.integers(8, 13, n); topt = np.empty(n)
    for i in range(0, n, 200):
        V0 = c0.dp_batch(G[i:i + 200], tab=False, dtype=np.float64); k = np.arange(len(V0)); topt[i:i + 200] = V0[k, x0[i:i + 200] + XM, v0[i:i + 200]]
    z = np.zeros_like(LO)
    return dict(green=G, tau=z, res=z, lo=LO, hi=HI, x0=x0, v0=v0, topt=topt)


def to_action(a):
    return np.searchsorted(ACC, np.clip(np.round(a), -3, 2).astype(int))


def window_policy(P):
    def f(x, v, g, ta, rs, idx, t):
        lo, hi = P['lo'][idx, t].astype(float), P['hi'][idx, t].astype(float); dist = -x.astype(float); v = v.astype(float)
        treach = dist / np.maximum(v, 1.0); sd = v * v / 6.0 + v
        vd = np.where(g, np.where(treach <= lo - 1, 12.0, np.where(treach > hi, dist / (hi + GMIN + ALLRED), 12.0)), dist / np.maximum(lo, 1.0))
        a = np.clip(vd - v, -3, 2)
        a = np.where((~g) & (dist <= sd + 6) & (lo > 1), -3, a)        # red: never reach the line before the earliest green
        return to_action(a)
    return f


def rollout(act, P):
    N = len(P['x0']); x = P['x0'].copy(); v = P['v0'].copy(); alive = np.ones(N, bool); cost = np.zeros(N); viol = np.zeros(N)
    for t in range(T):
        idx = np.flatnonzero(alive)
        if len(idx) == 0:
            break
        ai = act(x[idx], v[idx], P['green'][idx, t], P['tau'][idx, t], P['res'][idx, t], idx, t)
        x2, v2, c, passed, forced = c0.step(x[idx], v[idx], ai, P['green'][idx, t + 1]); cost[idx] += c; viol[idx] += forced
        x[idx], v[idx] = x2, v2; alive[idx[passed]] = False
    cost[alive] += c0.TIMEOUT
    return cost - P['topt'], viol


def job(args):
    kind, w, lam, seed, ncar, split, delta, cslope = args
    st, gA, lo, hi = simulate(kind, w, lam, seed, split, delta, cslope)
    out = dict(kind=kind, w=w, lam=list(lam), seed=seed, split=split, delta=delta, cslope=cslope, **st)
    if ncar:
        P = car_panel(gA, lo, hi, ncar, 9600 + seed)
        rw, vw = rollout(window_policy(P), P); rr, vr = rollout(lambda x, v, g, ta, rs, idx, t: c0.rule_policy(x, v, g, ta, rs), P)
        out.update(window_regret=float(rw.mean()), window_viol=float(vw.mean()), rule_regret=float(rr.mean()), rule_viol=float(vr.mean()))
    return out


def report(rows, out):
    L = ['Q5 light delay G_L (s/veh) and WINDOW-car regret H_C by light (mean over seeds); RULE-car regret in brackets']
    pred = {}
    for lam in [d for d in DEMANDS if any(tuple(r['lam']) == d for r in rows)]:
        R = [r for r in rows if tuple(r['lam']) == lam]
        def m(kind, w=None, key='delay'):
            vals = [r[key] for r in R if r['kind'] == kind and (w is None or r['w'] == w) and key in r]
            return float(np.mean(vals)) if vals else float('nan')
        fx = [r for r in R if r['kind'] == 'FIXED']; best = min({tuple(r['split']) for r in fx}, key=lambda sp: np.mean([r['delay'] for r in fx if tuple(r['split']) == sp]))
        ga, ha = m('ADAPT'), m('ADAPT', key='window_regret'); g0, h0 = m('COMMIT', 0), m('COMMIT', 0, 'window_regret')
        L.append(f'demand {lam}: ADAPT G {ga:.1f} H {ha:.2f} [{m("ADAPT", key="rule_regret"):.2f}]; ' + '; '.join(
            f'COMMIT({w}) G {m("COMMIT", w):.1f} H {m("COMMIT", w, "window_regret"):.2f} [{m("COMMIT", w, "rule_regret"):.2f}]' for w in WS) +
            f'; REVISE1 G {m("REVISE1"):.1f} H {m("REVISE1", key="window_regret"):.2f}; FIXED best {best} G {np.mean([r["delay"] for r in fx if tuple(r["split"]) == best]):.1f}')
        ok1 = [w for w in WS if w <= 10 and m('COMMIT', w) <= 1.05 * ga and m('COMMIT', w, 'window_regret') <= 1.25 * h0]
        pred[f'P5-1 demand {lam}: some w <= 10 within 5 % of ADAPT and 25 % of COMMIT(0) car regret'] = dict(windows=ok1, pass_=bool(ok1))
        pred[f'P5-2 demand {lam}: REVISE1 within 5 % and 25 %'] = dict(G=m('REVISE1'), G_adapt=ga, H=m('REVISE1', key='window_regret'), H0=h0,
                                                                       pass_=bool(m('REVISE1') <= 1.05 * ga and m('REVISE1', key='window_regret') <= 1.25 * h0))
    L += [f'{k}: {"SUPPORTED" if v["pass_"] else "NOT SUPPORTED"} {json.dumps({kk: vv for kk, vv in v.items() if kk != "pass_"})}' for k, v in pred.items()]
    txt = '\n'.join(L); print(txt, flush=True); (out / 'report.txt').write_text(txt + '\n')


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=a.smoke); ncar = 60 if a.smoke else 1000; seeds = [0] if a.smoke else [0, 1, 2]
    jobs = []; tuned = {}
    for lam in (DEMANDS[:1] if a.smoke else DEMANDS):              # Addendum 1: tune delta (ADAPT) and c (COMMIT(0)) on seeds 100-102
        dl = {d: np.mean([simulate('ADAPT', None, lam, ts, None, d, 2)[0]['delay'] for ts in (100, 101, 102)]) for d in (2, 4, 6, 8, 12, 'gap')}
        bd = min(dl, key=dl.get)
        cl = {c: np.mean([simulate('COMMIT', 0, lam, ts, None, bd, c)[0]['delay'] for ts in (100, 101, 102)]) for c in (1, 2, 3, 4)}
        bc = min(cl, key=cl.get); tuned[str(lam)] = dict(delta=bd, cslope=bc, delta_grid={str(k): float(v) for k, v in dl.items()}, c_grid={str(k): float(v) for k, v in cl.items()})
        print(f'tuning {lam}: delta {bd} ({dl[bd]:.1f}), c {bc} ({cl[bc]:.1f})', flush=True)
        for s in seeds:
            jobs += [('ADAPT', None, lam, s, ncar, None, bd, bc), ('REVISE1', 0, lam, s, ncar, None, bd, bc)] + [('COMMIT', w, lam, s, ncar, None, bd, bc) for w in WS]
            jobs += [('FIXED', None, lam, s, 0, [ga, gb], bd, bc) for ga in (15, 20, 25, 30) for gb in (10, 15, 20, 25)]
    (out / 'tuning.json').write_text(json.dumps(tuned, indent=1))
    t0 = time.perf_counter(); rows = []
    with Pool(a.workers) as pool:
        for r in pool.imap_unordered(job, jobs):
            rows.append(r)
            if 'window_regret' in r:
                print(f'[{time.perf_counter() - t0:.0f}s] {r["kind"]} w {r["w"]} lam {r["lam"]} s{r["seed"]}: delay {r["delay"]:.1f} window {r["window_regret"]:.2f} rule {r["rule_regret"]:.2f}', flush=True)
            (out / 'rows.json').write_text(json.dumps(rows, indent=1))
    report(rows, out)
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', q5_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                                                       c0_sha256=hashlib.sha256(C0P.read_bytes()).hexdigest(), n_jobs=len(jobs), smoke=a.smoke), indent=1))


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--out', required=True); ap.add_argument('--smoke', action='store_true')
    ap.add_argument('--workers', type=int, default=2); main(ap.parse_args())
