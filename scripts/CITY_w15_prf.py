#!/usr/bin/env python3
"""W15-6 (PROTOCOL_CITY_WAVE15_20261007, Amendment A2): the policy-aware forecaster (PRF).  The provider knows the deployed light's frozen
DQN (checkpoint of W15_PRF_LIGHT, e.g. RL-H:14) and its input adapter (A, B).  At a query second t on a green, for that light it projects
both served lane groups forward one second at a time:
  queue      = halting vehicles now, plus approaching vehicles once their ETA (distance / max(speed, 2 m/s)) has passed, unless their group is
               green with an empty queue (then they pass);
  discharge  = on the current green, n_lanes / 2 vehicles per second;
and at every decision epoch (multiples of 5 s, spent >= 5 s) builds the observation the light would see, with the adapter applied
(h + A n[0.1,2) + B n[2,5) from the not-yet-arrived vehicles' current speeds; vehicle count = queue + not arrived), evaluates the DQN on all
epochs in one batch and takes the first switch.  Answers: time-to-red T + 1, time-to-green of the other green T + 3 + 1 (yellow 3 s,
observation offset 1 s, the c2 convention).  Yellow answers, all-green links and gating are those of the wrapped N4 hybrid provider; if no
switch is projected within 120 s the N4 answer is used (counted).  W15_PRF="A:B:variant": variant prf = projection answer; prfq = never later
than the wrapped provider's answer (run it at q 0.1).  Counters (prf, fallback, shadow switch error) are added to the provider's stats.
Patches CITY_spat_forecast_n4.make_spat_n4; no file is edited.  Usage: W15_PRF=1:0.25:prf W15_PRF_LIGHT=RL-H:14 CITY_w15_prf.py <target> <args>"""
import os, runpy, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import torch  # noqa: E402
import scripts.CITY_w8_run  # noqa: E402,F401  (light_spec 4..18)
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_eval4 as E4  # noqa: E402
import scripts.CITY_xplay2 as X2  # noqa: E402
import scripts.CITY_spat_forecast_n4 as N4  # noqa: E402
A, B, VAR = os.environ['W15_PRF'].split(':'); A, B = float(A), float(B); assert VAR in ('prf', 'prfq'), VAR
LSPEC = os.environ['W15_PRF_LIGHT']; ARR = os.environ.get('W15_PRF_ARR', '1') == '1'; H = 120; YEL, DTL, MING, OFF = CE.YELLOW, CE.DT_L, CE.MIN_G, 1.0
_make = N4.make_spat_n4


def make(model_path, q, info, tracker, gate):
    base = _make(model_path, q, info, tracker, gate); stats = base.stats; stats.update(prf=0, prf_fallback=0, sw_err_n=0, sw_err_abs=0.0, sw_err_sum=0.0, mlp_err_n=0, mlp_err_abs=0.0, mlp_err_sum=0.0)
    _, ck, _ = X2.light_spec(LSPEC); net = torch.load(ck, weights_only=False)['net']; net.eval()
    Ws = [(m.weight.detach().numpy().astype(np.float64), m.bias.detach().numpy().astype(np.float64)) for m in net if isinstance(m, torch.nn.Linear)]
    lens, cache, track, st_cache = {}, {}, {}, {}
    arr = {}                                                          # (tid, group) -> [seen ids, new count, first t, last t]
    def lam(tid, gi, lanes, t):
        ls = CE.ls; s = arr.setdefault((tid, gi), [set(), 0, t, t]); ids = set()
        for l in lanes:
            ids.update(ls.lane.getLastStepVehicleIDs(l))
        if t > s[3]:
            s[1] += len(ids - s[0]); s[3] = t
        s[0] = ids; return s[1] / max(30.0, s[3] - s[2])

    def pol(O):
        x = O
        for i, (W, b) in enumerate(Ws):
            x = x @ W.T + b
            if i < len(Ws) - 1:
                x = np.maximum(x, 0.0)
        return x.argmax(1)

    def t_switch(tid, t):
        ls = CE.ls; d = info.tls[tid]; ph = ls.trafficlight.getPhase(tid)
        if ph not in d['greens']:
            return None
        cur = d['greens'].index(ph); s0 = ls.trafficlight.getSpentDuration(tid); G = []
        for lanes in d['serve'][:2]:
            q0, pend = 0, []
            for l in lanes:
                L = lens.get(l) or lens.setdefault(l, ls.lane.getLength(l))
                for v in ls.lane.getLastStepVehicleIDs(l):
                    sp = ls.vehicle.getSpeed(v)
                    if sp < 0.1:
                        q0 += 1
                    else:
                        pend.append(((L - ls.vehicle.getLanePosition(v)) / max(sp, 2.0), sp))
            pend.sort(); L0 = float(np.mean([lens[l] for l in lanes])) if lanes else 100.0
            G.append([q0, pend, len(lanes), 0.0, lam(tid, len(G), lanes, t) if ARR else 0.0, L0 / 13.89, 0.0])
        t0 = int(t); first = (t0 // DTL + 1) * DTL; obs, eps = [], []
        for u in range(t0 + 1, t0 + H + 1):
            el = u - t0
            for gi, g in enumerate(G):
                while g[1] and g[1][0][0] <= el:
                    g[1].pop(0)
                    if not (gi == cur and g[0] == 0):
                        g[0] += 1
                if g[4] > 0 and el > g[5]:                              # new entries reach the stop line after a free-flow traversal
                    g[6] += g[4]
                    while g[6] >= 1.0:
                        g[6] -= 1.0
                        if not (gi == cur and g[0] == 0):
                            g[0] += 1
                if gi == cur and g[0] > 0:
                    g[3] += g[2] / 2.0
                    while g[3] >= 1.0 and g[0] > 0:
                        g[0] -= 1; g[3] -= 1.0
            if u >= first and (u - first) % DTL == 0 and s0 + el >= MING:
                hq, n = [], []
                for g in G:
                    m1 = sum(1 for _, sp in g[1] if 0.1 <= sp < 2.0); m2 = sum(1 for _, sp in g[1] if 2.0 <= sp < 5.0)
                    hq.append(g[0] + A * m1 + B * m2); n.append(g[0] + len(g[1]) + g[4] * min(el, g[5]))
                obs.append([hq[0] / 10, hq[1] / 10, n[0] / 20, n[1] / 20, float(cur == 0), float(cur == 1), (s0 + el) / 60]); eps.append(el)
        if not obs:
            return None
        a = pol(np.asarray(obs, np.float64)); idx = np.nonzero(a == 1)[0]
        return float(eps[idx[0]]) if len(idx) else None

    def spat(tid, link):
        r = base(tid, link)
        if tid not in info.tls or not r.get('valid') or r.get('ttr', 0) >= 999:
            return r
        ls = CE.ls; t = ls.simulation.getTime(); ph = ls.trafficlight.getPhase(tid); d = info.tls[tid]
        tr = track.setdefault(tid, dict(ph=ph, preds=[], mlp=[]))       # shadow accounting: projected switch epoch vs the first second
        if tr['ph'] in d['greens'] and ph != tr['ph']:                  # the light is seen out of that green (queried seconds only)
            for (tq, sw) in tr['preds']:
                e = sw - t; stats['sw_err_n'] += 1; stats['sw_err_abs'] += abs(e); stats['sw_err_sum'] += e
            for (tq, sw) in tr['mlp']:                                  # the wrapped network's time-to-red on the same green, same convention
                e = sw - t; stats['mlp_err_n'] += 1; stats['mlp_err_abs'] += abs(e); stats['mlp_err_sum'] += e
            tr['preds'] = []; tr['mlp'] = []
        tr['ph'] = ph
        if ph not in d['greens']:
            return r                                                   # yellow: the hybrid's exact c2 answer
        key = (tid, int(t))
        if key not in cache:
            if len(cache) > 4096:
                cache.clear()
            T = t_switch(tid, t); cache[key] = T
            if T is not None:
                tr['preds'].append((t, t + T))
        T = cache[key]
        if T is None:
            stats['prf_fallback'] += 1; return r
        if tid not in st_cache:
            st_cache[tid] = [p.state for p in ls.trafficlight.getAllProgramLogics(tid)[0].phases]
        green = st_cache[tid][ph][link] in 'Gg'; stats['prf'] += 1
        if green and (not tr['mlp'] or tr['mlp'][-1][0] != t):
            tr['mlp'].append((t, t + r['ttr'] - OFF))
        if green:
            v = T + OFF
            if VAR == 'prfq':
                v = min(v, r['ttr'])
            return dict(ttg=0.0, ttr=v, valid=True, source='prf')
        v = T + YEL + OFF
        if VAR == 'prfq':
            v = min(v, r['ttg'])
        return dict(ttg=v, ttr=0.0, valid=True, source='prf')
    spat.stats = stats
    return spat


N4.make_spat_n4 = make
_run = E4.run


def run(a, seed, end):
    out = _run(a, seed, end); out['w15_prf'] = os.environ['W15_PRF']; return out


E4.run = run
E4.SRC = f"{getattr(E4, 'SRC', '')}+w15prf:{os.environ['W15_PRF']}"
if __name__ == '__main__':
    target = sys.argv[1]; sys.argv = [target] + sys.argv[2:]
    runpy.run_path(str(ROOT / target), run_name='__main__')
