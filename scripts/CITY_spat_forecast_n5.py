#!/usr/bin/env python3
"""N5 provider variants (05/10 01:4x; C-113 and the user's left-turn question): a COPY of CITY_spat_forecast_n4 (that file is frozen
while the TSI confirmation uses it) with extra gate kinds:
    hybd:<c2 table>    direct-only hybrid: c2 only when the light shows a yellow AND the link is served by the green right after it
                       (the one case where c2 is exact); otherwise the state model N2
    hybnl / hybdnl     as hyb / hybd, plus: links whose state in their serving green is 'g' (permissive left, must yield) get 'unavailable'
Base docstring:
N4 gated provider (PROTOCOL_CITY_N4_SERVICE_GATE_20261005): the N2 state model (CITY_spat_forecast_n2 features, unchanged) with a service
gate that answers either the forecast at quantile q or 'unavailable' (the fleet then drives sigma*).  The gate sees only causal quantities
of the query second: the forecast interval width w = pred(q0.5) - pred(q0.1) of the answer, the answered horizon (ttg for a link waiting for
green), and a deterministic hash for the random arm.
  gate spec:  all | w:<tau> | h:<tau> | wh:<tau_w>,<tau_h> | rnd:<p>
    w   publish iff w <= tau            (confidence-only)
    h   publish iff the link is green now, or its predicted ttg <= tau   (horizon gate: no long red-wait forecasts)
    wh  both conditions
    rnd publish with probability p, hash of (light, link, t // 5) (matched-activation random arm)
    hyb:<c2 table json>   N2-hybrid (C-102): while the light shows a yellow, answer with provider c2 on that table (exact there); else N2
Counters (valid queries, published) in the returned function's .stats."""
import hashlib, json
import numpy as np
import torch
import scripts.CITY_env as CE
import scripts.CITY_n2_fit as NF


def make_spat_n4(model_path, q, info, tracker, gate):
    d = torch.load(model_path, weights_only=False); net = NF.QNet(d['d']); net.load_state_dict(d['state']); net.eval(); qs = list(d['qs'])
    qi, i1, i5 = qs.index(q), qs.index(0.1), qs.index(0.5); ids = list(d['ids']); L = len(ids); cache = {}; st_cache = {}
    kind, _, par = gate.partition(':'); stats = dict(valid=0, published=0, hybrid=0)
    HY = kind in ('hyb', 'hybd', 'hybnl', 'hybdnl'); DIRECT = kind in ('hybd', 'hybdnl'); NOLEFT = kind in ('hybnl', 'hybdnl'); stats['noleft'] = 0
    P = [float(x) for x in par.split(',')] if (par and not HY) else []
    if HY:
        import scripts.CITY_spat_forecast_c2 as C2
        C2S = C2.make_spat_c2(json.load(open(par)), q)[0]

    def feats(tid, t):
        ls = CE.ls; j = ids.index(tid); dd = info.tls[tid]; gs = list(dd['greens']); ph = ls.trafficlight.getPhase(tid); s = ls.trafficlight.getSpentDuration(tid)
        ci = max([k for k, g in enumerate(gs) if g <= ph], default=len(gs) - 1); cur = gs[ci]
        H = [sum(ls.lane.getLastStepHaltingNumber(l) for l in sv) for sv in dd['serve'][:2]]; V = [sum(ls.lane.getLastStepVehicleNumber(l) for l in sv) for sv in dd['serve'][:2]]
        oh = np.zeros(4, np.float32); oh[min(ph, 3)] = 1; eye = np.zeros(L, np.float32); eye[j] = 1; rows, keys = [], []
        for gk, g in enumerate(gs):
            kd = 0 if ph == g else 1; ti = (1 - gk) if kd == 0 else gk
            rows.append(np.concatenate([oh, [s / 60.0, float(kd), H[ci] / 10.0, V[ci] / 20.0, H[ti] / 10.0, V[ti] / 20.0, tracker.mean(tid, cur, ph) / 60.0,
                                             tracker.mean(tid, g, ph) / 60.0], eye]).astype(np.float32)); keys.append((g, kd))
        with torch.no_grad():
            pr = net(torch.as_tensor(np.stack(rows))).numpy()
        return {k: (float(v[qi]), float(v[i5] - v[i1])) for k, v in zip(keys, pr)}, ph

    def ok(tid, link, t, green, val, w):
        if kind == 'all' or HY:
            return True
        if kind == 'w':
            return w <= P[0]
        if kind == 'h':
            return green or val <= P[0]
        if kind == 'wh':
            return w <= P[0] and (green or val <= P[1])
        if kind == 'rnd':
            h = int(hashlib.sha256(f'{tid}|{link}|{int(t) // 5}'.encode()).hexdigest()[:8], 16) / 0xFFFFFFFF; return h < P[0]
        raise ValueError(gate)

    def spat(tid, link):
        if tid not in info.tls:
            return dict(ttg=0.0, ttr=0.0, valid=False, source='unavailable')
        ls = CE.ls; t = ls.simulation.getTime()
        if tid not in st_cache:
            st_cache[tid] = [p.state for p in ls.trafficlight.getAllProgramLogics(tid)[0].phases]
        st = st_cache[tid]; gs = list(info.tls[tid]['greens']); serve = {g for g in gs if st[g][link] in 'Gg'}
        if len(serve) == len(gs):
            return dict(ttg=0.0, ttr=999.0, valid=True, source=f'n4:{q}')
        if not serve:
            return dict(ttg=0.0, ttr=0.0, valid=False, source='never-green')
        if NOLEFT and any(st[g][link] == 'g' for g in serve):
            stats['noleft'] += 1; return dict(ttg=0.0, ttr=0.0, valid=False, source='noleft')
        if HY:
            phn = ls.trafficlight.getPhase(tid)
            if phn not in gs and ((not DIRECT) or ((phn + 1) % len(st)) in serve):
                stats['valid'] += 1; stats['published'] += 1; stats['hybrid'] += 1; return C2S(tid, link)
        if cache.get(tid, (None,))[0] != t:
            cache[tid] = (t,) + feats(tid, t)
        _, pred, ph = cache[tid]; stats['valid'] += 1
        if ph in serve:
            val, w = pred[(ph, 0)]; green = True
        else:
            g = min(serve, key=lambda g: pred[(g, 1)][0]); val, w = pred[(g, 1)]; green = False
        if not ok(tid, link, t, green, max(0.0, val), w):
            return dict(ttg=0.0, ttr=0.0, valid=False, source='gated')
        stats['published'] += 1
        return dict(ttg=0.0, ttr=max(0.0, val), valid=True, source=f'n4:{q}') if green else dict(ttg=max(0.0, val), ttr=0.0, valid=True, source=f'n4:{q}')
    spat.stats = stats
    return spat
