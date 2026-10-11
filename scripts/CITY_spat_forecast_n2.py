#!/usr/bin/env python3
"""N2 deployed provider (PROTOCOL_CITY_N2_STATE_FORECAST_20261005): the state-conditioned quantile model of CITY_n2_fit served online.
Features are computed exactly as in CITY_n2_fit.build at the query second (checked by KN2-1 against the offline builder on the same run):
phase position, spent, target flag, halting / vehicles on the current (or just-ended) and target greens' lanes, run-length history (a
Tracker fed every second by the evaluator's logger), light one-hot.  Answers: light in a green serving the link -> ttr = predicted remaining;
otherwise ttg = predicted time to the serving green (min over serving greens).  Always-green: ttg 0 / ttr 999; never-green: invalid."""
import numpy as np
import torch
import scripts.CITY_env as CE
import scripts.CITY_n2_fit as NF


class Tracker:
    """completed run lengths per (light, phase), counted in observed seconds as the offline FC.runs."""
    def __init__(self):
        self.prev, self.cnt, self.hist = {}, {}, {}

    def step(self, ids):
        ls = CE.ls
        for tid in ids:
            ph = ls.trafficlight.getPhase(tid)
            if self.prev.get(tid) is None or ph != self.prev[tid]:
                if self.prev.get(tid) is not None:
                    h = self.hist.setdefault((tid, self.prev[tid]), []); h.append(self.cnt[tid]); del h[:-2]
                self.prev[tid], self.cnt[tid] = ph, 0
            self.cnt[tid] += 1

    def mean(self, tid, g, ph_now=None):
        """history as the offline builder sees it at this second: queries run before the logger's step, so a run that ends NOW (the
        light's phase differs from the last logged one) is counted as completed, exactly as CITY_n2_fit.hist_series does at index st + ln."""
        h = list(self.hist.get((tid, g), []))
        if ph_now is not None and self.prev.get(tid) is not None and ph_now != self.prev[tid] and self.prev[tid] == g:
            h = (h + [self.cnt[tid]])[-2:]
        return float(np.mean(h)) if h else 15.0


def make_spat_n2(model_path, q, info, tracker, debug=None):
    d = torch.load(model_path, weights_only=False); net = NF.QNet(d['d']); net.load_state_dict(d['state']); net.eval(); qi = list(d['qs']).index(q)
    ids = list(d['ids']); L = len(ids); cache = {}; st_cache = {}

    def feats(tid, t):
        ls = CE.ls; j = ids.index(tid); dd = info.tls[tid]; gs = list(dd['greens']); ph = ls.trafficlight.getPhase(tid); s = ls.trafficlight.getSpentDuration(tid)
        ci = max([k for k, g in enumerate(gs) if g <= ph], default=len(gs) - 1); cur = gs[ci]
        H = [sum(ls.lane.getLastStepHaltingNumber(l) for l in sv) for sv in dd['serve'][:2]]; V = [sum(ls.lane.getLastStepVehicleNumber(l) for l in sv) for sv in dd['serve'][:2]]
        oh = np.zeros(4, np.float32); oh[min(ph, 3)] = 1; eye = np.zeros(L, np.float32); eye[j] = 1; rows, keys = [], []
        for gk, g in enumerate(gs):
            kind = 0 if ph == g else 1; ti = (1 - gk) if kind == 0 else gk
            rows.append(np.concatenate([oh, [s / 60.0, float(kind), H[ci] / 10.0, V[ci] / 20.0, H[ti] / 10.0, V[ti] / 20.0, tracker.mean(tid, cur, ph) / 60.0,
                                             tracker.mean(tid, g, ph) / 60.0], eye]).astype(np.float32)); keys.append((g, kind))
        with torch.no_grad():
            pr = net(torch.as_tensor(np.stack(rows))).numpy()[:, qi]
        out = {k: float(v) for k, v in zip(keys, pr)}
        if debug is not None and len(debug) < 20000:
            for k, r, v in zip(keys, rows, pr):
                debug.append((float(t), tid, k[0], k[1], r.tolist(), float(v)))
        return out, ph, gs

    def spat(tid, link):
        if tid not in info.tls:
            return dict(ttg=0.0, ttr=0.0, valid=False, source='unavailable')
        ls = CE.ls; t = ls.simulation.getTime()
        if tid not in st_cache:
            st_cache[tid] = [p.state for p in ls.trafficlight.getAllProgramLogics(tid)[0].phases]
        st = st_cache[tid]; gs = list(info.tls[tid]['greens']); serve = {g for g in gs if st[g][link] in 'Gg'}
        if len(serve) == len(gs):
            return dict(ttg=0.0, ttr=999.0, valid=True, source=f'n2:{q}')
        if not serve:
            return dict(ttg=0.0, ttr=0.0, valid=False, source='never-green')
        if cache.get(tid, (None,))[0] != t:
            cache[tid] = (t,) + feats(tid, t)
        _, pred, ph, _gs = cache[tid]
        if ph in serve:
            return dict(ttg=0.0, ttr=max(0.0, pred[(ph, 0)]), valid=True, source=f'n2:{q}')
        return dict(ttg=max(0.0, min(pred[(g, 1)] for g in serve)), ttr=0.0, valid=True, source=f'n2:{q}')
    return spat
