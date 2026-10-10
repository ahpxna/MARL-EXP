#!/usr/bin/env python3
"""Causal SPaT FORECAST for a learned light (PROTOCOL_CITY_M2_COMPAT_20261004 Amendment M2b; 04/10/2026).  A forecast, not a plan:
published with its quantile and labelled source='forecast:q'.
  Fit (TRAIN traces only): completed green durations G per (intersection, green phase) from `--record` phase traces of RL-H:k runs
  (P[i, j] = phase of light j observed at time i + 1), pooled over traffic seeds; pooled-per-green-index fallback.
  Online forecast at time t from the light's CURRENT phase and spent time only (causal):
    green g, spent s:  remaining r_q = q-quantile of {G - s : G > s}  (fallback: pooled; else the next decision tick)
                       link served by g: ttg 0, ttr r_q + OBS;  link served by the other green: ttg r_q + YELLOW + OBS
    yellow:            rem = YELLOW - spent (exact: yellows run on the program timer);  link served by the next green: ttg rem + OBS;
                       link served by the green that just ended: ttg rem + OBS + q-quantile(G_next) + YELLOW
    always-green / never-green links as in CITY_spat_feature.spat
CLI:  fit K OUT_JSON TRACE...   |   validate K TABLE_JSON TRACE...   (offline forecast vs actual, per movement group = (light, green))"""
import json, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
OBS, YELLOW, DT_L = 1.0, 3.0, 5.0


def runs(col):
    """(phase, start index, length, complete) for each run of identical values in one light's phase column."""
    out = []; i = 0; n = len(col)
    while i < n:
        j = i
        while j + 1 < n and col[j + 1] == col[i]:
            j += 1
        out.append((int(col[i]), i, j - i + 1, j + 1 < n)); i = j + 1
    return out


def greens_of(ids):
    import scripts.CITY_eval4 as E4
    info = E4.NetInfo(E4.Q7.NET_S); return {tid: list(info.tls[tid]['greens']) for tid in ids}


def fit(files):
    T, ids = {}, None
    for f in files:
        z = np.load(f, allow_pickle=True); ids = [str(x) for x in z['ids']]; P = z['phases']; G = greens_of(ids)
        for j, tid in enumerate(ids):
            for ph, _st, ln, complete in runs(P[:, j]):
                if complete and ph in G[tid]:
                    T.setdefault(tid, {}).setdefault(str(ph), []).append(ln)
    pooled = {}
    for tid in T:
        for g, v in T[tid].items():
            pooled.setdefault(str(G[tid].index(int(g))), []).extend(v)
    return dict(per=T, pooled=pooled, greens=G, n_files=len(files))


class Forecast:
    def __init__(self, table, q):
        self.q = q; self.G = {tid: v for tid, v in table['greens'].items()}
        self.per = {tid: {int(g): np.sort(np.array(v, float)) for g, v in d.items()} for tid, d in table['per'].items()}
        self.pool = {int(k): np.sort(np.array(v, float)) for k, v in table['pooled'].items()}

    def _arr(self, tid, g):
        a = self.per.get(tid, {}).get(g)
        return a if a is not None and len(a) else self.pool[self.G[tid].index(g)]

    def rem(self, tid, g, s):
        a = self._arr(tid, g); r = a[a > s] - s
        if not len(r):
            a = self.pool[self.G[tid].index(g)]; r = a[a > s] - s
        if not len(r):
            return DT_L - (s % DT_L) if s % DT_L else DT_L
        return float(np.quantile(r, self.q, method='inverted_cdf'))

    def full(self, tid, g):
        return float(np.quantile(self._arr(tid, g), self.q, method='inverted_cdf'))

    def ttg(self, tid, ph, spent, serve):
        """Forecast time until a green in `serve` (set of green phase indices) given the current phase and spent time."""
        gs = self.G[tid]
        if ph in gs:
            if ph in serve:
                return 0.0
            return self.rem(tid, ph, spent) + YELLOW + OBS
        rem = max(0.0, YELLOW - spent); nxt = (ph + 1) % 4                  # grid4 programs: [G, y, G, y] (asserted at fit)
        assert nxt in gs
        if nxt in serve:
            return rem + OBS
        return rem + OBS + self.full(tid, nxt) + YELLOW


def make_spat(table, q):
    """Online replacement for CITY_spat_feature.spat under a learned light."""
    import scripts.CITY_env as CE
    F = Forecast(table, q); cache = {}

    def spat_fc(tid, link):
        ls = CE.ls
        if tid not in cache:
            lg = ls.trafficlight.getAllProgramLogics(tid)[0]; cache[tid] = [p.state for p in lg.phases]
        st = cache[tid]; gs = F.G[tid]; serve = {g for g in gs if st[g][link] in 'Gg'}
        if len(serve) == len(gs):
            return dict(ttg=0.0, ttr=999.0, valid=True, source=f'forecast:{q}')
        if not serve:
            return dict(ttg=0.0, ttr=0.0, valid=False, source='never-green')
        ph = ls.trafficlight.getPhase(tid); spent = ls.trafficlight.getSpentDuration(tid)
        if ph in serve:
            return dict(ttg=0.0, ttr=F.rem(tid, ph, spent) + OBS, valid=True, source=f'forecast:{q}')
        return dict(ttg=F.ttg(tid, ph, spent, serve), ttr=0.0, valid=True, source=f'forecast:{q}')
    return spat_fc, F


def validate(table, files):
    """Offline: for every second and every (light, green) not active, forecast (q50, q10, q90) vs the actual time until that green."""
    F = {q: Forecast(table, q) for q in (0.5, 0.1, 0.9)}; err, cov, n = [], 0, 0; per = {}
    for f in files:
        z = np.load(f, allow_pickle=True); ids = [str(x) for x in z['ids']]; P = z['phases']; S = z['spent']
        for j, tid in enumerate(ids):
            gs = F[0.5].G[tid]; col = P[:, j]
            nxt_idx = {g: np.full(len(col), -1) for g in gs}
            for g in gs:
                last = -1
                for i in range(len(col) - 1, -1, -1):
                    if col[i] == g:
                        last = i
                    nxt_idx[g][i] = last
            for i in range(len(col)):
                ph = int(col[i])
                for g in gs:
                    if ph == g or nxt_idx[g][i] < 0:
                        continue
                    act = float(nxt_idx[g][i] - i); fc = F[0.5].ttg(tid, ph, float(S[i, j]), {g})
                    lo, hi = F[0.1].ttg(tid, ph, float(S[i, j]), {g}), F[0.9].ttg(tid, ph, float(S[i, j]), {g})
                    e = fc - act; err.append(e); cov += lo <= act <= hi; n += 1; per.setdefault((tid, g), []).append(abs(e))
    err = np.array(err); grp = np.array([np.median(v) for v in per.values()])
    return dict(n=n, bias=float(err.mean()), mae=float(np.abs(err).mean()), med_abs=float(np.median(np.abs(err))), coverage_10_90=cov / n,
                per_group_med_abs=dict(min=float(grp.min()), median=float(np.median(grp)), max=float(grp.max()), groups=len(grp)))


if __name__ == '__main__':
    cmd, k = sys.argv[1], sys.argv[2]
    if cmd == 'fit':
        T = fit(sys.argv[4:]); Path(sys.argv[3]).write_text(json.dumps(T)); print('fit', k, 'files', T['n_files'], 'lights', len(T['per']))
    elif cmd == 'validate':
        r = validate(json.loads(Path(sys.argv[3]).read_text()), sys.argv[4:]); print(json.dumps(dict(light=k, **r)))
