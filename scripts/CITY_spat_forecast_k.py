#!/usr/bin/env python3
"""Multi-green empirical SPaT forecast for LightRLK-type controllers (M4 stage 4b candidate; prepared 04/10/2026 21:40, used only by a registered run).
Greens and the program's non-green phases come from CITY_lightk.NetInfoK / the net file at fit time (stored in the table), so three-green lights
are covered (CITY_spat_forecast assumes [G, y, G, y]).  Timing convention, every branch (C-71, C-84; checked by conv_k with TRUE durations):
  light in green g (spent s):   link of g only -> ttr = rem_q(g | s) + OBS
                                 link first served by the m-th green ahead -> ttg = rem_q(g | s) + NG(g) + 1 + sum over intermediate greens h of
                                 (full_q(h) + NG(h) + 1) + OBS          (every green ends by setPhase: its non-green transition is observed NG + 1)
  light in non-green after g:   ttg = (remaining program non-green time) + [chain as above from the next green] + OBS
  link served by the current AND the next green: 'unavailable' (ambiguous end); link served by every green: ttg 0, ttr 999.
q = quantile of the empirical (conditional) green durations, per light and green, pooled by green position as fallback."""
from __future__ import annotations
import numpy as np
import sumolib
import scripts.CITY_q7_cross_version as Q7
from scripts.CITY_env import DT_L
from scripts.CITY_lightk import NetInfoK
import scripts.CITY_spat_forecast as FC
OBS = 1.0


def program(net_file):
    """{tid: (greens, n_phases, [phase durations], [states])} for every NetInfoK light."""
    info = NetInfoK(net_file); net = sumolib.net.readNet(net_file, withPrograms=True); out = {}
    for t in net.getTrafficLights():
        if t.getID() in info.tls:
            ph = list(t.getPrograms().values())[0].getPhases(); d = info.tls[t.getID()]
            out[t.getID()] = (d['greens'], d['n_phases'], [float(p.duration) for p in ph], [p.state for p in ph])
    return out


def ng_of(greens, n, dur):
    """non-green program time between each green and the next green in cycle order."""
    out = []
    for i, g in enumerate(greens):
        j, s = (g + 1) % n, 0.0
        while j != greens[(i + 1) % len(greens)]:
            s += dur[j]; j = (j + 1) % n
        out.append(s)
    return out


def fit_k(files, net_file=None):
    PR = program(net_file or Q7.NET_S); T = {}
    for f in files:
        z = np.load(f, allow_pickle=True); ids = [str(x) for x in z['ids']]; P = z['phases']
        for j, tid in enumerate(ids):
            if tid not in PR:
                continue
            for ph, _st, ln, complete in FC.runs(P[:, j]):
                if complete and ph in PR[tid][0]:
                    T.setdefault(tid, {}).setdefault(str(ph), []).append(ln)
    pooled = {}
    for tid in T:
        for g, v in T[tid].items():
            pooled.setdefault(str(PR[tid][0].index(int(g))), []).extend(v)
    return dict(per=T, pooled=pooled, greens={t: v[0] for t, v in PR.items()}, ng={t: ng_of(v[0], v[1], v[2]) for t, v in PR.items()},
                n_phases={t: v[1] for t, v in PR.items()}, dur={t: v[2] for t, v in PR.items()}, n_files=len(files), kind='forecast_k')


class ForecastK:
    def __init__(self, table, q):
        self.q = q; self.G = table['greens']; self.NG = table['ng']; self.NP = table['n_phases']; self.DUR = table['dur']
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

    def chain(self, tid, c, t0, serve, rem_fn=None, full_fn=None):
        """t0 = time until green gs[c] starts (already including OBS-free offsets); walk greens c, c+1, ... until one serves the link."""
        gs = self.G[tid]; k = len(gs); t = t0; full_fn = full_fn or self.full
        for m in range(k):
            g = gs[(c + m) % k]
            if g in serve:
                return t + OBS
            t += full_fn(tid, g) + self.NG[tid][(c + m) % k] + 1.0
        return None

    def ttg(self, tid, ph, spent, serve, rem_fn=None, full_fn=None):
        gs = self.G[tid]; rem_fn = rem_fn or self.rem
        if ph in gs:
            c = gs.index(ph); return self.chain(tid, (c + 1) % len(gs), rem_fn(tid, ph, spent) + self.NG[tid][c] + 1.0, serve, full_fn=full_fn)
        n = self.NP[tid]; j = ph; left = self.DUR[tid][ph] - spent
        while True:                                              # remaining non-green time up to the next green
            j = (j + 1) % n
            if j in gs:
                break
            left += self.DUR[tid][j]
        return self.chain(tid, gs.index(j), max(0.0, left), serve, full_fn=full_fn)


def make_spat_k(table, q):
    import scripts.CITY_env as CE
    F = ForecastK(table, q); cache = {}

    def spat_k(tid, link):
        if tid not in F.G:
            return dict(ttg=0.0, ttr=0.0, valid=False, source='unavailable')
        ls = CE.ls
        if tid not in cache:
            cache[tid] = [p.state for p in ls.trafficlight.getAllProgramLogics(tid)[0].phases]
        st = cache[tid]; gs = F.G[tid]; serve = {g for g in gs if st[g][link] in 'Gg'}
        if len(serve) == len(gs):
            return dict(ttg=0.0, ttr=999.0, valid=True, source=f'forecastk:{q}')
        if not serve:
            return dict(ttg=0.0, ttr=0.0, valid=False, source='never-green')
        ph = ls.trafficlight.getPhase(tid); spent = ls.trafficlight.getSpentDuration(tid)
        if ph in serve:
            if gs[(gs.index(ph) + 1) % len(gs)] in serve:
                return dict(ttg=0.0, ttr=0.0, valid=False, source='unavailable:ambiguous-end')
            return dict(ttg=0.0, ttr=F.rem(tid, ph, spent) + OBS, valid=True, source=f'forecastk:{q}')
        return dict(ttg=F.ttg(tid, ph, spent, serve), ttr=0.0, valid=True, source=f'forecastk:{q}')
    return spat_k, F
