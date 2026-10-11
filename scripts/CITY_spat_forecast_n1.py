#!/usr/bin/env python3
"""N1 provider (PROTOCOL_CITY_N1_TAIL_SUPPORT_20261005): CITY_spat_forecast_k (unchanged, subclassed) with the SUPPORT state of every answer:
  local    the current green's remaining time came from this light / green's own samples longer than the current age
  pool     the light's own samples were exhausted; the pooled samples (same green position, all lights) were used
  none     both exhausted: the parent's tick fallback (DT_L - s % DT_L), i.e. a forecast BEYOND the data
  program  the light is in a non-green phase (remaining program time; no learned component for the current phase)
Modes: all (= the parent's answers, support only counted), tail (support 'none' -> unavailable), strict ('pool' or 'none' -> unavailable).
grid4 tables (old format) are augmented exactly as provider c2 (CITY_spat_forecast_c2.augment); spider tables are forecast-K tables."""
from collections import Counter
import numpy as np
import scripts.CITY_env as CE
import scripts.CITY_spat_forecast_k as FK
from scripts.CITY_env import DT_L

UNAV = dict(ttg=0.0, ttr=0.0, valid=False, source='unavailable')


class ForecastKX(FK.ForecastK):
    def __init__(self, table, q):
        super().__init__(table, q); self.last = 'program'

    def rem(self, tid, g, s):
        a = self._arr(tid, g); r = a[a > s] - s; self.last = 'local' if (self.per.get(tid, {}).get(g) is not None and len(self.per[tid][g]) and len(r)) else 'pool'
        if not len(r):
            a = self.pool[self.G[tid].index(g)]; r = a[a > s] - s; self.last = 'pool'
        if not len(r):
            self.last = 'none'; return DT_L - (s % DT_L) if s % DT_L else DT_L
        return float(np.quantile(r, self.q, method='inverted_cdf'))


def make_spat_n1(table, q, mode='all'):
    assert mode in ('all', 'tail', 'strict')
    F = ForecastKX(table, q); cache = {}; C = Counter()

    def spat(tid, link):
        if tid not in F.G:
            return UNAV
        ls = CE.ls
        if tid not in cache:
            cache[tid] = [p.state for p in ls.trafficlight.getAllProgramLogics(tid)[0].phases]
        st = cache[tid]; gs = F.G[tid]; serve = {g for g in gs if st[g][link] in 'Gg'}
        if len(serve) == len(gs):
            C['always'] += 1; return dict(ttg=0.0, ttr=999.0, valid=True, source='forecast-n1')
        if not serve:
            return dict(ttg=0.0, ttr=0.0, valid=False, source='never-green')
        ph = ls.trafficlight.getPhase(tid); spent = ls.trafficlight.getSpentDuration(tid); F.last = 'program'
        if ph in serve:
            if gs[(gs.index(ph) + 1) % len(gs)] in serve:
                return dict(ttg=0.0, ttr=0.0, valid=False, source='unavailable:ambiguous-end')
            out = dict(ttg=0.0, ttr=F.rem(tid, ph, spent) + FK.OBS, valid=True, source='forecast-n1')
        else:
            out = dict(ttg=F.ttg(tid, ph, spent, serve), ttr=0.0, valid=True, source='forecast-n1')
        sup = F.last; C[sup] += 1
        if (mode == 'tail' and sup == 'none') or (mode == 'strict' and sup in ('pool', 'none')):
            C['abstained'] += 1; return dict(UNAV, source=f'unavailable:support-{sup}')
        return out
    return spat, F, C
