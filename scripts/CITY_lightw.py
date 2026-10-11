#!/usr/bin/env python3
"""F1-B (PROTOCOL_CITY_F1_SALTLAKE_20261008, Amendment A3): LightRLW = CITY_lightk.LightRLK (keep / advance every DT_L s after MIN_G,
halting reward, unchanged step) with a WIDE observation that sees every green: [halting on green g's lanes / 10 for g < KMAX, vehicles on
green g's lanes / 20 for g < KMAX, one-hot current green (KMAX), spent / 60], KMAX = 4, zero-padded for fewer greens -> 13 inputs.
The two-green observation of LightRLK leaves a four-green light blind to two of its greens (C-202, C-203)."""
import numpy as np
import scripts.CITY_env as CE
from scripts.CITY_lightk import LightRLK
KMAX = 4; DIN = 3 * KMAX + 1


class LightRLW(LightRLK):
    def obs(self, tid):
        ls = CE.ls; d = self.info.tls[tid]; ph = ls.trafficlight.getPhase(tid)
        if ph not in d['greens']:
            return None, 0, -1
        cur = d['greens'].index(ph); k = len(d['greens']); assert k <= KMAX, k
        H = [sum(ls.lane.getLastStepHaltingNumber(l) for l in s) for s in d['serve']]; N = [sum(ls.lane.getLastStepVehicleNumber(l) for l in s) for s in d['serve']]
        o = np.zeros(DIN, np.float32); o[:k] = np.array(H) / 10; o[KMAX:KMAX + k] = np.array(N) / 20; o[2 * KMAX + cur] = 1.0
        o[3 * KMAX] = ls.trafficlight.getSpentDuration(tid) / 60
        return o, sum(H), cur


class LightRLWQ(LightRLW):
    """F1-4 (Amendment A5): the frozen RLW light behind the TSI demand adapter on every green's halting input:
    h_g + A n_g[0.1, 2) + B n_g[2, 5) (moving vehicles on green g's served lanes by speed band), as LightRLKQ does for two greens."""
    def __init__(self, info, policy, A, B, record=False):
        super().__init__(info, policy, record); self.A, self.B = A, B

    def obs(self, tid):
        o, halt, cur = super().obs(tid)
        if o is None or not (self.A or self.B):
            return o, halt, cur
        ls = CE.ls; d = self.info.tls[tid]; o = o.copy()
        for g, s in enumerate(d['serve']):
            h = m1 = m2 = 0
            for l in s:
                for v in ls.lane.getLastStepVehicleIDs(l):
                    sp = ls.vehicle.getSpeed(v); h += sp < 0.1; m1 += 0.1 <= sp < 2.0; m2 += 2.0 <= sp < 5.0
            o[g] = (h + self.A * m1 + self.B * m2) / 10
        return o, halt, cur
