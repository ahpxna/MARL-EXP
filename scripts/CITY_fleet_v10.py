#!/usr/bin/env python3
"""Fleet v10 (04/10/2026; PREPARED as the next single fix if v9 shows no learning — Amendment R5, not launched until registered):
v9 (residual on the in-class base controller, identical action and observation) with ONE change: DENSE per-agent credit.
  reward of the decision at t, read at t+1 for the same vehicle:
      r = -[ max(0, 1 - v_i / v_allowed) + 0.5 * fuel_i[mg/s] / 1000 + LAMBDA_F * max(0, 1 - v_f / v_allowed_f) ]
  where f is the immediate follower within 100 m on the same lane (none -> 0).  LAMBDA_F = 1 (fixed).  No threshold (crawling pays delay);
  the follower term is the part of the harm to other cars that the agent's own action most directly causes.  The last decision of a
  segment reads its cost one second later like every other decision (the car still exists just outside the zone); only arrival or a
  teleport gives no reading (counted dense_none, reward 0).  Everything else (segments, gaps, GAE, PPO) is v8."""
from __future__ import annotations
import numpy as np
import scripts.CITY_env as CE
import scripts.CITY_fleet_v8 as V8
import scripts.CITY_fleet_v9 as V9

LAMBDA_F = 1.0


def dense_cost(ls, v):
    sp = ls.vehicle.getSpeed(v); vl = ls.vehicle.getAllowedSpeed(v); fu = ls.vehicle.getFuelConsumption(v)
    if not (V8.ok(sp) and V8.ok(vl) and vl > 0 and V8.ok(fu, nonneg=False)):
        return None
    c = max(0.0, 1.0 - sp / vl) + V9.KAPPA * max(fu, 0.0) / 1000.0
    fol = ls.vehicle.getFollower(v, 100.0)
    if fol and fol[0] and fol[1] >= 0:
        fs = ls.vehicle.getSpeed(fol[0]); fvl = ls.vehicle.getAllowedSpeed(fol[0])
        if V8.ok(fs) and V8.ok(fvl) and fvl > 0:
            c += LAMBDA_F * max(0.0, 1.0 - fs / fvl)
    return c


class CarPPOD(V9.CarPPOR):
    def __init__(self, *a, **k):
        super().__init__(*a, **k); self.reward = 'AD'; self.prev = {}; self.stats.update(dense_none=0, dense_n=0)

    def step(self, t):
        ls = CE.ls
        if self.record:
            for v, dec in self.prev.items():                       # credit the previous second's decisions with the cost observed now
                if dec.get('dropped'):
                    continue
                try:
                    c = dense_cost(ls, v)
                except Exception:
                    c = None
                if c is None:
                    self.stats['dense_none'] += 1
                else:
                    dec['rew'] -= c; self.stats['dense_n'] += 1
        super().step(t)
        self.prev = {v: seg['dec'][-1] for v, seg in self.open.items() if seg['dec'] and seg['dec'][-1]['t'] == t} if self.record else {}
