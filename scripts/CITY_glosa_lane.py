#!/usr/bin/env python3
"""R8 (Amendment R8, 04/10/2026): GLOSA with LANE-AWARE release.  The R6 parametric GLOSA rule (CITY_es_glosa.CarESGlosa, frozen, not
edited) commands v = clip(d / (ttg + b), v_lo, v_allowed) only when the car is on a lane that continues on its route (getBestLanes offset
of the current lane == 0); otherwise it releases to SUMO, so SUMO's strategic / cooperative speed adaptation can complete the lane change.
lane_aware=False reproduces CarESGlosa exactly (identity check KL).  base_sigma (None = SUMO default 0.5): setImperfection at departure
for the agents, as in CITY_es_glosa_sbase / CITY_eval6_sbase."""
import scripts.CITY_env as CE
import scripts.CITY_fleet_v8 as V8
import scripts.CITY_es_glosa as ES
from scripts.CITY_spat_feature import spat


def lane_ok(ls, v):
    ln = ls.vehicle.getLaneID(v)
    for b in ls.vehicle.getBestLanes(v):
        if b[0] == ln:
            return b[3] == 0
    return False                                                   # internal lane / not found: release


class CarGlosaL(ES.CarESGlosa):
    def __init__(self, rho, seed, theta=(0.0, 0.0, 200.0), lane_aware=True, base_sigma=None):
        super().__init__(rho, seed, theta); self.lane_aware, self.base_sigma = lane_aware, base_sigma; self.lane_released = 0

    def step(self, t):
        ls = CE.ls
        for v in ls.simulation.getDepartedIDList():
            if self.is_agent(v):
                self.agents.add(v)
                if self.base_sigma is not None:
                    ls.vehicle.setImperfection(v, self.base_sigma)
        for v in ls.simulation.getArrivedIDList():
            self.agents.discard(v)
        for v in list(self.agents):
            try:
                nt = ls.vehicle.getNextTLS(v)
                if not nt or nt[0][2] > V8.ZONE:
                    ls.vehicle.setSpeed(v, -1); continue
                tid, link, dist, st = nt[0]; s = spat(tid, link); self.decisions += 1
                if st not in 'Gg' and s['valid'] and s['ttg'] > 0 and dist <= self.dact:
                    if self.lane_aware and not lane_ok(ls, v):
                        ls.vehicle.setSpeed(v, -1); self.lane_released += 1; continue
                    vl = ls.vehicle.getAllowedSpeed(v); ls.vehicle.setSpeed(v, float(min(vl, max(self.vlo, dist / (s['ttg'] + self.b))))); self.fired += 1
                else:
                    ls.vehicle.setSpeed(v, -1)
            except Exception:
                continue
