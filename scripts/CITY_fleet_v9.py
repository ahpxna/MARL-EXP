#!/usr/bin/env python3
"""Fleet v9 (04/10/2026; PROTOCOL_CITY_SPAT_PILOT_20261004 Amendment R4): the ONE fix chosen from diagnostics D1 / D2 (ledger C-39, C-40).
  * Residual on an in-class base controller (the D2 representability control IC-GLOSA): every second in the zone,
        a_base = clip(target - v, LO, HI), target = min(v_allowed, d / ttg) if the own movement is not green and SPaT is valid, else v_allowed
        a      = clip(a_base + delta, LO, HI),  delta = 1.5 * tanh(u)  (symmetric: u = 0 -> delta = 0 -> exactly the base controller)
    The actor's last layer is zero-initialised, so the policy at episode 0 IS the base controller (stochastic around it, std exp(-1)).
  * Reward "A-group" (replaces B, which D2 showed is gameable by crawling): per light and program-phase interval, over ALL vehicles on
    the light's incoming lanes, r = -mean over vehicle-seconds of [ max(0, 1 - v / v_lane) + 0.5 * fuel[mg/s] / 1000 ]  (the v3 / A weights;
    no threshold, so crawling pays delay; SUMO cars are included, so harm to them is paid), credited to each agent's LAST decision on that
    light in the interval, exactly as in v8 (same tracker logic, same per-vehicle segments, gaps, terminals, GAE).
  * Everything else is v8: observation (13, SPaT on), PPO hyper-parameters, conventions, counters."""
from __future__ import annotations
import math
import numpy as np
import torch
from torch import nn
import scripts.CITY_env as CE
import scripts.CITY_fleet_v8 as V8
from scripts.CITY_spat_feature import spat

DMAX = 1.5; KAPPA = 0.5


class NetR(V8.Net):
    def __init__(self, seed):
        super().__init__(seed)
        with torch.no_grad():
            self.pi[4].weight.zero_(); self.pi[4].bias.zero_(); self.log_std.fill_(-1.0)


def base_accel(ls, v, nt0, sp, vl):
    tid, link, dist, st = nt0; s = spat(tid, link)
    tgt = min(vl, dist / s['ttg']) if (st not in 'Gg' and s['valid'] and s['ttg'] > 0) else vl
    return float(np.clip(tgt - sp, V8.LO, V8.HI))


class PhaseRewardAG(V8.PhaseRewardB):
    """Same intervals / credit as PhaseRewardB; the interval reward is the negative mean physical cost over vehicle-seconds."""
    def _reset(self, L, ph):
        L['phase'] = ph; L['acc'] = [0, 0.0, 0.0, 0, False]; L['credit'] = {}      # [vehicle-seconds, cost sum, -, -, -]

    def step(self, t):
        ls = CE.ls
        for tid, L in self.lights.items():
            ph = ls.trafficlight.getPhase(tid)
            if L['phase'] is None:
                self._reset(L, ph)
            elif ph != L['phase']:
                self._close(t, tid, L); self._reset(L, ph)
            a = L['acc']
            for lane, length, vmax in L['lanes']:
                for v in ls.lane.getLastStepVehicleIDs(lane):
                    sp = ls.vehicle.getSpeed(v); fu = ls.vehicle.getFuelConsumption(v)
                    if not (V8.ok(sp) and V8.ok(fu, nonneg=False)) or vmax <= 0:
                        self.stats['b_invalid'] += 1; continue
                    a[0] += 1; a[1] += max(0.0, 1.0 - sp / vmax) + KAPPA * max(fu, 0.0) / 1000.0

    def _close(self, t, tid, L):
        a = L['acc']
        if a[0] == 0:
            self.stats['b_empty'] += 1; return
        r = -a[1] / a[0]; n = 0; self.stats['b_R2'] += 1                       # one branch only; counted in b_R2 for the shared logger
        for dec in L['credit'].values():
            if not dec.get('dropped'):
                dec['rew'] += r; n += 1
        self.log.append((t, tid, a[0], a[1] / a[0], 0.0, 0.0, False, r, 'AG', n))


class CarPPOR(V8.CarPPO):
    """v8 CarPPO with the residual action on the base controller and the A-group reward."""
    def step(self, t):
        if self.tracker is None and self.reward == 'AG':
            self.tracker = PhaseRewardAG(self.stats)
        orig_squash, ls = V8.squash, CE.ls
        self._base = {}

        def squash_r(u):                                          # called by CarPPO.step with the batch U; maps to the final a
            return np.array([float(np.clip(b + DMAX * math.tanh(x), V8.LO, V8.HI)) for x, b in zip(np.atleast_1d(u), self._bq)])
        orig_build = V8.build_obs

        def build(ls_, v, nt0, sp, vl, spat_on, stats):
            o = orig_build(ls_, v, nt0, sp, vl, spat_on, stats); self._base[v] = base_accel(ls_, v, nt0, sp, vl); self._order.append(v); return o
        self._order = []; V8.build_obs = build
        orig_dist = self.net.dist
        self._bq = []

        def dist(O):
            self._bq = [self._base[v] for v in self._order]; return orig_dist(O)
        self.net.dist = dist; V8.squash = squash_r
        try:
            super().step(t)
        finally:
            V8.squash = orig_squash; V8.build_obs = orig_build; self.net.dist = orig_dist
