#!/usr/bin/env python3
"""Fleet v11 (04/10/2026; PROTOCOL_CITY_SPAT_PILOT_20261004 Amendment R10): PPO RESIDUAL on the confirmed rule GLOSA-L∘σ* (C-46), with the
corrected actuation interface (lane-aware release, C-45).
  * Base driver σ* = 0.3 for every agent (setImperfection at departure), as in GLOSA-L∘σ*.
  * The policy ACTS ONLY where the rule commands: in the zone, own movement not green, SPaT valid, ttg > 0, dist <= 200 m, and the current
    lane continues on the route (best-lanes offset 0).  Everywhere else the car is released to SUMO (setSpeed(-1)), exactly as the rule.
  * Action (speed residual): cmd = clip(v_rule + DV * tanh(u), 0, v_allowed), v_rule = min(v_allowed, d / ttg), DV = 3 m/s.  The actor's
    last layer is zero-initialised (V9.NetR), so the deterministic policy at episode 0 IS GLOSA-L∘σ* (identity check K10-1).
  * Credit (dense, per agent, v10 cost): every second while the car's segment is open, cost_i = own delay share + 0.5 fuel[mg/s]/1000 +
    follower delay share (V10.dense_cost) is credited to the car's MOST RECENT decision, including the seconds after a release (so the
    effect of the arrival state on later delay is paid, not hidden).  Segment = one zone visit (in practice one trip on grid4);
    terminal on zone exit / arrival, truncated (pop + bootstrap) on teleport or episode end.
  * Observation (13, SPaT on), PPO, GAE, scales: v8."""
from __future__ import annotations
import math
import numpy as np
import torch
import scripts.CITY_env as CE
import scripts.CITY_fleet_v8 as V8
import scripts.CITY_fleet_v10 as V10
import scripts.CITY_glosa_lane as GL
from scripts.CITY_spat_feature import spat

DV = 3.0; SIG = 0.3; DACT = 200.0


class CarPPOL(V8.CarPPO):
    def __init__(self, net, rho, seed, deterministic=False, record=True):
        super().__init__(net, rho, seed, True, deterministic=deterministic, record=record, reward=None)
        self.stats.update(active=0, released=0, dense_none=0, dense_n=0)

    def step(self, t):
        ls = CE.ls
        if self.record:                                            # credit the cost observed now to each open segment's latest decision
            for v, seg in self.open.items():
                try:
                    c = V10.dense_cost(ls, v)
                except Exception:
                    c = None
                if c is None:
                    self.stats['dense_none'] += 1
                else:
                    seg['dec'][-1]['rew'] -= c; self.stats['dense_n'] += 1
        for v in ls.simulation.getDepartedIDList():
            if self.is_agent(v):
                self.agents.add(v); ls.vehicle.setImperfection(v, SIG)
        for v in ls.simulation.getArrivedIDList():
            if v in self.agents:
                if v in self.open:
                    self.stats['terminal_arrival'] += 1
                self._close(v, 'terminal'); self.agents.discard(v)
        todo = []
        for v in list(self.agents):
            try:
                lane = ls.vehicle.getLaneID(v); sp = ls.vehicle.getSpeed(v)
            except Exception:
                self.stats['exc'] += 1; continue
            if lane == '' or not V8.ok(sp):
                self.stats['teleport_hidden'] += 1
                if v in self.open:
                    self.stats['gap'] += 1; self._close(v, 'truncated')
                continue
            try:
                nt = ls.vehicle.getNextTLS(v)
                if not nt or nt[0][2] > V8.ZONE:
                    if v in self.open:
                        self.stats['terminal_exit'] += 1; self._close(v, 'terminal')
                    ls.vehicle.setSpeed(v, -1); self.ctrl.discard(v); continue
                tid, link, dist, st = nt[0]; s = spat(tid, link); vl = ls.vehicle.getAllowedSpeed(v)
                if not (st not in 'Gg' and s['valid'] and s['ttg'] > 0 and dist <= DACT and GL.lane_ok(ls, v)) or not (V8.ok(vl) and vl > 0):
                    ls.vehicle.setSpeed(v, -1); self.stats['released'] += 1; continue
                vr = min(vl, dist / s['ttg']); o = V8.build_obs(ls, v, nt[0], sp, vl, True, self.stats)
            except Exception:
                self.stats['exc'] += 1; continue
            todo.append((v, tid, sp, vl, vr, o))
        if not todo:
            return
        O = torch.as_tensor(np.stack([x[5] for x in todo]))
        with torch.no_grad():
            d = self.net.dist(O); U = d.mean if self.det else d.sample(); LP = d.log_prob(U); V = self.net.value(O)
        U, LP, V = U.numpy(), LP.numpy(), V.numpy()
        for (v, tid, sp, vl, vr, o), u, lp, val in zip(todo, U, LP, V):
            cmd = float(min(max(vr + DV * math.tanh(float(u)), 0.0), vl))
            try:
                ls.vehicle.setSpeed(v, cmd)
            except Exception:
                self.stats['exc'] += 1; continue
            self.decisions += 1; self.stats['decisions'] += 1; self.stats['active'] += 1; self.ctrl.add(v)
            if self.record:
                dec = dict(vid=v, t=t, obs=o, u=float(u), logp=float(lp), val=float(val), a=cmd - sp, sp=sp, cmd=cmd, rew=0.0, tid=tid)
                self.open.setdefault(v, dict(vid=v, dec=[], end=None, boot_obs=None))['dec'].append(dec)
            self.cmd_log.append((t, v, cmd))
        self.digest.update(f'{t}|{len(todo)}'.encode())
