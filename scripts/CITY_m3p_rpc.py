#!/usr/bin/env python3
"""M3′ RPC light (PROTOCOL_CITY_M3P_PRECISION_COMMIT_20261004): RL-H:k (frozen keep / switch, decision every DT_L after MIN_G) plus
receiver-triggered precision commitments.
  trigger (at a decision tick of light j in green g, no commitment pending at j):
    receiver  >= 1 fleet vehicle ELIGIBLE at j: approaching on a link served only by the other green, rule-active geometry (dist <= 200 m,
              lane continues) and frozen-R10 command sensitivity > 0 at the hypothetical ttg = h_D + YELLOW + OBS (pure probe, C-66 S11)
    eta       >= 1 fleet vehicle approaching j on ANY movement with ETA = d / max(v, 1) in [5, 25] s
    random    with probability p_j (matched to the receiver trigger rate on the common TRAIN trace), RNG seeded per run
    none      never (identity with RL-H:k: self-check P1)
  commitment  T_c = t + clip(h_D, H_MIN, H_MAX); h_D = the first future decision tick at which RL-H:k's own Q-network (queues held, spent
              advanced) prefers switch (none within 60 s -> H_MAX).  From t to T_c the light HOLDS g (its own decisions are logged, not applied);
              at T_c it switches (yellow onset).  Messages: pending -> commitment (green end T_c - t; green onset T_c + YELLOW + OBS - t);
              otherwise unavailable."""
from __future__ import annotations
import numpy as np
import torch
import scripts.CITY_env as CE
from scripts.CITY_env import DT_L, MIN_G, YELLOW, ZONE
import scripts.CITY_glosa_lane as GL
import scripts.CITY_m3_core as M

H_MIN, H_MAX, OBS = 5.0, 20.0, 1.0


class LightRPC:
    def __init__(self, info, qnet, trigger='receiver', p_rate=None, seed=0):
        self.info, self.qnet, self.trigger = info, qnet, trigger; self.ids = list(info.tls); self.pending = {}; self.fleet = None
        self.p_rate = p_rate or {}; self.rng = np.random.default_rng(seed + 7907)
        self.log = dict(commits=[], realised=[], overridden=0, decisions=0, ticks_eligible=0, ticks_total=0, per_light={})
        self.states = {}

    def _obs(self, tid):
        ls = CE.ls; d = self.info.tls[tid]; ph = ls.trafficlight.getPhase(tid)
        h = [sum(ls.lane.getLastStepHaltingNumber(l) for l in s) for s in d['serve']]
        n = [sum(ls.lane.getLastStepVehicleNumber(l) for l in s) for s in d['serve']]
        cur = d['greens'].index(ph) if ph in d['greens'] else -1
        return np.array([h[0] / 10, h[1] / 10, n[0] / 20, n[1] / 20, cur == 0, cur == 1, ls.trafficlight.getSpentDuration(tid) / 60], np.float32), cur

    def _q(self, O):
        with torch.no_grad():
            return self.qnet(torch.as_tensor(np.asarray(O, np.float32)))

    def h_D(self, o):
        spent = float(o[6]) * 60.0
        for h in np.arange(DT_L, 61, DT_L):
            if spent + h < MIN_G:
                continue
            oo = o.copy(); oo[6] = (spent + h) / 60.0; q = self._q(oo[None])[0]
            if q[1] > q[0]:
                return float(h)
        return H_MAX

    def _served(self, tid, link):
        if tid not in self.states:
            self.states[tid] = [p.state for p in CE.ls.trafficlight.getAllProgramLogics(tid)[0].phases]
        st = self.states[tid]; return {g for g in self.info.tls[tid]['greens'] if st[g][link] in 'Gg'}

    def _eligible_receiver(self, tid, g, hD):
        ls = CE.ls; net = getattr(self.fleet, 'net', None)
        if net is None:
            return False
        ttg = hD + YELLOW + OBS; fake = lambda a, b: dict(ttg=ttg, ttr=0.0, valid=True, source='rpc-probe')  # noqa: E731
        for v in list(getattr(self.fleet, 'agents', ())):
            try:
                nt = ls.vehicle.getNextTLS(v)
                if not nt or nt[0][0] != tid or nt[0][2] > ZONE:
                    continue
                link, dist, st = nt[0][1], nt[0][2], nt[0][3]
                srv = self._served(tid, link)
                if g in srv or not srv or st in 'Gg' or dist > 200 or not GL.lane_ok(ls, v):
                    continue
                if M.sensitivity(ls, v, nt[0], net, fake, ttg) > 0:
                    return True
            except Exception:
                continue
        return False

    def _eta(self, tid):
        ls = CE.ls
        for v in list(getattr(self.fleet, 'agents', ())):
            try:
                nt = ls.vehicle.getNextTLS(v)
                if nt and nt[0][0] == tid and nt[0][2] <= ZONE and 5 <= nt[0][2] / max(ls.vehicle.getSpeed(v), 1.0) <= 25:
                    return True
            except Exception:
                continue
        return False

    def step(self, t):
        ls = CE.ls
        for tid, Tc in list(self.pending.items()):
            if t >= Tc:
                d = self.info.tls[tid]; ph = ls.trafficlight.getPhase(tid); ls.trafficlight.setPhase(tid, (ph + 1) % d['n_phases'])
                self.log['realised'].append((tid, Tc, float(t))); del self.pending[tid]
        if int(t) % DT_L:
            return
        todo, O = [], []
        for tid in self.ids:
            o, cur = self._obs(tid)
            if cur < 0:
                continue
            if tid in self.pending:
                ls.trafficlight.setPhaseDuration(tid, 1e5); self.log['overridden'] += 1; continue
            if ls.trafficlight.getSpentDuration(tid) < MIN_G:
                ls.trafficlight.setPhaseDuration(tid, 1e5); continue
            todo.append((tid, cur, o)); O.append(o)
        if not todo:
            return
        A = self._q(np.stack(O)).argmax(1).numpy()
        for (tid, cur, o), a in zip(todo, A):
            self.log['decisions'] += 1; g = self.info.tls[tid]['greens'][cur]; trig = False
            if self.trigger != 'none' and self.fleet is not None:
                self.log['ticks_total'] += 1; hD = self.h_D(o)
                if self.trigger == 'receiver':
                    trig = self._eligible_receiver(tid, g, hD)
                elif self.trigger == 'eta':
                    trig = self._eta(tid)
                elif self.trigger == 'random':
                    trig = self.rng.random() < self.p_rate.get(tid, 0.0)
                elif self.trigger == 'measure':                        # rate measurement only: count receiver eligibility, never commit
                    e = int(self._eligible_receiver(tid, g, hD)); self.log['ticks_eligible'] += e; trig = False
                    pl = self.log['per_light'].setdefault(tid, [0, 0]); pl[0] += e; pl[1] += 1
            if trig:
                Tc = float(t + min(max(hD, H_MIN), H_MAX)); self.pending[tid] = Tc; self.log['commits'].append((tid, float(t), Tc))
                ls.trafficlight.setPhaseDuration(tid, 1e5); continue
            if a == 1:
                d = self.info.tls[tid]; ls.trafficlight.setPhase(tid, (d['greens'][cur] + 1) % d['n_phases'])
            else:
                ls.trafficlight.setPhaseDuration(tid, 1e5)

    def spat(self, tid, link):
        """The fleet's SPaT under RPC: commitment while pending, else unavailable."""
        if tid in self.pending:
            ls = CE.ls; t = ls.simulation.getTime(); Tc = self.pending[tid]; ph = ls.trafficlight.getPhase(tid)
            if self.states.get(tid) is None:
                self._served(tid, link)
            if self.states[tid][ph][link] in 'Gg':
                return dict(ttg=0.0, ttr=Tc - t, valid=True, source='commitment')
            return dict(ttg=Tc - t + YELLOW + OBS, ttr=0.0, valid=True, source='commitment')
        return dict(ttg=0.0, ttr=0.0, valid=False, source='unavailable')
