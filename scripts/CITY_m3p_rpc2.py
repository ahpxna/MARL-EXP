#!/usr/bin/env python3
"""M3′-D light (PROTOCOL_CITY_M3P_DIAG_20261004): CITY_m3p_rpc.LightRPC (unchanged, subclassed) with two factors and H1 logging.
  forced=True  (F1, registered)  a trigger at a tick where RL-H chose switch still holds >= H_MIN (T_c = t + clip(h_D, H_MIN, H_MAX))
  forced=False (F0)              if RL-H chose switch at the trigger tick, switch NOW and record a zero-hold commitment T_c = t
  keep=False   (M1, registered)  the message is withdrawn at T_c ('unavailable' during the yellow)
  keep=True    (M0)              after T_c, links served by the committed next green keep ttg = T_c + YELLOW + OBS - t until that onset
H1 log: at every trigger, RL-H's action and Q-gap (Q_switch - Q_keep); at every held decision tick, the action RL-H would choose and its Q-gap.
With forced=True, keep=False every simulation-touching operation is the parent's, in the parent's order (check KD-1)."""
from __future__ import annotations
import numpy as np
import scripts.CITY_env as CE
from scripts.CITY_env import DT_L, MIN_G, YELLOW
import scripts.CITY_m3p_rpc as RPC

OBS, H_MIN, H_MAX = RPC.OBS, RPC.H_MIN, RPC.H_MAX
UNAV = dict(ttg=0.0, ttr=0.0, valid=False, source='unavailable')


class LightRPC2(RPC.LightRPC):
    def __init__(self, info, qnet, trigger='receiver', p_rate=None, seed=0, forced=True, keep=False):
        super().__init__(info, qnet, trigger, p_rate, seed); self.forced, self.keep = forced, keep; self.onset = {}
        self.log.update(issue_switch=0, issue_keep=0, issue_gap=[], held_switch=0, held_keep=0, held_gap=[], zero_hold=0, kept_msgs=0)

    def step(self, t):
        ls = CE.ls
        for tid, (ton, _g2) in list(self.onset.items()):
            if t >= ton:
                del self.onset[tid]
        for tid, Tc in list(self.pending.items()):
            if t >= Tc:
                d = self.info.tls[tid]; ph = ls.trafficlight.getPhase(tid); ls.trafficlight.setPhase(tid, (ph + 1) % d['n_phases'])
                self.log['realised'].append((tid, Tc, float(t))); del self.pending[tid]
                if self.keep and ph in d['greens']:
                    self.onset[tid] = (Tc + YELLOW + OBS, d['greens'][(d['greens'].index(ph) + 1) % len(d['greens'])])
        if int(t) % DT_L:
            return
        todo, O, H = [], [], []
        for tid in self.ids:
            o, cur = self._obs(tid)
            if cur < 0:
                continue
            if tid in self.pending:
                ls.trafficlight.setPhaseDuration(tid, 1e5); self.log['overridden'] += 1; H.append(o); continue
            if ls.trafficlight.getSpentDuration(tid) < MIN_G:
                ls.trafficlight.setPhaseDuration(tid, 1e5); continue
            todo.append((tid, cur, o)); O.append(o)
        if H:                                                         # H1: what RL-H would choose at held ticks (no simulation effect)
            for q in self._q(np.stack(H)).numpy():
                g = float(q[1] - q[0]); self.log['held_gap'].append(g); self.log['held_switch' if g > 0 else 'held_keep'] += 1
        if not todo:
            return
        Q = self._q(np.stack(O)); A = Q.argmax(1).numpy(); Qn = Q.numpy()
        for (tid, cur, o), a, q in zip(todo, A, Qn):
            self.log['decisions'] += 1; g = self.info.tls[tid]['greens'][cur]; trig = False
            if self.trigger != 'none' and self.fleet is not None:
                self.log['ticks_total'] += 1; hD = self.h_D(o)
                if self.trigger == 'receiver':
                    trig = self._eligible_receiver(tid, g, hD)
                elif self.trigger == 'eta':
                    trig = self._eta(tid)
                elif self.trigger == 'random':
                    trig = self.rng.random() < self.p_rate.get(tid, 0.0)
            if trig:
                self.log['issue_switch' if a == 1 else 'issue_keep'] += 1; self.log['issue_gap'].append(float(q[1] - q[0]))
                if not self.forced and a == 1:                        # F0: switch now (as RL-H), zero-hold commitment
                    d = self.info.tls[tid]; self.log['commits'].append((tid, float(t), float(t))); self.log['zero_hold'] += 1
                    ls.trafficlight.setPhase(tid, (d['greens'][cur] + 1) % d['n_phases']); self.log['realised'].append((tid, float(t), float(t)))
                    if self.keep:
                        self.onset[tid] = (float(t) + YELLOW + OBS, d['greens'][(cur + 1) % len(d['greens'])])
                    continue
                Tc = float(t + min(max(hD, H_MIN), H_MAX)); self.pending[tid] = Tc; self.log['commits'].append((tid, float(t), Tc))
                ls.trafficlight.setPhaseDuration(tid, 1e5); continue
            if a == 1:
                d = self.info.tls[tid]; ls.trafficlight.setPhase(tid, (d['greens'][cur] + 1) % d['n_phases'])
            else:
                ls.trafficlight.setPhaseDuration(tid, 1e5)

    def spat(self, tid, link):
        if tid in self.pending:
            return super().spat(tid, link)
        if self.keep and tid in self.onset:
            ls = CE.ls; t = ls.simulation.getTime(); ton, g2 = self.onset[tid]
            if t < ton:
                if self.states.get(tid) is None:
                    self._served(tid, link)
                st = self.states[tid]; ph = ls.trafficlight.getPhase(tid)
                if st[g2][link] in 'Gg' and st[ph][link] not in 'Gg':
                    self.log['kept_msgs'] += 1; return dict(ttg=ton - t, ttr=0.0, valid=True, source='commitment-onset')
        return UNAV
