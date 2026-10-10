#!/usr/bin/env python3
"""M3 core (PROTOCOL_CITY_M3_COMPAT_UPDATE_20261004 + Amendment A1; 04/10/2026).  Pure parts (tickets, penalty, credit) are SUMO-free so the
self-checks S9 / S10 can exercise them on synthetic traces.
  Tickets   one per decision tick during a green occurrence o of light j: (t_k, That_k = t_k + r_0.5(spent), raw and normalised weights at
            ISSUE).  Never replaced; closed at the event (switch = yellow onset); censored at the end of the run.
  penalty   of the CURRENT action at decision t over the OPEN tickets (same occurrence, t - 20 <= t_k <= t - 5), weight type w:
            keep:   sum_k w_k * max(0, (t + DT_L) - max(t, That_k + TAU)) / 10        (late seconds this keep creates)
            switch: sum_k w_k * max(0, That_k - TAU - t) / 10                          (early seconds)
  Credit    pending (o_t, a_t, pens_t) closed at the light's NEXT decision t': (o_t, a_t, r_phys[t, t') - lam * pens_t[w], o_t', 0)
  r_phys    -(sum over seconds in (t, t'] and vehicles on the light's incoming lanes of max(0, 1 - v / v_lane) + 0.5 fuel[mg/s] / 1000)
            / (10 * DT_L); realised speed and fuel only
  Weights   (raw, at issue; fleet agents approaching j): uniform 1; eta = #ETA in [5, 25] s on any movement; active = #eligible (red
            approach, R10 rule active under the deployed provider); receiver = sum over eligible of |dcmd/dttg| from a PURE probe that
            substitutes ttg in BOTH the rule speed and observation feature 10.  Normalised by the common-trace mean, clipped at 10.
  LightE    the RL-H keep/switch logic (identical actions to LightRL / LightRLX raw for the same policy outputs) on a 12-dim input:
            the 7 RL-H features + [n_open / 4, mean(That - t) / 30, sum receiver / 4, sum active / 4, sum eta / 4]."""
from __future__ import annotations
import math
import numpy as np
import torch
from torch import nn
import scripts.CITY_env as CE
from scripts.CITY_env import DT_L, MIN_G, ZONE
import scripts.CITY_fleet_v8 as V8
import scripts.CITY_fleet_v11 as V11
import scripts.CITY_glosa_lane as GL

TAU = 2.0; WIN = (5.0, 20.0); ETA_WIN = (5.0, 25.0); CLIP = 10.0; TYPES = ('uniform', 'eta', 'active', 'receiver'); KAPPA = 0.5


# ------------------------------------------------------------------------------------------------------------------------ pure parts
class Tickets:
    def __init__(self, scale):
        self.scale = scale; self.T = {}; self.closed = set(); self.stats = dict(issued=0, closed=0, censored=0, no_open=0)

    def issue(self, tid, occ, t, That, w_raw):
        wn = {k: (min(CLIP, w_raw[k] / self.scale[k]) if self.scale.get(k, 0) > 0 else 0.0) for k in TYPES}
        self.T.setdefault((tid, occ), []).append(dict(t=float(t), That=float(That), w=dict(w_raw), wn=wn)); self.stats['issued'] += 1

    def open(self, tid, occ, t):
        op = [k for k in self.T.get((tid, occ), []) if t - WIN[1] <= k['t'] <= t - WIN[0]]
        if not op:
            self.stats['no_open'] += 1
        return op

    def close(self, tid, occ):
        if (tid, occ) in self.T and (tid, occ) not in self.closed:
            self.closed.add((tid, occ)); self.stats['closed'] += 1

    def censor(self):
        self.stats['censored'] = sum(1 for key in self.T if key not in self.closed); return self.stats['censored']


def penalty(a, t, open_tickets, wkey):
    if a == 1:
        s = sum(k['wn'][wkey] * max(0.0, k['That'] - TAU - t) for k in open_tickets)
    else:
        s = sum(k['wn'][wkey] * max(0.0, (t + DT_L) - max(t, k['That'] + TAU)) for k in open_tickets)
    return s / 10.0


def features(open_tickets, t):
    if not open_tickets:
        return np.zeros(5, np.float32)
    return np.array([len(open_tickets) / 4.0, float(np.mean([k['That'] - t for k in open_tickets])) / 30.0,
                     sum(k['wn']['receiver'] for k in open_tickets) / 4.0, sum(k['wn']['active'] for k in open_tickets) / 4.0,
                     sum(k['wn']['eta'] for k in open_tickets) / 4.0], np.float32)


class Credit:
    def __init__(self, lam, wkey):
        self.lam, self.wkey = lam, wkey; self.pending = {}; self.trans = []; self.log = []

    def decide(self, tid, t, o, a, pens, r_interval):
        """r_interval = physical reward of the interval since this light's previous decision (the PREVIOUS action's outcome)."""
        if tid in self.pending:
            po, pa, ppen, pt = self.pending[tid]; r = r_interval - self.lam * ppen[self.wkey]
            self.trans.append((po, pa, r, o, 0.0)); self.log.append(dict(tid=tid, t_prev=pt, t=t, a=pa, pen=ppen[self.wkey], r_phys=r_interval, r=r))
        self.pending[tid] = (o, a, pens, t)


# ------------------------------------------------------------------------------------------------------------------- networks
def widen(net7, extra=5):
    """RL-H Sequential(Linear(7,64), ReLU, Linear(64,64), ReLU, Linear(64,2)) -> first layer 7 + extra inputs, new columns ZERO."""
    l0 = net7[0]; new = nn.Linear(l0.in_features + extra, l0.out_features)
    with torch.no_grad():
        new.weight.zero_(); new.weight[:, :l0.in_features] = l0.weight; new.bias.copy_(l0.bias)
    layers = [new] + [m for m in list(net7)[1:]]
    import copy
    return nn.Sequential(*[layers[0]] + [copy.deepcopy(m) for m in layers[1:]])


# --------------------------------------------------------------------------------------------------------------- receiver probe
def eligible(ls, v, nt0, spat_fn):
    tid, link, dist, st = nt0; s = spat_fn(tid, link)
    return st not in 'Gg' and s['valid'] and s['ttg'] > 0 and dist <= V11.DACT and GL.lane_ok(ls, v), s


def r10_cmd(ls, v, nt0, net, spat_fn, ttg=None):
    """The command R10 (CarPPOL, evaluation mode) would send at this state, with ttg substituted in BOTH the rule and obs[10]."""
    tid, link, dist, st = nt0; s = dict(spat_fn(tid, link))
    if ttg is not None:
        s['ttg'] = float(ttg)
    vl = ls.vehicle.getAllowedSpeed(v); sp = ls.vehicle.getSpeed(v); vr = min(vl, dist / s['ttg'])
    old = V8.spat
    V8.spat = lambda a, b, _s=s, _o=old: _s if (a, b) == (tid, link) else _o(a, b)
    try:
        o = V8.build_obs(ls, v, nt0, sp, vl, True, dict(spat_valid=0, spat_n=0))
    finally:
        V8.spat = old
    with torch.no_grad():
        mu = net.dist(torch.as_tensor(o[None])).mean.numpy()[0]
    return float(min(max(vr + V11.DV * math.tanh(float(mu)), 0.0), vl))


def sensitivity(ls, v, nt0, net, spat_fn, ttg):
    h = min(1.0, ttg / 2.0)
    return abs(r10_cmd(ls, v, nt0, net, spat_fn, ttg + h) - r10_cmd(ls, v, nt0, net, spat_fn, ttg - h)) / (2 * h)


def weights_at_issue(ls, tid, fleet, spat_fn):
    w = dict(uniform=1.0, eta=0.0, active=0.0, receiver=0.0)
    if fleet is None:
        return w
    net = getattr(fleet, 'net', None)
    for v in list(getattr(fleet, 'agents', ())):
        try:
            nt = ls.vehicle.getNextTLS(v)
            if not nt or nt[0][0] != tid or nt[0][2] > ZONE:
                continue
            sp = ls.vehicle.getSpeed(v)
            if ETA_WIN[0] <= nt[0][2] / max(sp, 1.0) <= ETA_WIN[1]:
                w['eta'] += 1
            if net is not None:
                ok, s = eligible(ls, v, nt[0], spat_fn)
                if ok:
                    w['active'] += 1; w['receiver'] += sensitivity(ls, v, nt[0], net, spat_fn, s['ttg'])
        except Exception:
            continue
    return w


# ---------------------------------------------------------------------------------------------------------------------- the light
class LightE:
    def __init__(self, info, policy, F, spat_fn, scale, lam=0.0, wkey='uniform', record=False, fleet=None, log_phases=False, log_decisions=False,
                 base='physical'):
        self.info, self.policy, self.F, self.spat_fn, self.base = info, policy, F, spat_fn, base
        self.ids = list(info.tls); self.tickets = Tickets(scale); self.credit = Credit(lam, wkey); self.record = record; self.fleet = fleet
        self.occ = {tid: 0 for tid in self.ids}; self.prev = {}; self.cost = {tid: 0.0 for tid in self.ids}; self.vmax = {}
        self.stats = dict(invalid=0, decisions=0, switches=0); self.log_phases = log_phases; self.P = []; self.S = []
        self.log_decisions = log_decisions; self.dlog = []

    def obs7(self, tid):
        ls = CE.ls; d = self.info.tls[tid]; ph = ls.trafficlight.getPhase(tid)
        h = [sum(ls.lane.getLastStepHaltingNumber(l) for l in s) for s in d['serve']]
        n = [sum(ls.lane.getLastStepVehicleNumber(l) for l in s) for s in d['serve']]
        cur = d['greens'].index(ph) if ph in d['greens'] else -1
        return np.array([h[0] / 10, h[1] / 10, n[0] / 20, n[1] / 20, cur == 0, cur == 1, ls.trafficlight.getSpentDuration(tid) / 60], np.float32), cur, sum(h)

    def _cost(self):
        ls = CE.ls
        for tid in self.ids:
            c = 0.0
            for lane in self.info.tls[tid]['lanes']:
                vm = self.vmax.get(lane) or self.vmax.setdefault(lane, ls.lane.getMaxSpeed(lane))
                for v in ls.lane.getLastStepVehicleIDs(lane):
                    sp, fu = ls.vehicle.getSpeed(v), ls.vehicle.getFuelConsumption(v)
                    if not (V8.ok(sp) and V8.ok(fu, nonneg=False)) or vm <= 0:
                        self.stats['invalid'] += 1; continue
                    c += max(0.0, 1.0 - sp / vm) + KAPPA * max(fu, 0.0) / 1000.0
            self.cost[tid] += c

    def _issue(self, tid, t, g, spent):
        That = t + self.F.rem(tid, g, spent)
        self.tickets.issue(tid, self.occ[tid], t, That, weights_at_issue(CE.ls, tid, self.fleet, self.spat_fn))

    def step(self, t):
        ls = CE.ls
        for tid in self.ids:                                       # green occurrences
            ph = ls.trafficlight.getPhase(tid)
            if ph in self.info.tls[tid]['greens'] and self.prev.get(tid) != ph:
                self.occ[tid] += 1
            self.prev[tid] = ph
        self._cost()
        if int(t) % DT_L == 0:
            todo, O = [], []
            for tid in self.ids:
                o7, cur, halt = self.obs7(tid)
                if cur < 0:
                    continue
                spent = ls.trafficlight.getSpentDuration(tid); g = self.info.tls[tid]['greens'][cur]
                if spent < MIN_G:
                    ls.trafficlight.setPhaseDuration(tid, 1e5); self._issue(tid, t, g, spent); continue
                op = self.tickets.open(tid, self.occ[tid], t)
                todo.append((tid, cur, g, spent, op, halt)); O.append(np.concatenate([o7, features(op, t)]))
            if todo:
                A = np.asarray(self.policy(np.stack(O)))
                for (tid, cur, g, spent, op, halt), o, a in zip(todo, O, A):
                    a = int(a); pens = {k: penalty(a, t, op, k) for k in TYPES}; self.stats['decisions'] += 1
                    r_int = (-halt / 10.0) if self.base == 'queue' else -self.cost[tid] / (10.0 * DT_L); self.cost[tid] = 0.0   # E0-queue: LightRL credit
                    if self.record:
                        self.credit.decide(tid, t, o, a, pens, r_int)
                    if self.log_decisions:
                        self.dlog.append(dict(t=t, tid=tid, a=a, open=[dict(That=k['That'], wn=k['wn'], w=k['w'], t=k['t']) for k in op], pens=pens))
                    if a == 1:
                        d = self.info.tls[tid]; ls.trafficlight.setPhase(tid, (d['greens'][cur] + 1) % d['n_phases'])
                        self.tickets.close(tid, self.occ[tid]); self.stats['switches'] += 1
                    else:
                        ls.trafficlight.setPhaseDuration(tid, 1e5); self._issue(tid, t, g, spent)
        if self.log_phases:
            self.P.append([ls.trafficlight.getPhase(tid) for tid in self.ids]); self.S.append([ls.trafficlight.getSpentDuration(tid) for tid in self.ids])

    def finish(self):
        self.tickets.censor()


def greedy(net):
    def f(O):
        with torch.no_grad():
            return net(torch.as_tensor(np.asarray(O, np.float32))).argmax(1).numpy()
    return f
