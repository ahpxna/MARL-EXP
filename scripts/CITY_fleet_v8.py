#!/usr/bin/env python3
"""Fleet v8 (04/10/2026; PROTOCOL_CITY_SPAT_PILOT_20261004 Amendments R1 / R2): shared pieces for the PPO eco-driving pilot.
  * build_obs     13 inputs: dist/200, v/14, own-movement G/y/r one-hot, PHASE AGE getSpentDuration/60 (both arms), leader gap/100 and
                  speed/14 (none -> 1, v_allowed/14), follower gap/100 and speed/14 (none -> 1, 0), [ttg/90, ttr/90 (<= 1), valid]; the
                  no-SPaT arm gets [0, 0, 0] (the ONLY difference between the arms)
  * Net           Gaussian actor (64x64 tanh, state-independent log-std) on the pre-squash u; a = LO + (tanh(u)+1)/2 (HI-LO); log-prob is
                  taken on u (the squash is deterministic, so PPO ratios on the same u are exact); separate 64x64 tanh critic
  * PhaseRewardB  Jayawardana & Wu 2022 Eq. 9-10 / Table III as printed, per light and program-phase interval, over ALL vehicles on
                  the light's incoming lanes; f in L/s (mg/s / 745 000), v / lane max speed, stopped vehicle-second share; exponent
                  1000 f capped at 30 (counted); R1 if some vehicle has v < 0.1 within the first 10 m of an incoming lane; credited
                  to each agent's LAST decision on that light inside the interval; the open interval at the episode cut is dropped
  * CarPPO        per-vehicle segments (consecutive seconds); a teleport / discontinuity / episode cut pops the last decision
                  (outcome unobserved) and closes the segment as TRUNCATED with bootstrap V(popped obs); zone exit and arrival are
                  TERMINAL (exit link not costed); setSpeed(clip(v + a, 0, v_allowed)); setSpeed(-1) on leaving the zone
  * gae           per segment, gamma 0.99, lambda 0.95
  * CarGLOSA      simple heuristic GLOSA with the same SPaT: on non-green with valid ttg, v = min(v_allowed, d / ttg); else release"""
from __future__ import annotations
import hashlib, math
import numpy as np
import torch
from torch import nn
import scripts.CITY_env as CE
from scripts.CITY_env import ZONE, _stable_u
from scripts.CITY_spat_feature import spat

INVALID = -1073741824.0; LO, HI = -3.0, 2.6; OBS_DIM = 13; MG_PER_L = 745000.0; EXP_CAP = 30.0; GAMMA, LAM = 0.99, 0.95
MU = dict(m1=-100.0, m2=-5.0, m3=5.0, m4=-5.0, m5=5.0, m6=-10.0, m7=-7.0, m8=-3.0, m9=1000.0, m10=4.0, m11=-10.0, delta=0.01)
REWARD_SCALE = 0.1          # rewards are divided by 10 for learning (a constant factor: policy-invariant); logs use the printed scale


def ok(x, nonneg=True):
    return x is not None and math.isfinite(x) and x > INVALID / 2 and (x >= 0 or not nonneg)


def squash(u):
    return LO + (np.tanh(u) + 1.0) * 0.5 * (HI - LO)


class Net(nn.Module):
    def __init__(self, seed):
        super().__init__(); torch.manual_seed(seed)
        mk = lambda o: nn.Sequential(nn.Linear(OBS_DIM, 64), nn.Tanh(), nn.Linear(64, 64), nn.Tanh(), nn.Linear(64, o))
        self.pi, self.v = mk(1), mk(1); self.log_std = nn.Parameter(torch.full((1,), -0.5))

    def dist(self, O):
        return torch.distributions.Normal(self.pi(O)[:, 0], self.log_std.exp().expand(O.shape[0]))

    def value(self, O):
        return self.v(O)[:, 0]


def build_obs(ls, v, nt0, sp, vlim, spat_on, stats):
    tid, link, dist, st = nt0
    g, y = st in 'Gg', st in 'yY'
    lead = ls.vehicle.getLeader(v, 100.0)
    if lead and lead[0]:
        lsp = ls.vehicle.getSpeed(lead[0]); lg, lsv = lead[1] / 100.0, (lsp / 14.0 if ok(lsp) else vlim / 14.0)
    else:
        lg, lsv = 1.0, vlim / 14.0
    fol = ls.vehicle.getFollower(v, 100.0)
    if fol and fol[0] and fol[1] >= 0:
        fsp = ls.vehicle.getSpeed(fol[0]); fg, fsv = min(fol[1], 100.0) / 100.0, (fsp / 14.0 if ok(fsp) else 0.0)
    else:
        fg, fsv = 1.0, 0.0
    if spat_on:
        s = spat(tid, link); ttg, ttr, val = s['ttg'] / 90.0, min(s['ttr'], 90.0) / 90.0, float(s['valid'])
        stats['spat_valid'] += int(s['valid']); stats['spat_n'] += 1
    else:
        ttg = ttr = val = 0.0
    return np.array([dist / ZONE, sp / 14.0, float(g), float(y), float(not (g or y)), ls.trafficlight.getSpentDuration(tid) / 60.0,
                     min(lg, 1.0), lsv, fg, fsv, ttg, ttr, val], np.float32)


def phase_reward_b(f, v, s, start_stop, stats=None):
    """Eq. 9-10 as printed.  f in L/s, v in [0, 1], s in [0, 1].  Returns (reward, branch)."""
    if start_stop:
        return MU['m1'], 'R1'
    if f <= MU['delta']:
        if s == 0:
            return MU['m2'] + MU['m3'] * math.exp(v), 'R2'
        return MU['m4'] + MU['m5'] * math.exp(v) + MU['m6'] * s, 'R3'
    x = MU['m9'] * f
    if x > EXP_CAP:
        x = EXP_CAP
        if stats is not None:
            stats['capped'] += 1
    return MU['m7'] + MU['m8'] * math.exp(x) + MU['m10'] * math.exp(v) + MU['m11'] * s, 'R4'


class PhaseRewardB:
    def __init__(self, stats):
        ls = CE.ls; self.stats = stats; self.lights = {}
        for tid in ls.trafficlight.getIDList():
            lanes = sorted(set(ls.trafficlight.getControlledLanes(tid)))
            self.lights[tid] = dict(lanes=[(l, ls.lane.getLength(l), ls.lane.getMaxSpeed(l)) for l in lanes], phase=None, acc=None, credit={})
        self.log = []                                          # (t_end, tid, n_vs, f, v, s, start_stop, reward, branch, n_credited)

    def _reset(self, L, ph):
        L['phase'] = ph; L['acc'] = [0, 0.0, 0.0, 0, False]; L['credit'] = {}    # [vehicle-seconds, fuel L, v/vmax, stopped, start-stop]

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
                    if not (ok(sp) and ok(fu, nonneg=False)):
                        self.stats['b_invalid'] += 1; continue
                    a[0] += 1; a[1] += max(fu, 0.0) / MG_PER_L; a[2] += min(sp / vmax, 1.0) if vmax > 0 else 0.0
                    if sp < 0.1:
                        a[3] += 1
                        if ls.vehicle.getLanePosition(v) <= 10.0:
                            a[4] = True

    def credit(self, tid, dec):
        self.lights[tid]['credit'][dec['vid']] = dec            # the agent's LAST decision on this light in the interval

    def _close(self, t, tid, L):
        a = L['acc']
        if a[0] == 0:
            self.stats['b_empty'] += 1; return
        f, v, s = a[1] / a[0], a[2] / a[0], a[3] / a[0]
        r, br = phase_reward_b(f, v, s, a[4], self.stats); self.stats['b_' + br] += 1; n = 0
        for dec in L['credit'].values():
            if not dec.get('dropped'):
                dec['rew'] += r; n += 1
        self.log.append((t, tid, a[0], f, v, s, a[4], r, br, n))


class CarPPO:
    """Training (record=True, stochastic) or evaluation (deterministic) fleet; eval4-compatible attributes."""
    def __init__(self, net, rho, seed, spat_on, deterministic=False, record=True, reward='B'):
        self.net, self.rho, self.seed, self.spat_on, self.det, self.record = net, rho, seed, spat_on, deterministic, record
        self.agents, self.open, self.segments = set(), {}, []
        self.stats = dict(exc=0, invalid=0, gap=0, popped=0, teleport_hidden=0, spat_valid=0, spat_n=0, capped=0, b_invalid=0, b_empty=0,
                          b_R1=0, b_R2=0, b_R3=0, b_R4=0, decisions=0, terminal_exit=0, terminal_arrival=0)
        self.tracker = None; self.reward = reward; self.fired = 0; self.decisions = 0; self.digest = hashlib.sha256(); self.cmd_log = []
        self.ctrl = set()          # vehicles commanded at least once since entering the zone (eval-mode release, fix 04/10 14:01)

    def is_agent(self, vid):
        return _stable_u(self.seed, vid) < self.rho

    def _close(self, v, end, boot_obs=None):
        seg = self.open.pop(v, None)
        if not seg:
            return
        if end == 'truncated':
            last = seg['dec'].pop(); last['dropped'] = True; self.stats['popped'] += 1
            if last['rew'] != 0.0:
                self.stats['popped_with_reward'] = self.stats.get('popped_with_reward', 0) + 1
            if not seg['dec']:
                return
            seg['boot_obs'] = last['obs']
        seg['end'] = end; self.segments.append(seg)

    def step(self, t):
        ls = CE.ls
        if self.tracker is None and self.reward == 'B':
            self.tracker = PhaseRewardB(self.stats)
        if self.tracker is not None:
            self.tracker.step(t)
        for v in ls.simulation.getDepartedIDList():
            if self.is_agent(v):
                self.agents.add(v)
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
            if lane == '' or not ok(sp):
                self.stats['teleport_hidden'] += 1
                if v in self.open:
                    self.stats['gap'] += 1; self._close(v, 'truncated')
                continue
            try:
                nt = ls.vehicle.getNextTLS(v)
            except Exception:
                self.stats['exc'] += 1; continue
            if not nt or nt[0][2] > ZONE:
                if v in self.open:
                    self.stats['terminal_exit'] += 1; self._close(v, 'terminal')
                    try:
                        ls.vehicle.setSpeed(v, -1)
                    except Exception:
                        pass
                elif not self.record and v in self.ctrl:              # FIX (evaluation mode only): without segments the exit release was
                    try:                                              # never sent, so cars kept their last commanded speed outside the zone
                        ls.vehicle.setSpeed(v, -1)
                    except Exception:
                        pass
                self.ctrl.discard(v)
                continue
            try:
                vlim = ls.vehicle.getAllowedSpeed(v)
                if not (ok(vlim) and vlim > 0):
                    self.stats['invalid'] += 1; continue
                o = build_obs(ls, v, nt[0], sp, vlim, self.spat_on, self.stats)
            except Exception:
                self.stats['exc'] += 1; continue
            if v in self.open and self.open[v]['dec'][-1]['t'] != t - 1:     # a skipped second: cut the segment
                self.stats['gap'] += 1; self._close(v, 'truncated')
            todo.append((v, nt[0][0], sp, vlim, o))
        if not todo:
            return
        O = torch.as_tensor(np.stack([x[4] for x in todo]))
        with torch.no_grad():
            d = self.net.dist(O); U = d.mean if self.det else d.sample(); LP = d.log_prob(U); V = self.net.value(O)
        U, LP, V = U.numpy(), LP.numpy(), V.numpy(); A = squash(U)
        for (v, tid, sp, vlim, o), u, lp, val, a in zip(todo, U, LP, V, A):
            cmd = float(min(max(sp + float(a), 0.0), vlim))
            try:
                ls.vehicle.setSpeed(v, cmd)
            except Exception:
                self.stats['exc'] += 1; continue
            self.decisions += 1; self.stats['decisions'] += 1; self.ctrl.add(v)
            if self.record:
                dec = dict(vid=v, t=t, obs=o, u=float(u), logp=float(lp), val=float(val), a=float(a), sp=sp, cmd=cmd, rew=0.0, tid=tid)
                self.open.setdefault(v, dict(vid=v, dec=[], end=None, boot_obs=None))['dec'].append(dec)
                if self.tracker is not None:
                    self.tracker.credit(tid, dec)
                self.cmd_log.append((t, v, cmd))
        self.digest.update(f'{t}|{len(todo)}|{float(np.sum(A)):.6f}'.encode())

    def finish(self):
        """Episode cut: every open segment is truncated (last decision popped, bootstrap on its obs)."""
        for v in list(self.open):
            self._close(v, 'truncated')


def gae(segments, net, gamma=GAMMA, lam=LAM, scale=REWARD_SCALE):
    """Returns flat arrays obs, u, logp, adv, ret.  Per segment; terminal -> next value 0; truncated -> V(boot_obs)."""
    allO, allU, allLP, allA, allR = [], [], [], [], []
    for seg in segments:
        dec = seg['dec']
        if not dec:
            continue
        O = np.stack([d['obs'] for d in dec]); r = np.array([d['rew'] for d in dec], np.float64) * scale
        with torch.no_grad():
            V = net.value(torch.as_tensor(O)).numpy().astype(np.float64)
            boot = 0.0 if seg['end'] == 'terminal' else float(net.value(torch.as_tensor(seg['boot_obs'][None]))[0])
        nxt = np.append(V[1:], boot); delta = r + gamma * nxt - V; A = np.zeros(len(dec)); run = 0.0
        for k in range(len(dec) - 1, -1, -1):
            run = delta[k] + gamma * lam * run; A[k] = run
        allO.append(O); allU.append([d['u'] for d in dec]); allLP.append([d['logp'] for d in dec]); allA.append(A); allR.append(A + V)
    if not allO:
        return None
    return (np.concatenate(allO).astype(np.float32), np.concatenate(allU).astype(np.float32), np.concatenate(allLP).astype(np.float32),
            np.concatenate(allA).astype(np.float32), np.concatenate(allR).astype(np.float32))


def ppo_update(net, opt, batch, epochs=4, mb=4096, clip=0.2, vcoef=0.5, ent=0.0, gclip=0.5, rng=None):
    O, U, LP0, A, R = (torch.as_tensor(x) for x in batch); A = (A - A.mean()) / (A.std() + 1e-8); n = len(O); out = []
    rng = rng or np.random.default_rng(0)
    for _ in range(epochs):
        idx = rng.permutation(n)
        for s in range(0, n, mb):
            j = torch.as_tensor(idx[s:s + mb]); d = net.dist(O[j]); lp = d.log_prob(U[j]); ratio = torch.exp(lp - LP0[j])
            pl = -torch.min(ratio * A[j], torch.clamp(ratio, 1 - clip, 1 + clip) * A[j]).mean(); vl = ((net.value(O[j]) - R[j]) ** 2).mean()
            loss = pl + vcoef * vl - ent * d.entropy().mean(); opt.zero_grad(); loss.backward(); nn.utils.clip_grad_norm_(net.parameters(), gclip); opt.step()
            out.append((pl.item(), vl.item(), (ratio - 1).abs().mean().item()))
    return np.mean(out, axis=0) if out else (float('nan'),) * 3


class CarGLOSA:
    """Simple heuristic GLOSA (NOT a published algorithm): on a non-green own movement with a valid ttg, command
    v = min(v_allowed, d / ttg); otherwise release to SUMO.  Same SPaT feature as the learned arm."""
    def __init__(self, rho, seed):
        self.rho, self.seed, self.agents = rho, seed, set(); self.fired = 0; self.decisions = 0; self.digest = hashlib.sha256()
        self.stats = dict(spat_valid=0, spat_n=0)

    def is_agent(self, vid):
        return _stable_u(self.seed, vid) < self.rho

    def step(self, t):
        ls = CE.ls
        for v in ls.simulation.getDepartedIDList():
            if self.is_agent(v):
                self.agents.add(v)
        for v in ls.simulation.getArrivedIDList():
            self.agents.discard(v)
        for v in list(self.agents):
            try:
                nt = ls.vehicle.getNextTLS(v)
                if not nt or nt[0][2] > ZONE:
                    ls.vehicle.setSpeed(v, -1); continue
                tid, link, dist, st = nt[0]; s = spat(tid, link); self.decisions += 1; self.stats['spat_n'] += 1; self.stats['spat_valid'] += int(s['valid'])
                if st not in 'Gg' and s['valid'] and s['ttg'] > 0:
                    vlim = ls.vehicle.getAllowedSpeed(v); ls.vehicle.setSpeed(v, float(min(vlim, dist / s['ttg']))); self.fired += 1
                else:
                    ls.vehicle.setSpeed(v, -1)
            except Exception:
                continue
