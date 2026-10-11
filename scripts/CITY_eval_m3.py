#!/usr/bin/env python3
"""M3 evaluation wrapper (PROTOCOL_CITY_M3_COMPAT_UPDATE_20261004 + A1 + A1b; 04/10/2026): CITY_eval6_v11 (all fleet specs, CITY_eval4.run)
plus M3 lights and SPaT arms.  No frozen file is edited.
Lights (--light):
  M3E:<ckpt>        the fine-tuned E light (LightE, greedy, its own scale and deployed provider table)
  RL-H:<k>          the original learned light (CITY_eval4.build_light)
  M3WC:<k>:<W>      fixed-W commitment: RL-H:k decides; a switch decided at t is executed at t + W (no new decision while pending)
  M3B:<k>:<W>       ETA commitment (B): the switch is delayed and committed W s ahead only if a fleet vehicle with ETA in [5, 20] s approaches
                    on the red movement; otherwise immediate
  M3CYC:<G>         predictable 2-phase cycle: the static program with green G (yellows unchanged), installed at the first step
SPaT arms (--spat-arm), what the fleet's spat() returns:
  none              unavailable (fallback; the reference R with RL-H:k)
  fc:<q>:<table>    empirical forecast quantile q of the given table
  D:<k>:<table>     policy-aware point forecast with RL-H:k's Q-network (queues held; first future tick with Q(switch) > Q(keep);
                    fallback: table median)
  deployed          the M3E checkpoint's own provider table, q 0.5
  commit:<table>    commitment while a switch is pending (green end Ts - t, green onset Ts + YELLOW + OBS - t), else forecast 0.5 of table
  program           the static-program SPaT (exact for M3CYC; CITY_spat_feature.spat)
--base-sigma S      with --fleet L-ACT:0 --guard always: σ-family cars (setImperfection at departure), for light-side cost rows
Sidecar <out>/<tag>_m3.json: arm, light, checkpoint / table hashes, spat calls (total / valid), commanded vehicle-seconds, commitments and
violations (promised vs observed events), forecast error at sampled fleet query times (every 5 s), ticket stats of M3E lights."""
import argparse, hashlib, json, math, sys
from pathlib import Path
import numpy as np
import torch
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_eval4 as E4  # noqa: E402
import scripts.CITY_eval6_v11 as _E  # noqa: E402,F401
import scripts.CITY_env as CE  # noqa: E402
from scripts.CITY_env import DT_L, MIN_G, YELLOW, ZONE  # noqa: E402
import scripts.CITY_xplay2 as X2  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_spat_forecast as FC  # noqa: E402
import scripts.CITY_spat_feature as SF  # noqa: E402
import scripts.CITY_fleet_v8 as V8  # noqa: E402
import scripts.CITY_es_glosa as ES  # noqa: E402
import scripts.CITY_glosa_lane as GL  # noqa: E402
import scripts.CITY_glosa_lane_d as LD  # noqa: E402
import scripts.CITY_fleet_v11 as V11  # noqa: E402
import scripts.CITY_m3_core as M  # noqa: E402

OBS = FC.OBS
pre = argparse.ArgumentParser(add_help=False); pre.add_argument('--spat-arm', required=True); pre.add_argument('--base-sigma', type=float)
A0, REST = pre.parse_known_args()
sha = lambda b: hashlib.sha256(b).hexdigest()
E4.SRC = f"{E4.SRC}+m3:{sha(Path(__file__).read_bytes())}"
CUR = dict(cars=None, light=None, spat=None); LOG = dict(total=0, valid=0, queries=[], commits=[], realised=[], tickets=[], cmd=0, meta={})


# ------------------------------------------------------------------------------------------------------------------ lights
class LightWC:
    def __init__(self, info, policy, W, mode):
        self.info, self.policy, self.W, self.mode = info, policy, W, mode; self.ids = list(info.tls); self.pending = {}; self.fleet = None

    def obs(self, tid):
        ls = CE.ls; d = self.info.tls[tid]; ph = ls.trafficlight.getPhase(tid)
        h = [sum(ls.lane.getLastStepHaltingNumber(l) for l in s) for s in d['serve']]
        n = [sum(ls.lane.getLastStepVehicleNumber(l) for l in s) for s in d['serve']]
        cur = d['greens'].index(ph) if ph in d['greens'] else -1
        return np.array([h[0] / 10, h[1] / 10, n[0] / 20, n[1] / 20, cur == 0, cur == 1, ls.trafficlight.getSpentDuration(tid) / 60], np.float32), cur

    def requests(self, tid):
        ls = CE.ls
        for v in list(getattr(self.fleet, 'agents', ())):
            try:
                nt = ls.vehicle.getNextTLS(v)
                if nt and nt[0][0] == tid and nt[0][2] <= ZONE and nt[0][3] not in 'Gg' and 5 <= nt[0][2] / max(ls.vehicle.getSpeed(v), 1.0) <= 20:
                    return True
            except Exception:
                continue
        return False

    def step(self, t):
        ls = CE.ls
        for tid, te in list(self.pending.items()):
            if t >= te:
                d = self.info.tls[tid]; ph = ls.trafficlight.getPhase(tid); ls.trafficlight.setPhase(tid, (ph + 1) % d['n_phases'])
                LOG['realised'].append((tid, te, float(t))); del self.pending[tid]
        if int(t) % DT_L:
            return
        todo, O = [], []
        for tid in self.ids:
            o, cur = self.obs(tid)
            if cur < 0:
                continue
            if tid in self.pending:
                ls.trafficlight.setPhaseDuration(tid, 1e5); continue
            if ls.trafficlight.getSpentDuration(tid) < MIN_G:
                ls.trafficlight.setPhaseDuration(tid, 1e5); continue
            todo.append((tid, cur)); O.append(o)
        if not todo:
            return
        A = np.asarray(self.policy(np.stack(O)))
        for (tid, cur), a in zip(todo, A):
            if a == 1:
                delay = self.W if self.mode == 'fixed' else (self.W if self.requests(tid) else 0)
                if delay == 0:
                    d = self.info.tls[tid]; ls.trafficlight.setPhase(tid, (d['greens'][cur] + 1) % d['n_phases'])
                else:
                    self.pending[tid] = float(t + delay); LOG['commits'].append((tid, float(t), float(t + delay))); ls.trafficlight.setPhaseDuration(tid, 1e5)
            else:
                ls.trafficlight.setPhaseDuration(tid, 1e5)


def cyc_init(G):
    def f():
        ls = CE.ls
        for tid in ls.trafficlight.getIDList():
            lg = ls.trafficlight.getAllProgramLogics(tid)[0]
            ph = [ls.trafficlight.Phase(float(G) if ('G' in p.state or 'g' in p.state) and 'y' not in p.state.lower() else float(p.duration), p.state) for p in lg.phases]
            ls.trafficlight.setProgramLogic(tid, ls.trafficlight.Logic('cyc', 0, 0, ph)); ls.trafficlight.setProgram(tid, 'cyc')
    return f


_bl = E4.build_light


def build_light(spec, info, adapter, box):
    if spec.startswith('M3E:'):
        p = Path(spec[4:]); d = torch.load(p, weights_only=False); spat_fn, F = FC.make_spat(d['table'], 0.5)
        L = M.LightE(info, M.greedy(d['net']), F, spat_fn, d['scale'])
        LOG['meta'].update(ckpt=str(p), ckpt_sha256=sha(p.read_bytes()), table_sha256=d.get('table_sha256'), arm=d['arm'], lam=d['lam'], k=d['k'])
        CUR.update(light=L, deployed=spat_fn); return Q7.NET_S, L, [], None
    if spec.startswith('M3WC:') or spec.startswith('M3B:'):
        kind, k, W = spec.split(':'); _n, ck, _m = X2.light_spec(f'RL-H:{k}')
        L = LightWC(info, Q7.load_policy(ck), float(W), 'fixed' if kind == 'M3WC' else 'eta'); LOG['meta'].update(rlh_sha256=sha(Path(ck).read_bytes()))
        CUR.update(light=L); return Q7.NET_S, L, [], None
    if spec.startswith('M3CYC:'):
        CUR.update(light=None); return Q7.NET_S, None, [], cyc_init(float(spec.split(':')[1]))
    net, light, extra, init = _bl(spec, info, adapter, box); CUR.update(light=light); return net, light, extra, init


E4.build_light = build_light
_lf = E4.load_fleet


def load_fleet(spec, seed, guard):
    c, p = _lf(spec, seed, guard); CUR['cars'] = c
    if CUR.get('light') is not None and hasattr(CUR['light'], 'fleet'):
        CUR['light'].fleet = c
    LOG.setdefault('cars', []).append(c); return c, p


E4.load_fleet = load_fleet

if A0.base_sigma is not None:                                        # σ-family cars for light-side cost rows (as CITY_eval4_sigma)
    _rlg = E4.CarRLG.step

    def rlg_step(self, t):
        for v in CE.ls.simulation.getDepartedIDList():
            if self.is_agent(v):
                CE.ls.vehicle.setImperfection(v, A0.base_sigma)
        _rlg(self, t)
    E4.CarRLG.step = rlg_step


# ------------------------------------------------------------------------------------------------------------------ SPaT arms
def _serve(tid, link, cache={}):
    if tid not in cache:
        cache[tid] = [p.state for p in CE.ls.trafficlight.getAllProgramLogics(tid)[0].phases]
    return cache[tid]


def make_D(k, table):
    _n, ck, _m = X2.light_spec(f'RL-H:{k}'); net = torch.load(ck, weights_only=False)['net']; net.eval(); spat_fc, F = FC.make_spat(table, 0.5)
    info = Q7.NetInfo(Q7.NET_S); memo = {}

    def rem(tid, g, spent, t):
        key = (tid, t)
        if key not in memo:
            ls = CE.ls; d = info.tls[tid]
            h_ = [sum(ls.lane.getLastStepHaltingNumber(l) for l in s) for s in d['serve']]; n_ = [sum(ls.lane.getLastStepVehicleNumber(l) for l in s) for s in d['serve']]
            cur = d['greens'].index(g); h0 = (DT_L - (int(t) % DT_L)) if int(t) % DT_L else DT_L; r = None
            for h in np.arange(h0, 61, DT_L):
                if spent + h < MIN_G:
                    continue
                o = np.array([[h_[0] / 10, h_[1] / 10, n_[0] / 20, n_[1] / 20, cur == 0, cur == 1, (spent + h) / 60]], np.float32)
                with torch.no_grad():
                    q = net(torch.as_tensor(o))[0]
                if q[1] > q[0]:
                    r = float(h); break
            memo.clear() if len(memo) > 5000 else None; memo[key] = r if r is not None else F.rem(tid, g, spent)
        return memo[key]

    def spat_D(tid, link):
        ls = CE.ls; st = _serve(tid, link); gs = F.G[tid]; serve = {g for g in gs if st[g][link] in 'Gg'}
        if len(serve) == len(gs) or not serve:
            return spat_fc(tid, link)
        ph = ls.trafficlight.getPhase(tid); spent = ls.trafficlight.getSpentDuration(tid); t = ls.simulation.getTime()
        if ph not in gs:
            return spat_fc(tid, link)                               # yellow: exact program timer, as the provider
        r = rem(tid, ph, spent, t)
        if ph in serve:
            return dict(ttg=0.0, ttr=r + OBS, valid=True, source='forecast:D')
        return dict(ttg=r + YELLOW + OBS, ttr=0.0, valid=True, source='forecast:D')
    return spat_D


def make_commit(table):
    spat_fc, F = FC.make_spat(table, 0.5)

    def spat_c(tid, link):
        L = CUR.get('light'); ls = CE.ls
        if L is not None and tid in getattr(L, 'pending', {}):
            Ts = L.pending[tid]; t = ls.simulation.getTime(); st = _serve(tid, link); ph = ls.trafficlight.getPhase(tid)
            if st[ph][link] in 'Gg':
                return dict(ttg=0.0, ttr=Ts - t, valid=True, source='commitment')
            return dict(ttg=Ts - t + YELLOW + OBS, ttr=0.0, valid=True, source='commitment')
        return spat_fc(tid, link)
    return spat_c


arm = A0.spat_arm
if arm == 'none':
    BASE = lambda tid, link: dict(ttg=0.0, ttr=0.0, valid=False, source='unavailable')  # noqa: E731
elif arm.startswith('fc:'):
    _, q, tb = arm.split(':', 2); BASE = FC.make_spat(json.loads(Path(tb).read_text()), float(q))[0]; LOG['meta']['table_sha256'] = sha(Path(tb).read_bytes())
elif arm.startswith('D:'):
    _, k, tb = arm.split(':', 2); BASE = make_D(int(k), json.loads(Path(tb).read_text())); LOG['meta']['table_sha256'] = sha(Path(tb).read_bytes())
elif arm.startswith('commit:'):
    tb = arm.split(':', 1)[1]; BASE = make_commit(json.loads(Path(tb).read_text())); LOG['meta']['table_sha256'] = sha(Path(tb).read_bytes())
elif arm == 'program':
    BASE = SF.spat
elif arm == 'deployed':
    BASE = lambda tid, link: CUR['deployed'](tid, link)  # noqa: E731
else:
    raise SystemExit(f'unknown spat arm {arm}')


def spat_m3(tid, link):
    s = BASE(tid, link); LOG['total'] += 1; LOG['valid'] += bool(s['valid'])
    t = CE.ls.simulation.getTime()
    if s['valid'] and int(t) % 5 == 0 and len(LOG['queries']) < 400000:
        _serve(tid, link)                                           # cache the phase states while the network is live
        LOG['queries'].append((float(t), tid, int(link), float(s['ttg']), float(min(s['ttr'], 999.0))))
    return s


for m in (V8, ES, GL, LD, V11):
    m.spat = spat_m3

# phase observer (for commitment / forecast realisation): appended to the light step through a tiny wrapper of CE.run_episode's loop
_run = CE.run_episode
PHASES = []


def run_episode(net, rou, seed, light, cars, end=3600, tripinfo=None, extra=()):
    PHASES.clear()

    class Obs:
        def step(self, t):
            light.step(t)
            ls = CE.ls; PHASES.append((float(t), {tid: ls.trafficlight.getPhase(tid) for tid in ls.trafficlight.getIDList()}))
    return _run(net, rou, seed, Obs(), cars, end=end, tripinfo=tripinfo, extra=extra)


E4.run_episode = run_episode


def realise():
    """Observed events from the phase log: per light, the times its phase changed (t, from, to)."""
    ch = {}
    prev = {}
    for t, ph in PHASES:
        for tid, p in ph.items():
            if tid in prev and p != prev[tid]:
                ch.setdefault(tid, []).append((t, prev[tid], p))
            prev[tid] = p
    return ch


_main_run = E4.run


def run(a, seed, end):
    LOG['queries'].clear(); n_r0, n_c0 = len(LOG['realised']), len(LOG['commits'])
    out = _main_run(a, seed, end); ch = realise(); per = LOG.setdefault('per_seed', {}); S = per.setdefault(str(seed), {})
    # commitment violations: promised green end Ts vs the observed change out of that green at or after the commit time
    viol, ncom, cens = 0, 0, 0; t_last = PHASES[-1][0] if PHASES else 0.0
    for tid, t0, Ts in LOG['commits'][n_c0:]:
        obs_end = next((t for t, a_, b_ in ch.get(tid, []) if t >= t0), None); ncom += 1
        if obs_end is None and Ts > t_last:
            cens += 1                                               # the run ended before the promised time: censored, not a violation
        elif obs_end is None or abs(obs_end - Ts) > 1e-9:
            viol += 1
    S.update(commits=ncom, violations=viol, censored=cens)
    # forecast error at sampled query times: predicted green-onset (t + ttg) vs the observed onset of a phase serving the link
    errs = []
    for t, tid, link, ttg, _ttr in LOG['queries']:
        if ttg <= 0 or tid not in _serve.__defaults__[0]:
            continue
        st = _serve(tid, link); onset = next((tt for tt, a_, b_ in ch.get(tid, []) if tt > t and st[b_][link] in 'Gg'), None)
        if onset is not None:
            errs.append((t + ttg) - onset)
    S.update(queries=len(errs), mae=float(np.mean(np.abs(errs))) if errs else None, bias=float(np.mean(errs)) if errs else None,
             med_abs=float(np.median(np.abs(errs))) if errs else None)
    L = CUR.get('light')
    if isinstance(L, M.LightE):
        L.finish(); S.update(tickets=dict(L.tickets.stats), decisions=L.stats['decisions'], switches=L.stats['switches'])
    c = CUR.get('cars'); S.update(commanded=int(c.decisions if isinstance(c, V11.CarPPOL) else getattr(c, 'fired', 0)) if c is not None else 0)
    return out


E4.run = run

if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--light', default='ACT'); p.add_argument('--light-obs', default='raw'); p.add_argument('--light-fallback', default='none')
    p.add_argument('--fleet', default='human'); p.add_argument('--guard', default='none')
    p.add_argument('--record'); p.add_argument('--replay'); p.add_argument('--replay-dir'); p.add_argument('--discharge', action='store_true'); p.add_argument('--delay-trace', action='store_true')
    p.add_argument('--swap-at', type=float); p.add_argument('--swap-light'); p.add_argument('--swap-fleet')
    p.add_argument('--seeds', type=int, nargs='+', default=[100, 101, 102, 103, 104]); p.add_argument('--smoke', action='store_true')
    p.add_argument('--tag'); p.add_argument('--out', required=True)
    a = p.parse_args(REST); E4.main(a)
    side = dict(arm=arm, light=a.light, fleet=a.fleet, base_sigma=A0.base_sigma, spat_total=LOG['total'], spat_valid=LOG['valid'], meta=LOG['meta'],
                per_seed=LOG.get('per_seed', {}), source_sha256=sha(Path(__file__).read_bytes()))
    Path(a.out, f'{a.tag}_m3.json').write_text(json.dumps(side)); print('m3 sidecar', json.dumps({k: v for k, v in side.items() if k != 'per_seed'})[:300], flush=True)
