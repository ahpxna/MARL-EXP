#!/usr/bin/env python3
"""W20 self-checks (PROTOCOL_CITY_WAVE20_20261009).  Run through CITY_w20_run.py.  One 600-s episode per check, traffic seed 0, all SUMO
drivers (no fleet controller).
  obs <k>     KW20-1: the deployed light's observation (evaluator light, raw) equals an independent recomputation written here every 5 s for
              every signal (RESCO sticky queued / wait kept per (vehicle, lane) from getLaneID, sumo-rl density / queue from lane counts);
              actions equal the policy's argmax.  Must be 0 mismatches.
  bis0 <k>    KW20-2: TSI-G with an empty fleet (rho 0) equals the raw observation exactly (k an AH light or a W20 light).
  twin <k>    KW20-3 (descriptive): human-twin fidelity.  Fleet members (u(0, id) < 0.5) are driven by SUMO like everyone, so their twins should
              reproduce their real halting; reports per-vehicle-second agreement and the per-lane member halting-count error at 5-s ticks.
Usage: CITY_w20_run.py scripts/CITY_w20_check.py <mode> <k>"""
import sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_eval4 as E4  # noqa: E402
import scripts.CITY_xplay2 as X2  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_w19_obs as W  # noqa: E402
import scripts.CITY_w20_bench as B  # noqa: E402


class Indep:
    """RESCO semantics, written independently: key (vehicle, lane); queued once speed < 0.1 on that lane; wait += 1 per second while queued."""

    def __init__(self, info):
        self.info = info; self.st = {}; self.lanes = {l for d in info.tls.values() for s in d['serve'] for l in s}

    def tick(self):
        ls = CE.ls; keep = {}
        for v in ls.vehicle.getIDList():
            l = ls.vehicle.getLaneID(v)
            if l not in self.lanes:
                continue
            q, w = self.st.get((v, l), (False, 0.0)); sp = ls.vehicle.getSpeed(v)
            q = q or sp < 0.1; w = w + 1.0 if q else w; keep[(v, l)] = (q, w)
        self.st = keep

    def lane(self, l):
        ls = CE.ls; ids = ls.lane.getLastStepVehicleIDs(l); q = sum(self.st.get((v, l), (False, 0))[0] for v in ids)
        w = sum(self.st.get((v, l), (False, 0.0))[1] for v in ids); return len(ids), q, w

    def expected(self, tid, kind, spd):
        ls = CE.ls; d = self.info.tls[tid]; ph = ls.trafficlight.getPhase(tid); cur = d['greens'].index(ph) if ph in d['greens'] else -1
        sp = ls.trafficlight.getSpentDuration(tid); lanes = list(d['serve'][0]) + list(d['serve'][1])
        if kind == 'SRL':
            return np.array([cur == 0, cur == 1, float(sp >= 5)] + [ls.lane.getLastStepVehicleNumber(l) / (ls.lane.getLength(l) / 7.5) for l in lanes]
                            + [ls.lane.getLastStepHaltingNumber(l) / (ls.lane.getLength(l) / 7.5) for l in lanes], np.float32)
        if kind == 'RDQ':
            o = []
            for g, s in enumerate(d['serve']):
                for l in s:
                    n, q, w = self.lane(l); o += [float(cur == g), (n - q) / 28, w / 28, q / 28, spd.get(l, 0.0) / 20 / 28]
            return np.array(o, np.float32)
        if kind == 'RMP':
            outs = [set(), set()]
            for lk in ls.trafficlight.getControlledLinks(tid):
                for i_l, o_l, _v in lk:
                    for g in (0, 1):
                        if i_l in d['serve'][g] and o_l in self.lanes:
                            outs[g].add(o_l)
            p = [sum(self.lane(l)[1] for l in d['serve'][g]) - sum(self.lane(l)[1] for l in outs[g]) for g in (0, 1)]
            return np.array([float(max(cur, 0)), p[0], p[1]], np.float32)
        if kind == 'RWV':
            return np.array([sum(ls.lane.getLastStepVehicleNumber(l) for l in d['serve'][g]) / 28 for g in (0, 1)] + [cur == 0, cur == 1], np.float32)
        raise ValueError(kind)


def build(k, adapter):
    _n, lck, _m = X2.light_spec(f'RL-H:{k}'); info = CE.NetInfo(Q7.NET_S)
    _n2, light, _x, _i = E4.build_light(f'RL-H:{k}', info, adapter, None); return light, info, Q7.load_policy(lck)


def main(mode, k):
    B.TRACK.reset(); B.TRACK.seed = 0; B.TRACK.info = None
    light, info, pol = build(k, 'bis' if mode in ('bis0', 'twin') else 'raw'); kind = W.obs_kind()
    if mode == 'bis0':
        B.TRACK.rho = 0.0
    ind = Indep(info); st = dict(n=0, bad=0, act=0, dec=0, agree=0, vs=0, err=[], first=None); inner = light.policy; avgsp = {}

    def probe(O):
        a = np.asarray(inner(O)); b = pol(O); st['act'] += int((a != b).sum()); st['dec'] += len(a); return a
    light.policy = probe

    class P:
        def step(self, t):
            ind.tick(); B.TRACK.update(info, t)
            if mode == 'obs' and kind == 'RDQ':                       # RESCO average speed per vehicle (since entering the lane), independent
                acc = avgsp.setdefault('_acc', {}); now = {}          # per (vehicle, lane) while continuously on it (RESCO: a new record per lane visit)
                for l in ind.lanes:
                    tot = 0.0
                    for v in CE.ls.lane.getLastStepVehicleIDs(l):
                        r = acc.get((v, l), [0.0, 0]); r = [r[0] + CE.ls.vehicle.getSpeed(v), r[1] + 1]; now[(v, l)] = r; tot += r[0] / r[1]
                    avgsp[l] = tot
                avgsp['_acc'] = now
            if mode == 'twin':
                for r in B.TRACK.veh.values():
                    if r['fleet']:
                        th, rh = r['tw']['s'] == 'halt', r['v'] < 0.1; st['vs'] += 1; st['agree'] += th == rh
                        cm = st.setdefault('cm', [0, 0, 0, 0]); cm[2 * th + rh] += 1
            if int(t) % CE.DT_L == 0:
                for tid in light.ids:
                    o, _h, _c = light.obs(tid); st['n'] += 1
                    if mode == 'obs':
                        e = ind.expected(tid, kind, avgsp)
                    elif mode == 'bis0':
                        B.TRACK.bis = False; e = light.__class__.__mro__[1].obs(light, tid)[0] if False else W._ORIG_OBS(light, tid)[0] if kind == 'A' else None; B.TRACK.bis = True
                        if e is None:
                            B.TRACK.bis = False; e = B.family_obs(light, tid)[0]; B.TRACK.bis = True
                    else:
                        d = info.tls[tid]
                        for s in d['serve']:
                            for l in s:
                                recs = [r for r in B.TRACK.bylane.get(l, ()) if r['fleet']]
                                st['err'].append(sum(r['tw']['s'] == 'halt' for r in recs) - sum(r['v'] < 0.1 for r in recs))
                        e = o
                    if o.shape != e.shape or not np.allclose(o, e, atol=1e-5):
                        st['bad'] += 1
                        if st['first'] is None:
                            st['first'] = (tid, np.round(o, 4).tolist(), np.round(e, 4).tolist())
            light.step(t)
    CE.run_episode(Q7.NET_S, Q7.ROU.format(0), 0, P(), None, end=600)
    if mode == 'twin':
        err = np.array(st['err']); print(f'KW20-3 k{k} {W.CUR["fam"]}: member vehicle-seconds {st["vs"]}, twin == real halting {st["agree"] / max(1, st["vs"]):.3f}; '
                                         f'per-lane member halting count at ticks: mean error {err.mean():+.3f}, MAE {np.abs(err).mean():.3f}, '
                                         f'share exact {np.mean(err == 0):.3f} (n {len(err)}); member-seconds [twin moving & real moving, twin moving & real halted, twin halted & real '
                                         f'moving, both halted] = {st["cm"]}', flush=True); return True
    ok = st['bad'] == 0 and st['act'] == 0
    print(f'KW20-{"1" if mode == "obs" else "2"} k{k} family {W.CUR["fam"]} obs {kind}: compared {st["n"]}, obs mismatches {st["bad"]}, action mismatches '
          f'{st["act"]} of {st["dec"]}; first mismatch {st["first"]}', flush=True)
    return ok


if __name__ == '__main__':
    ok = main(sys.argv[1], int(sys.argv[2])); print('PASS' if ok else 'FAIL'); sys.exit(0 if ok else 1)
