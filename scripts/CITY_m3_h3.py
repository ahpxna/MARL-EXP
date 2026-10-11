#!/usr/bin/env python3
"""M3-H3 continuation opportunity check (PROTOCOL_CITY_M3_H3_OPPORTUNITY_20261004).  CITY_eval_m3p (unchanged, imported: fleet SPaT = the light's
spat(); violation sidecar) with the light spec
  ONE:<k>:scan                       RL-H:k, no SPaT anywhere; logs every decision tick t in [600, 3000]: (t, light, RL-H action, Q-gap,
                                     receiver-eligible, fleet vehicles within 200 m)
  ONE:<k>:<opt>:<t*>:<light>         RL-H:k, no SPaT except ONE intervention at decision tick (t*, light): opt in I0 PLACEBO Z H5 H10 H15 P
Every branch re-simulates the full episode (same seed, same policies), so the prefix to t* is identical (KH-3: phase-trace hash to t*).
Outputs per run: <tag>.json (E4 rows), <tag>_m3p.json (violations), <tag>_h3.json (scan list or the intervention log, prefix hash), and
<tag>_veh.npz (per-vehicle tripinfo: id, agent flag, fuel, time loss, finished) for the local outcomes.  Usage as CITY_eval_m3p.py."""
import hashlib, json, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_eval_m3p as P  # noqa: E402
import scripts.CITY_m3p_rpc2 as RPC2  # noqa: E402
import scripts.CITY_env as CE  # noqa: E402
from scripts.CITY_env import DT_L, MIN_G  # noqa: E402
import torch  # noqa: E402
W, E4, X2 = P.W, P.E4, P.X2; E4.SRC = f"{E4.SRC}+m3h3:{hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}"
OUT = {}; VEH = {}; H_OF = {'H5': 5.0, 'H10': 10.0, 'H15': 15.0}


class LightOne(RPC2.LightRPC2):
    def __init__(self, info, qnet, k, mode, t_star=None, j=None):
        super().__init__(info, qnet, 'none', None, seed=int(k), forced=True, keep=True); self.mode, self.t_star, self.j = mode, t_star, j
        self.scan = []; self.done = None; self.hph = hashlib.sha256()

    def step(self, t):
        ls = CE.ls
        if self.t_star is not None and t <= self.t_star:              # KH-3 prefix hash (phases of every light, each second, up to t*)
            self.hph.update(np.array([ls.trafficlight.getPhase(x) for x in self.ids], np.int16).tobytes())
        if self.mode == 'scan' or int(t) % DT_L or (self.t_star is not None and int(t) != self.t_star):
            if self.mode == 'scan' and int(t) % DT_L == 0 and 600 <= t <= 3000:
                self._scan(t)
            return super().step(t)
        return self._intervene(t)

    def _scan(self, t):
        ls = CE.ls; O, todo = [], []
        for tid in self.ids:
            o, cur = self._obs(tid)
            if cur < 0 or tid in self.pending or ls.trafficlight.getSpentDuration(tid) < MIN_G:
                continue
            todo.append((tid, cur, o)); O.append(o)
        if not todo:
            return
        Q = self._q(np.stack(O)).numpy()
        for (tid, cur, o), q in zip(todo, Q):
            g = self.info.tls[tid]['greens'][cur]; hD = self.h_D(o); el = bool(self._eligible_receiver(tid, g, hD)) if self.fleet is not None else False
            near = 0
            for v in list(getattr(self.fleet, 'agents', ())):
                try:
                    nt = ls.vehicle.getNextTLS(v); near += bool(nt and nt[0][0] == tid and nt[0][2] <= 200)
                except Exception:
                    pass
            self.scan.append((float(t), tid, int(q[1] > q[0]), float(q[1] - q[0]), el, near, float(hD)))

    def _intervene(self, t):
        """the parent's step for this tick, with the option applied to light j (only if j is deciding now)."""
        ls = CE.ls; d = self.info.tls.get(self.j); o, cur = self._obs(self.j)
        deciding = cur >= 0 and self.j not in self.pending and ls.trafficlight.getSpentDuration(self.j) >= MIN_G
        if not deciding or self.mode in ('I0', 'PLACEBO'):
            if self.mode == 'PLACEBO' and deciding:
                self.h_D(o)                                            # exercise the same code path, no effect
            self.done = dict(deciding=deciding, mode=self.mode); return super().step(t)
        a = int(self._q(o[None]).numpy()[0].argmax()); hD = self.h_D(o)
        mode = self.mode if self.mode != 'P' else ('Z' if a == 1 else 'HP')
        self.done = dict(deciding=True, mode=self.mode, applied=mode, rl_action=a, hD=hD)
        saved = self.ids; self.ids = [x for x in saved if x != self.j]
        super().step(t)                                                # every other light exactly as the base
        self.ids = saved
        if mode == 'Z':
            self.log['commits'].append((self.j, float(t), float(t))); ls.trafficlight.setPhase(self.j, (d['greens'][cur] + 1) % d['n_phases'])
            self.onset[self.j] = (float(t) + RPC2.YELLOW + RPC2.OBS, d['greens'][(cur + 1) % len(d['greens'])])
        else:
            h = H_OF.get(mode, min(max(hD, RPC2.H_MIN), RPC2.H_MAX)); Tc = float(t + h)
            self.pending[self.j] = Tc; self.log['commits'].append((self.j, float(t), Tc)); ls.trafficlight.setPhaseDuration(self.j, 1e5)


_bl = E4.build_light


def build_light(spec, info, adapter, box):
    if spec.startswith('ONE:'):
        parts = spec.split(':'); k = parts[1]; _n, ck, _m = X2.light_spec(f'RL-H:{k}'); q = torch.load(ck, weights_only=False)['net']; q.eval()
        L = LightOne(info, q, k, 'scan') if parts[2] == 'scan' else LightOne(info, q, k, parts[2], int(parts[3]), parts[4])
        W.CUR.update(light=L); return W.Q7.NET_S, L, [], None
    return _bl(spec, info, adapter, box)


E4.build_light = build_light
_rt = E4.read_tripinfo


def read_tripinfo(ti):
    rows = _rt(ti); VEH['rows'] = rows; return rows


E4.read_tripinfo = read_tripinfo
_run = E4.run


def run(a, seed, end):
    out = _run(a, seed, end); L = W.CUR.get('light'); c = W.CUR.get('cars'); rows = VEH.get('rows', [])
    if isinstance(L, LightOne):
        OUT[str(seed)] = dict(scan=L.scan) if L.mode == 'scan' else dict(done=L.done, prefix_hash=L.hph.hexdigest(), t_star=L.t_star, light=L.j)
        if L.mode != 'scan':
            isa = (lambda v: c.is_agent(v)) if c is not None else (lambda v: False)
            VEH[str(seed)] = dict(ids=np.array([r['id'] for r in rows]), agent=np.array([isa(r['id']) for r in rows]), fuel=np.array([r['fuel'] for r in rows], float),
                                  tl=np.array([r['timeloss'] for r in rows], float), fin=np.array([r['finished'] for r in rows]))
    return out


E4.run = run
if __name__ == '__main__':
    import argparse
    p = argparse.ArgumentParser()
    p.add_argument('--light', default='ACT'); p.add_argument('--light-obs', default='raw'); p.add_argument('--light-fallback', default='none')
    p.add_argument('--fleet', default='human'); p.add_argument('--guard', default='none')
    p.add_argument('--record'); p.add_argument('--replay'); p.add_argument('--replay-dir'); p.add_argument('--discharge', action='store_true'); p.add_argument('--delay-trace', action='store_true')
    p.add_argument('--swap-at', type=float); p.add_argument('--swap-light'); p.add_argument('--swap-fleet')
    p.add_argument('--seeds', type=int, nargs='+', default=[0]); p.add_argument('--smoke', action='store_true')
    p.add_argument('--tag'); p.add_argument('--out', required=True)
    a = p.parse_args(); E4.main(a)
    Path(a.out, f'{a.tag}_m3p.json').write_text(json.dumps(dict(light=a.light, per_seed=P.SIDE)))
    Path(a.out, f'{a.tag}_h3.json').write_text(json.dumps(dict(light=a.light, per_seed=OUT)))
    for s, v in VEH.items():
        if s != 'rows':
            np.savez_compressed(Path(a.out, f'{a.tag}_veh_s{s}.npz'), **v)
