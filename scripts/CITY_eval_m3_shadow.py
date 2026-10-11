#!/usr/bin/env python3
"""M3 Addendum A2 (04/10/2026): CITY_eval_m3 (unchanged, imported) plus a SHADOW fleet spec
    --fleet SHADOW:<v11 fleet.pt>   the fleet's members drive as σ* (setImperfection 0.3 at departure; never commanded), but the object carries
                                    the R10 policy net and the member set, so an M3E light computes its tickets / weights / inputs exactly as in
                                    deployment (receiver sensitivity probed on the frozen R10 policy with the deployed provider).
Sidecar: as CITY_eval_m3, plus the mean raw ticket weights per type of the E light (to compare shadow vs fleet-driving runs).
Usage: CITY_eval_m3_shadow.py --spat-arm deployed --light M3E:<ckpt> --fleet SHADOW:<fleet.pt> ..."""
import hashlib, json, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_eval_m3 as W  # noqa: E402  (pre-parses --spat-arm; patches E4)
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_fleet_v8 as V8  # noqa: E402
import torch  # noqa: E402
E4 = W.E4; SIG = 0.3
E4.SRC = f"{E4.SRC}+shadow:{hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}"


class ShadowFleet:
    def __init__(self, net, rho, seed):
        self.net, self.rho, self.seed = net, rho, seed; self.agents = set(); self.fired = 0; self.decisions = 0; self.digest = hashlib.sha256()

    def is_agent(self, vid):
        return V8._stable_u(self.seed, vid) < self.rho

    def step(self, t):
        ls = CE.ls
        for v in ls.simulation.getDepartedIDList():
            if self.is_agent(v):
                self.agents.add(v); ls.vehicle.setImperfection(v, SIG)
        for v in ls.simulation.getArrivedIDList():
            self.agents.discard(v)


_lf = E4.load_fleet


def load_fleet(spec, seed, guard):
    if spec.startswith('SHADOW:'):
        d = torch.load(spec[7:], weights_only=False); net = d['net']; net.eval(); c = ShadowFleet(net, E4.Q7.RHO, seed)
        W.CUR['cars'] = c
        if W.CUR.get('light') is not None and hasattr(W.CUR['light'], 'fleet'):
            W.CUR['light'].fleet = c
        W.LOG.setdefault('cars', []).append(c); return c, spec
    return _lf(spec, seed, guard)


E4.load_fleet = load_fleet
_run = E4.run
WSUM = {}


def run(a, seed, end):
    out = _run(a, seed, end); L = W.CUR.get('light')
    if isinstance(L, W.M.LightE):
        for tk in L.tickets.T.values():
            for k in tk:
                for ty, v in k['w'].items():
                    s = WSUM.setdefault(ty, [0.0, 0]); s[0] += v; s[1] += 1
    return out


E4.run = run
if __name__ == '__main__':
    import argparse
    p = argparse.ArgumentParser()
    p.add_argument('--light', default='ACT'); p.add_argument('--light-obs', default='raw'); p.add_argument('--light-fallback', default='none')
    p.add_argument('--fleet', default='human'); p.add_argument('--guard', default='none')
    p.add_argument('--record'); p.add_argument('--replay'); p.add_argument('--replay-dir'); p.add_argument('--discharge', action='store_true'); p.add_argument('--delay-trace', action='store_true')
    p.add_argument('--swap-at', type=float); p.add_argument('--swap-light'); p.add_argument('--swap-fleet')
    p.add_argument('--seeds', type=int, nargs='+', default=[100, 101, 102, 103, 104]); p.add_argument('--smoke', action='store_true')
    p.add_argument('--tag'); p.add_argument('--out', required=True)
    a = p.parse_args(W.REST); E4.main(a)
    Path(a.out, f'{a.tag}_shadow.json').write_text(json.dumps(dict(light=a.light, fleet=a.fleet, w_mean={k: v[0] / max(1, v[1]) for k, v in WSUM.items()},
                                                                   n_tickets={k: v[1] for k, v in WSUM.items()})))
