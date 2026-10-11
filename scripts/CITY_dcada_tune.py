#!/usr/bin/env python3
"""Job 070 of research/city_sim/PROTOCOL_CITY_WAVE2_JOBS_20261004.md (04/10/2026 wake 3): the DC-Ada comparator for input adaptation at a
FROZEN learned light (cell A-F (i)).  Port of the accept/reject random search with common random numbers of DC-Ada (Alqithami, IEEE
Access 2026, DOI 10.1109/ACCESS.2026.3687163; MIT code github.com/alqithami/DC-ADA src/agents/methods.py, read 04/10): every round, one
baseline rollout and M Gaussian candidates theta + sigma*eps under the SAME traffic seed (CRN); the best candidate is accepted iff it improves
the return by more than tau.  Here theta = (s, b) of the affine transform o' = o*exp(s) + b on the light's 7 inputs (CITY_eval2 --light-obs
affine:FILE), return = -city time loss of one 3600 s rollout on a TRAINING demand seed (0-7, never SELECT/TEST), the fleet being the
deployed one (F1).  Budget = rounds * (1 + M) rollouts, recorded.  No constraint on F0 (as published); F0's effect is evaluated afterwards."""
from __future__ import annotations
import argparse, json, os, sys, tempfile, time
from pathlib import Path
from types import SimpleNamespace
import numpy as np

ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_eval2 as E  # noqa: E402


def rollout(light, fleet, theta, seed, tmp):
    p = Path(tmp) / f'affine_{os.getpid()}.json'; p.write_text(json.dumps(dict(s=theta[:7].tolist(), b=theta[7:].tolist())))
    a = SimpleNamespace(light=light, light_obs=f'affine:{p}', light_fallback='none', fleet=fleet, guard='none', record=None, replay=None,
                        discharge=False, swap_at=None, swap_light=None, swap_fleet=None)
    return -E.run(a, seed, 3600)['timeloss']


def main(a):
    if os.environ.get('PYTHONHASHSEED') != '0':
        sys.exit('run with PYTHONHASHSEED=0')
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True); fn = out / f'{a.name}.json'
    if fn.exists():
        print('skip', a.name); return
    rng = np.random.default_rng(a.rng); theta = np.zeros(14); tmp = tempfile.mkdtemp(dir=os.environ.get('XPLAY_TMP')); log = []; used = 0; t0 = time.perf_counter()
    for r in range(a.rounds):
        seed = r % 8                                                   # training demand seeds 0-7, cycled; CRN inside the round
        base = rollout(a.light, a.fleet, theta, seed, tmp); used += 1; best, best_eps = base, None
        for m in range(a.M):
            eps = rng.standard_normal(14); val = rollout(a.light, a.fleet, theta + a.sigma * eps, seed, tmp); used += 1
            if val > best:
                best, best_eps = val, eps
        acc = best_eps is not None and best - base > a.tau
        if acc:
            theta = theta + a.alpha * a.sigma * best_eps
        log.append(dict(round=r, seed=seed, base=base, best=best, accepted=bool(acc), used=used, wall=time.perf_counter() - t0))
        print(f'[{time.perf_counter() - t0:.0f}s] {a.name} round {r} seed {seed} base TL {-base:.2f} best {-best:.2f} accepted {acc}', flush=True)
    fn.write_text(json.dumps(dict(s=theta[:7].tolist(), b=theta[7:].tolist(), light=a.light, fleet=a.fleet, rounds=a.rounds, M=a.M, sigma=a.sigma, tau=a.tau,
                                  alpha=a.alpha, rollouts=used, rollout_seconds=3600, log=log, source_sha256=__import__('hashlib').sha256(Path(__file__).read_bytes()).hexdigest()), indent=1))
    print('saved', fn, 'rollouts', used, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--light', required=True); p.add_argument('--fleet', required=True); p.add_argument('--name', required=True); p.add_argument('--out', required=True)
    p.add_argument('--rounds', type=int, default=8); p.add_argument('--M', type=int, default=4); p.add_argument('--sigma', type=float, default=0.1)
    p.add_argument('--tau', type=float, default=0.2); p.add_argument('--alpha', type=float, default=1.0); p.add_argument('--rng', type=int, default=0)
    main(p.parse_args())
