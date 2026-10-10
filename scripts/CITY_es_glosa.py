#!/usr/bin/env python3
"""R6 (04/10/2026; PROTOCOL_CITY_SPAT_PILOT_20261004 Amendment R6): a LEARNED fleet by derivative-free policy search on the DEPLOYMENT
objective, over a 3-parameter GLOSA controller (same SPaT feature; release to SUMO outside the active region or on green):
    theta = (b, v_lo, d_act):  own movement not green, SPaT valid, ttg > 0, distance <= d_act  ->  v = clip(d / (ttg + b), v_lo, v_allowed)
                               otherwise                                                      ->  release (SUMO drives)
    b in [0, 6] s (arrival buffer after green onset), v_lo in [0, 8] m/s (no crawling below it), d_act in [30, 200] m.
    theta0 = (0, 0, 200) is the simple heuristic GLOSA.
Objective on TRAIN traffic (FT), common random numbers (the same traffic seeds for every candidate in an iteration):
    J(theta) = agent fuel % vs always-SUMO  +  PEN * [max(0, dTL_agent - 0.0) + max(0, dTL_human - 0.0)]   (s/veh, PEN = 5 %/s)
  i.e. fuel is primary; time-loss increases over always-SUMO are penalised (the registered margins are +0.5 on SELECT; training uses 0).
Search: (1) 24 Latin-hypercube candidates on traffic seeds {0, 1, 2, 3}; (2) 12 iterations of (1+4) local search (Gaussian steps, 15 % of
the range, accept if J improves on fresh seeds {4..7} averaged with {0..3}); the search seed sets the sampler.  Output: best theta + log.
Usage: CITY_es_glosa.py search SEED OUT_JSON ; CITY_es_glosa.py fleet THETA_JSON (prints nothing; used by eval6 spec ES:<json>)"""
import json, os, sys, tempfile, argparse
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_fleet_v8 as V8  # noqa: E402
from scripts.CITY_spat_feature import spat  # noqa: E402

LO_B, HI_B = np.array([0.0, 0.0, 30.0]), np.array([6.0, 8.0, 200.0]); PEN = 5.0


class CarESGlosa(V8.CarGLOSA):
    def __init__(self, rho, seed, theta):
        super().__init__(rho, seed); self.b, self.vlo, self.dact = (float(x) for x in theta)

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
                if not nt or nt[0][2] > V8.ZONE:
                    ls.vehicle.setSpeed(v, -1); continue
                tid, link, dist, st = nt[0]; s = spat(tid, link); self.decisions += 1
                if st not in 'Gg' and s['valid'] and s['ttg'] > 0 and dist <= self.dact:
                    vl = ls.vehicle.getAllowedSpeed(v); ls.vehicle.setSpeed(v, float(min(vl, max(self.vlo, dist / (s['ttg'] + self.b))))); self.fired += 1
                else:
                    ls.vehicle.setSpeed(v, -1)
            except Exception:
                continue


def episode(fleet_fn, seed):
    """One FT episode, 5400 s; returns (agent fuel mean, agent TL mean, human TL mean, teleports)."""
    cars = fleet_fn(seed) if fleet_fn else None
    track = cars if cars is not None else V8.CarGLOSA(Q7.RHO, seed)            # membership only, when no fleet (always-SUMO)
    if cars is None:
        track.step = lambda t: [track.agents.add(v) for v in CE.ls.simulation.getDepartedIDList() if track.is_agent(v)]
    fd, ti = tempfile.mkstemp(suffix='.xml', dir=os.environ.get('XPLAY_TMP')); os.close(fd)
    m = CE.run_episode(Q7.NET_S, Q7.ROU.format(seed), seed, None, track, end=5400, tripinfo=ti)
    rows = CE.read_tripinfo(ti); os.remove(ti); isa = lambda v: V8._stable_u(seed, v) < Q7.RHO
    ag = [r for r in rows if isa(r['id'])]; hu = [r for r in rows if not isa(r['id'])]
    return float(np.mean([r['fuel'] for r in ag])), float(np.mean([r['timeloss'] for r in ag])), float(np.mean([r['timeloss'] for r in hu])), m['teleports']


BASE = {}


def J(theta, seeds):
    vals = []
    for s in seeds:
        if s not in BASE:
            BASE[s] = episode(None, s)
        f, ta, th, tel = episode(lambda sd: CarESGlosa(Q7.RHO, sd, theta), s); f0, ta0, th0, _ = BASE[s]
        vals.append(100 * (f / f0 - 1) + PEN * (max(0.0, ta - ta0) + max(0.0, th - th0)))
    return float(np.mean(vals))


def search(seed, out):
    rng = np.random.default_rng(seed); A, B = [0, 1, 2, 3], [4, 5, 6, 7]; log = []
    lhs = (np.stack([rng.permutation(24) for _ in range(3)], 1) + rng.random((24, 3))) / 24; cands = LO_B + lhs * (HI_B - LO_B)
    cands[0] = np.array([0.0, 0.0, 200.0])                                    # include the untuned heuristic
    scores = [J(c, A) for c in cands]; k = int(np.argmin(scores)); best, bj = cands[k], scores[k]
    log.append(dict(stage='lhs', cands=cands.tolist(), J=scores)); print(f'seed {seed} LHS best {best.round(2)} J {bj:.3f} (heuristic J {scores[0]:.3f})', flush=True)
    bj_full = 0.5 * (bj + J(best, B))
    for it in range(12):
        props = [np.clip(best + rng.normal(0, 0.15, 3) * (HI_B - LO_B), LO_B, HI_B) for _ in range(4)]
        ps = [0.5 * (J(p, A) + J(p, B)) for p in props]; j = int(np.argmin(ps))
        acc = ps[j] < bj_full
        if acc:
            best, bj_full = props[j], ps[j]
        log.append(dict(stage='local', it=it, props=[p.tolist() for p in props], J=ps, accepted=bool(acc), best=best.tolist(), J_best=bj_full))
        print(f'seed {seed} it {it} best {best.round(2)} J {bj_full:.3f} {"accepted" if acc else ""}', flush=True)
    Path(out).write_text(json.dumps(dict(theta=best.tolist(), J=bj_full, seed=seed, log=log, pen=PEN, bounds=[LO_B.tolist(), HI_B.tolist()],
                                         source_sha256=__import__('hashlib').sha256(Path(__file__).read_bytes()).hexdigest()), indent=1))


if __name__ == '__main__':
    assert os.environ.get('PYTHONHASHSEED') == '0'
    if sys.argv[1] == 'search':
        search(int(sys.argv[2]), sys.argv[3])
