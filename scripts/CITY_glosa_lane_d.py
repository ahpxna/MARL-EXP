#!/usr/bin/env python3
"""R9 (Amendment R9, 04/10/2026): GLOSA-LD∘σ*, a 4-parameter GLOSA with lane-aware release limited to the last d_lc metres, learned by the
R6 derivative-free search generalised to 4 dimensions, on TRAIN traffic, with J relative to the σ* fleet (as R7b):
    theta = (b, v_lo, d_act, d_lc): own movement not green, SPaT valid, ttg > 0, dist <= d_act, and (lane continues OR dist >= d_lc)
                                    -> v = clip(d / (ttg + b), v_lo, v_allowed);   otherwise release.  Base driver σ* = 0.3 for the agents.
    theta_L = (0, 0, 200, 200) is GLOSA-L∘σ* (CITY_glosa_lane, lane_aware); (0, 0, 200, 0) is GLOSA∘σ*.
CITY_glosa_lane / CITY_es_glosa / CITY_es_glosa_sbase are frozen and not edited.
Usage: CITY_glosa_lane_d.py search SEED OUT_JSON"""
import hashlib, json, os, sys, tempfile
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_fleet_v8 as V8  # noqa: E402
import scripts.CITY_glosa_lane as GL  # noqa: E402
import scripts.CITY_es_glosa_sbase as S  # noqa: E402
from scripts.CITY_spat_feature import spat  # noqa: E402

SIG = 0.3; PEN = 5.0
LO, HI = np.array([0.0, 0.0, 30.0, 0.0]), np.array([6.0, 8.0, 200.0, 200.0]); THETA_L = np.array([0.0, 0.0, 200.0, 200.0])


class CarGlosaLD(GL.CarGlosaL):
    def __init__(self, rho, seed, theta):
        super().__init__(rho, seed, theta[:3], lane_aware=True, base_sigma=SIG); self.dlc = float(theta[3])

    def step(self, t):
        ls = CE.ls
        for v in ls.simulation.getDepartedIDList():
            if self.is_agent(v):
                self.agents.add(v); ls.vehicle.setImperfection(v, SIG)
        for v in ls.simulation.getArrivedIDList():
            self.agents.discard(v)
        for v in list(self.agents):
            try:
                nt = ls.vehicle.getNextTLS(v)
                if not nt or nt[0][2] > V8.ZONE:
                    ls.vehicle.setSpeed(v, -1); continue
                tid, link, dist, st = nt[0]; s = spat(tid, link); self.decisions += 1
                if st not in 'Gg' and s['valid'] and s['ttg'] > 0 and dist <= self.dact:
                    if dist < self.dlc and not GL.lane_ok(ls, v):
                        ls.vehicle.setSpeed(v, -1); self.lane_released += 1; continue
                    vl = ls.vehicle.getAllowedSpeed(v); ls.vehicle.setSpeed(v, float(min(vl, max(self.vlo, dist / (s['ttg'] + self.b))))); self.fired += 1
                else:
                    ls.vehicle.setSpeed(v, -1)
            except Exception:
                continue


def episode(theta, seed):
    if theta is None:
        return S.episode_s(None, seed)                                # the σ* fleet (identical to the R7b baseline, K7-3)
    cars = CarGlosaLD(Q7.RHO, seed, theta)
    fd, ti = tempfile.mkstemp(suffix='.xml', dir=os.environ.get('XPLAY_TMP')); os.close(fd)
    m = CE.run_episode(Q7.NET_S, Q7.ROU.format(seed), seed, None, cars, end=5400, tripinfo=ti)
    rows = CE.read_tripinfo(ti); os.remove(ti); isa = lambda v: V8._stable_u(seed, v) < Q7.RHO
    ag = [r for r in rows if isa(r['id'])]; hu = [r for r in rows if not isa(r['id'])]
    return float(np.mean([r['fuel'] for r in ag])), float(np.mean([r['timeloss'] for r in ag])), float(np.mean([r['timeloss'] for r in hu])), m['teleports']


BASE = {}


def J(theta, seeds):
    vals = []
    for s in seeds:
        if s not in BASE:
            BASE[s] = episode(None, s)
        f, ta, th, _ = episode(theta, s); f0, ta0, th0, _ = BASE[s]
        vals.append(100 * (f / f0 - 1) + PEN * (max(0.0, ta - ta0) + max(0.0, th - th0)))
    return float(np.mean(vals))


def search(seed, out):
    """The R6 procedure (CITY_es_glosa.search) in 4 dimensions."""
    rng = np.random.default_rng(seed); A, B = [0, 1, 2, 3], [4, 5, 6, 7]; log = []; k = len(LO)
    lhs = (np.stack([rng.permutation(24) for _ in range(k)], 1) + rng.random((24, k))) / 24; cands = LO + lhs * (HI - LO); cands[0] = THETA_L
    scores = [J(c, A) for c in cands]; i = int(np.argmin(scores)); best, bj = cands[i], scores[i]
    log.append(dict(stage='lhs', cands=cands.tolist(), J=scores)); print(f'seed {seed} LHS best {best.round(2)} J {bj:.3f} (theta_L J {scores[0]:.3f})', flush=True)
    bj_full = 0.5 * (bj + J(best, B))
    for it in range(12):
        props = [np.clip(best + rng.normal(0, 0.15, k) * (HI - LO), LO, HI) for _ in range(4)]
        ps = [0.5 * (J(p, A) + J(p, B)) for p in props]; j = int(np.argmin(ps)); acc = ps[j] < bj_full
        if acc:
            best, bj_full = props[j], ps[j]
        log.append(dict(stage='local', it=it, props=[p.tolist() for p in props], J=ps, accepted=bool(acc), best=best.tolist(), J_best=bj_full))
        print(f'seed {seed} it {it} best {best.round(2)} J {bj_full:.3f} {"accepted" if acc else ""}', flush=True)
    Path(out).write_text(json.dumps(dict(theta=best.tolist(), J=bj_full, seed=seed, log=log, pen=PEN, bounds=[LO.tolist(), HI.tolist()], base_sigma=SIG,
                                         source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()), indent=1))


if __name__ == '__main__':
    assert os.environ.get('PYTHONHASHSEED') == '0'
    if sys.argv[1] == 'search':
        search(int(sys.argv[2]), sys.argv[3])
