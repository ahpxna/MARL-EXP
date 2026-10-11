#!/usr/bin/env python3
"""R7b (Amendment R7, 04/10/2026): the R6 policy search (CITY_es_glosa.search, unchanged) with ONE change: every agent car's base driver is
SUMO Krauss at imperfection SIG = σ* = 0.3 (setImperfection at departure, the σ-family mechanism), and J is defined relative to the fleet's
own base driver, i.e. the σ* fleet:
    J(theta) = agent fuel % vs σ*  +  PEN * [max(0, dTL_agent vs σ*) + max(0, dTL_human vs σ*)]     (PEN = 5 %/(s/veh), as in R6)
CITY_es_glosa.py is frozen and not edited: this module rebinds ES.J and calls ES.search.
Usage: CITY_es_glosa_sbase.py search SEED OUT_JSON"""
import hashlib, json, os, sys, tempfile
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_fleet_v8 as V8  # noqa: E402
import scripts.CITY_es_glosa as ES  # noqa: E402

SIG = 0.3


class CarESGlosaS(ES.CarESGlosa):
    def step(self, t):
        for v in CE.ls.simulation.getDepartedIDList():
            if self.is_agent(v):
                CE.ls.vehicle.setImperfection(v, SIG)
        super().step(t)


def episode_s(theta, seed):
    """One FT episode, 5400 s, base driver σ* for the agents; theta None = the σ* fleet (SUMO drives every agent)."""
    if theta is None:
        cars = V8.CarGLOSA(Q7.RHO, seed)

        def st(t):
            for v in CE.ls.simulation.getDepartedIDList():
                if cars.is_agent(v):
                    cars.agents.add(v); CE.ls.vehicle.setImperfection(v, SIG)
        cars.step = st
    else:
        cars = CarESGlosaS(Q7.RHO, seed, theta)
    fd, ti = tempfile.mkstemp(suffix='.xml', dir=os.environ.get('XPLAY_TMP')); os.close(fd)
    m = CE.run_episode(Q7.NET_S, Q7.ROU.format(seed), seed, None, cars, end=5400, tripinfo=ti)
    rows = CE.read_tripinfo(ti); os.remove(ti); isa = lambda v: V8._stable_u(seed, v) < Q7.RHO
    ag = [r for r in rows if isa(r['id'])]; hu = [r for r in rows if not isa(r['id'])]
    return float(np.mean([r['fuel'] for r in ag])), float(np.mean([r['timeloss'] for r in ag])), float(np.mean([r['timeloss'] for r in hu])), m['teleports']


BASE_S = {}


def J_s(theta, seeds):
    vals = []
    for s in seeds:
        if s not in BASE_S:
            BASE_S[s] = episode_s(None, s)
        f, ta, th, _ = episode_s(theta, s); f0, ta0, th0, _ = BASE_S[s]
        vals.append(100 * (f / f0 - 1) + ES.PEN * (max(0.0, ta - ta0) + max(0.0, th - th0)))
    return float(np.mean(vals))


if __name__ == '__main__':
    assert os.environ.get('PYTHONHASHSEED') == '0'
    if sys.argv[1] == 'search':
        ES.J = J_s; out = sys.argv[3]; ES.search(int(sys.argv[2]), out)
        d = json.loads(Path(out).read_text()); d.update(base_sigma=SIG, objective='relative to the sigma* fleet (R7)',
                                                         sbase_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
        Path(out).write_text(json.dumps(d, indent=1))
    elif sys.argv[1] == 'J':                                   # smoke: J of a theta on given traffic seeds
        print(J_s(json.loads(sys.argv[2]), [int(x) for x in sys.argv[3:]]), flush=True)
