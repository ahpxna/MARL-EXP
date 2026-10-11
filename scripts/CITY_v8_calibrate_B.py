#!/usr/bin/env python3
"""Reward-B calibration (PROTOCOL_CITY_SPAT_PILOT_20261004 Amendment R2, rule frozen before this run): FT, training traffic 0-7 only,
policies always-SUMO (no control), sigma0.3 (SUMO, imperfection 0.3 on the agent cars) and random (agents in the 200 m zone get
setSpeed(clip(v + U(LO, HI), 0, v_allowed)) every second).  Logs per phase interval: R1-R4 shares, reward distribution, capped share,
f / v / s quantiles, empty intervals.  Degeneracy rule (frozen): under the random policy one branch >= 99 % of non-empty intervals, or
every branch but one at 0 % -> B is NOT trained this round.  Usage: CITY_v8_calibrate_B.py POLICY SEED OUT_JSON"""
import json, os, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_fleet_v8 as V8  # noqa: E402


class Runner:
    def __init__(self, policy, seed):
        self.policy, self.seed = policy, seed; self.stats = {k: 0 for k in ('capped', 'b_invalid', 'b_empty', 'b_R1', 'b_R2', 'b_R3', 'b_R4')}
        self.tr = None; self.rng = np.random.default_rng(seed + 17)

    def step(self, t):
        ls = CE.ls
        if self.tr is None:
            self.tr = V8.PhaseRewardB(self.stats)
        self.tr.step(t)
        for v in ls.simulation.getDepartedIDList():
            if V8._stable_u(self.seed, v) < Q7.RHO and self.policy == 'sigma0.3':
                ls.vehicle.setImperfection(v, 0.3)
        if self.policy == 'random':
            for v in ls.vehicle.getIDList():
                if V8._stable_u(self.seed, v) >= Q7.RHO:
                    continue
                try:
                    nt = ls.vehicle.getNextTLS(v)
                    if not nt or nt[0][2] > V8.ZONE:
                        ls.vehicle.setSpeed(v, -1); continue
                    sp = ls.vehicle.getSpeed(v); vl = ls.vehicle.getAllowedSpeed(v)
                    if V8.ok(sp) and V8.ok(vl):
                        ls.vehicle.setSpeed(v, float(min(max(sp + self.rng.uniform(V8.LO, V8.HI), 0.0), vl)))
                except Exception:
                    continue


if __name__ == '__main__':
    assert os.environ.get('PYTHONHASHSEED') == '0'
    pol, seed, out = sys.argv[1], int(sys.argv[2]), Path(sys.argv[3])
    r = Runner(pol, seed); m = CE.run_episode(Q7.NET_S, Q7.ROU.format(seed), seed, None, r, end=3600)
    L = r.tr.log; f = np.array([x[3] for x in L]); v = np.array([x[4] for x in L]); s = np.array([x[5] for x in L]); rew = np.array([x[7] for x in L])
    q = lambda a: [float(np.quantile(a, p)) for p in (0, 0.05, 0.5, 0.95, 0.99, 1)] if len(a) else []
    res = dict(policy=pol, seed=seed, n_intervals=len(L), stats=r.stats, teleports=m['teleports'], f_q=q(f), v_q=q(v), s_q=q(s), r_q=q(rew),
               branch={b: int(sum(x[8] == b for x in L)) for b in ('R1', 'R2', 'R3', 'R4')}, start_stop=int(sum(x[6] for x in L)),
               source_sha256=__import__('hashlib').sha256(Path(__file__).read_bytes()).hexdigest(), v8_sha256=__import__('hashlib').sha256(Path(V8.__file__).read_bytes()).hexdigest())
    out.parent.mkdir(parents=True, exist_ok=True); out.write_text(json.dumps(res, indent=1)); print(pol, seed, res['branch'], 'f max %.5f' % (f.max() if len(f) else -1), 'r q', [round(x, 2) for x in res['r_q']])
