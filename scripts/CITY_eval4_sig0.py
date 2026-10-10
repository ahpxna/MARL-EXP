#!/usr/bin/env python3
"""CITY_eval4 with a NON-LEARNED comparator fleet (PROTOCOL_CITY_B6 §B6-Z, Z-4; 04/10/2026 wake 8): the agent vehicles (same membership,
_stable_u(seed, vid) < rho) are driven by SUMO's own driver model with the driver IMPERFECTION removed (vehicle.setImperfection(v, 0)
at departure; Krauss sigma 0.5 -> 0).  Use with --fleet L-ACT:0 --guard always, so SUMO drives every agent decision exactly as in
always-SUMO; the only change is sigma.  CITY_eval4 itself is not edited; this wrapper patches CarRLG.step and records its own hash in
source_sha256 ('<eval4 sha>+sig0:<wrapper sha>').  Question it answers: is a learned fleet's time gain over SUMO more than what a
perfect (sigma = 0) SUMO driver already gets?"""
import hashlib, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_eval4 as E4  # noqa: E402

E4.SRC = f"{E4.SRC}+sig0:{hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}"
_orig = E4.CarRLG.step
SIG0 = dict(set=0)


def step(self, t):
    ls = E4.CE.ls
    for v in ls.simulation.getDepartedIDList():
        if self.is_agent(v):
            ls.vehicle.setImperfection(v, 0.0); SIG0['set'] += 1
    _orig(self, t)


E4.CarRLG.step = step

if __name__ == '__main__':
    import runpy
    if '--guard' not in sys.argv or sys.argv[sys.argv.index('--guard') + 1] != 'always':
        sys.exit('Z-4 is defined with --guard always (SUMO drives every agent decision)')
    sys.argv[0] = str(Path(E4.__file__))
    E4_ns = vars(E4)
    import argparse
    p = argparse.ArgumentParser()
    p.add_argument('--light', default='ACT'); p.add_argument('--light-obs', default='raw'); p.add_argument('--light-fallback', default='none')
    p.add_argument('--fleet', default='human'); p.add_argument('--guard', default='none')
    p.add_argument('--record'); p.add_argument('--replay'); p.add_argument('--replay-dir'); p.add_argument('--discharge', action='store_true'); p.add_argument('--delay-trace', action='store_true')
    p.add_argument('--swap-at', type=float); p.add_argument('--swap-light'); p.add_argument('--swap-fleet')
    p.add_argument('--seeds', type=int, nargs='+', default=[100, 101, 102, 103, 104]); p.add_argument('--smoke', action='store_true')
    p.add_argument('--tag'); p.add_argument('--out', required=True)
    E4.main(p.parse_args()); print('setImperfection calls', SIG0['set'], flush=True)
