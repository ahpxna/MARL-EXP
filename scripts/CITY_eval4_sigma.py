#!/usr/bin/env python3
"""CITY_eval4 with the agent cars driven by SUMO at driver imperfection SIGMA (PROTOCOL_CITY_B6 §B6-S, 04/10/2026 wake 8): the σ-family of
NON-LEARNED comparators (σ = 0.5 is always-SUMO, σ = 0 is Z-sig0 / CITY_eval4_sig0).  Same membership (_stable_u), --guard always (SUMO
drives every agent decision), vehicle.setImperfection(v, SIGMA) at departure.  CITY_eval4 is not edited; source_sha256 records
'<eval4 sha>+sigma<S>:<wrapper sha>'.  Usage: CITY_eval4_sigma.py --sigma S <eval4 arguments>."""
import argparse, hashlib, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_eval4 as E4  # noqa: E402

pre = argparse.ArgumentParser(add_help=False); pre.add_argument('--sigma', type=float, required=True)
A0, REST = pre.parse_known_args()
E4.SRC = f"{E4.SRC}+sigma{A0.sigma}:{hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}"
_orig = E4.CarRLG.step; N = dict(set=0)


def step(self, t):
    ls = E4.CE.ls
    for v in ls.simulation.getDepartedIDList():
        if self.is_agent(v):
            ls.vehicle.setImperfection(v, A0.sigma); N['set'] += 1
    _orig(self, t)


E4.CarRLG.step = step

if __name__ == '__main__':
    if '--guard' not in REST or REST[REST.index('--guard') + 1] != 'always':
        sys.exit('the sigma family is defined with --guard always')
    p = argparse.ArgumentParser()
    p.add_argument('--light', default='ACT'); p.add_argument('--light-obs', default='raw'); p.add_argument('--light-fallback', default='none')
    p.add_argument('--fleet', default='human'); p.add_argument('--guard', default='none')
    p.add_argument('--record'); p.add_argument('--replay'); p.add_argument('--replay-dir'); p.add_argument('--discharge', action='store_true'); p.add_argument('--delay-trace', action='store_true')
    p.add_argument('--swap-at', type=float); p.add_argument('--swap-light'); p.add_argument('--swap-fleet')
    p.add_argument('--seeds', type=int, nargs='+', default=[100, 101, 102, 103, 104]); p.add_argument('--smoke', action='store_true')
    p.add_argument('--tag'); p.add_argument('--out', required=True)
    E4.main(p.parse_args(REST)); print('setImperfection calls', N['set'], 'sigma', A0.sigma, flush=True)
