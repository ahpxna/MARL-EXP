#!/usr/bin/env python3
"""CITY_eval6_lane2 plus the R10 fleet (Amendment R10, 04/10/2026): --fleet PL:<v11 *_fleet.pt> -> CITY_fleet_v11.CarPPOL, DETERMINISTIC
(u = mean), evaluation mode (no credit).  All eval6 / lane / lane2 specs remain.  No file is edited; source_sha256 records '+v11:<sha>'."""
import argparse, hashlib, sys
from pathlib import Path
import torch
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_eval4 as E4  # noqa: E402
import scripts.CITY_eval6_lane2 as EL2  # noqa: E402,F401  (eval6 + lane + lane2 specs)
import scripts.CITY_fleet_v11 as V11  # noqa: E402

E4.SRC = f"{E4.SRC}+v11:{hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}"
_lf = E4.load_fleet


def load_fleet(spec, seed, guard):
    if spec.startswith('PL:'):
        p = Path(spec[3:]); d = torch.load(p, weights_only=False); net = d['net']; net.eval()
        return V11.CarPPOL(net, E4.Q7.RHO, seed, deterministic=True, record=False), p
    return _lf(spec, seed, guard)


E4.load_fleet = load_fleet

if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--light', default='ACT'); p.add_argument('--light-obs', default='raw'); p.add_argument('--light-fallback', default='none')
    p.add_argument('--fleet', default='human'); p.add_argument('--guard', default='none')
    p.add_argument('--record'); p.add_argument('--replay'); p.add_argument('--replay-dir'); p.add_argument('--discharge', action='store_true'); p.add_argument('--delay-trace', action='store_true')
    p.add_argument('--swap-at', type=float); p.add_argument('--swap-light'); p.add_argument('--swap-fleet')
    p.add_argument('--seeds', type=int, nargs='+', default=[100, 101, 102, 103, 104]); p.add_argument('--smoke', action='store_true')
    p.add_argument('--tag'); p.add_argument('--out', required=True)
    E4.main(p.parse_args())
