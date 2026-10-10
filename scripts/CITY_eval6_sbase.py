#!/usr/bin/env python3
"""CITY_eval6 with the agent cars' BASE DRIVER at imperfection BASE_SIGMA (Amendment R7, 04/10/2026): any eval6 / eval4 fleet spec, plus
vehicle.setImperfection(v, BASE_SIGMA) for every agent car at departure (the σ-family mechanism of CITY_eval4_sigma), applied before the
fleet's own step.  The fleet still commands speeds where it does; released cars are driven by SUMO Krauss at BASE_SIGMA instead of the
default 0.5.  CITY_eval4 / CITY_eval6 are not edited; source_sha256 records '<eval6 src>+sbase<S>:<wrapper sha>'.
Usage: CITY_eval6_sbase.py --base-sigma S <eval6 arguments>."""
import argparse, hashlib, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_eval4 as E4  # noqa: E402
import scripts.CITY_eval6 as E6  # noqa: E402,F401  (patches E4.load_fleet for the eval6 specs)

pre = argparse.ArgumentParser(add_help=False); pre.add_argument('--base-sigma', type=float, required=True)
A0, REST = pre.parse_known_args()
SIG = A0.base_sigma
E4.SRC = f"{E4.SRC}+sbase{SIG}:{hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}"
_lf = E4.load_fleet; N = dict(set=0)


def wrap(cars):
    inner = cars.step

    def step(t):
        ls = E4.CE.ls
        for v in ls.simulation.getDepartedIDList():
            if cars.is_agent(v):
                ls.vehicle.setImperfection(v, SIG); N['set'] += 1
        inner(t)
    cars.step = step
    return cars


def load_fleet(spec, seed, guard):
    cars, fp = _lf(spec, seed, guard)
    if cars is None:
        raise SystemExit('sbase needs a fleet object (agent membership); use the σ-family wrapper for SUMO-only fleets')
    return wrap(cars), fp


E4.load_fleet = load_fleet

if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--light', default='ACT'); p.add_argument('--light-obs', default='raw'); p.add_argument('--light-fallback', default='none')
    p.add_argument('--fleet', default='human'); p.add_argument('--guard', default='none')
    p.add_argument('--record'); p.add_argument('--replay'); p.add_argument('--replay-dir'); p.add_argument('--discharge', action='store_true'); p.add_argument('--delay-trace', action='store_true')
    p.add_argument('--swap-at', type=float); p.add_argument('--swap-light'); p.add_argument('--swap-fleet')
    p.add_argument('--seeds', type=int, nargs='+', default=[100, 101, 102, 103, 104]); p.add_argument('--smoke', action='store_true')
    p.add_argument('--tag'); p.add_argument('--out', required=True)
    E4.main(p.parse_args(REST)); print('setImperfection calls', N['set'], 'base sigma', SIG, flush=True)
