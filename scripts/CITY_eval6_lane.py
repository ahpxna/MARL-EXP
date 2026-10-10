#!/usr/bin/env python3
"""CITY_eval6 plus the R8 lane-aware GLOSA fleets (Amendment R8, 04/10/2026).  CITY_eval4 / CITY_eval6 are not edited; this wrapper patches
load_fleet for new specs and records '<eval6 src>+lane:<wrapper sha>' in source_sha256:
  --fleet GLOSAL:<base>    theta0 GLOSA with lane-aware release; <base> = 0.3 (σ* base driver) or 0.5 (SUMO default, no setImperfection)
  --fleet GLOSAL0:<base>   the same class with the lane condition OFF (identity check KL: == GLOSA∘σ* / GLOSA)"""
import argparse, hashlib, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_eval4 as E4  # noqa: E402
import scripts.CITY_eval6 as E6  # noqa: E402,F401  (patches E4.load_fleet for the eval6 specs)
import scripts.CITY_glosa_lane as GL  # noqa: E402

E4.SRC = f"{E4.SRC}+lane:{hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}"
_lf = E4.load_fleet


def load_fleet(spec, seed, guard):
    for key, aware in (('GLOSAL0:', False), ('GLOSAL:', True)):
        if spec.startswith(key):
            base = float(spec[len(key):])
            return GL.CarGlosaL(E4.Q7.RHO, seed, lane_aware=aware, base_sigma=None if base == 0.5 else base), spec
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
