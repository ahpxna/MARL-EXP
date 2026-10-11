#!/usr/bin/env python3
"""CITY_eval6_lane plus the R9 learned fleet (Amendment R9, 04/10/2026): --fleet ESLD:<theta json> -> CarGlosaLD (σ* base).  All CITY_eval6 /
CITY_eval6_lane specs (GLOSAL:<base>, GLOSAL0:<base>, GLOSA, P:, R:, ES:, IC:GLOSA) remain available.  No file is edited; source_sha256
records '<eval6_lane src>+lane2:<wrapper sha>'."""
import argparse, hashlib, json, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_eval4 as E4  # noqa: E402
import scripts.CITY_eval6_lane as EL  # noqa: E402,F401  (patches E4.load_fleet: eval6 + lane specs)
import scripts.CITY_glosa_lane_d as LD  # noqa: E402

E4.SRC = f"{E4.SRC}+lane2:{hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}"
_lf = E4.load_fleet


def load_fleet(spec, seed, guard):
    if spec.startswith('ESLD:'):
        th = json.loads(Path(spec[5:]).read_text())['theta']
        return LD.CarGlosaLD(E4.Q7.RHO, seed, th), spec
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
