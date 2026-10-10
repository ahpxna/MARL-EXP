#!/usr/bin/env python3
"""CITY_eval4 on a ROUTE VARIANT (PROTOCOL_CITY_B6 §B6-AC, 04/10/2026 wake 9): Q7.ROU -> research/city_sim/demand/grid4_var/<V>/rou_s{}.xml.
CITY_eval4 is not edited; source_sha256 records '<eval4 sha>+route-<V>:<wrapper sha>'.  Usage: CITY_eval4_route.py --route-variant V <eval4 args>
(defined with --guard always: SUMO drives every agent decision with the variant's vType)."""
import argparse, hashlib, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_eval4 as E4  # noqa: E402

pre = argparse.ArgumentParser(add_help=False); pre.add_argument('--route-variant', required=True)
A0, REST = pre.parse_known_args()
E4.Q7.ROU = str(ROOT / 'research/city_sim/demand/grid4_var' / A0.route_variant / 'rou_s{}.xml')
E4.SRC = f"{E4.SRC}+route-{A0.route_variant}:{hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}"

if __name__ == '__main__':
    if '--guard' not in REST or REST[REST.index('--guard') + 1] != 'always':
        sys.exit('B6-AC is defined with --guard always')
    p = argparse.ArgumentParser()
    p.add_argument('--light', default='ACT'); p.add_argument('--light-obs', default='raw'); p.add_argument('--light-fallback', default='none')
    p.add_argument('--fleet', default='human'); p.add_argument('--guard', default='none')
    p.add_argument('--record'); p.add_argument('--replay'); p.add_argument('--replay-dir'); p.add_argument('--discharge', action='store_true'); p.add_argument('--delay-trace', action='store_true')
    p.add_argument('--swap-at', type=float); p.add_argument('--swap-light'); p.add_argument('--swap-fleet')
    p.add_argument('--seeds', type=int, nargs='+', default=[100, 101, 102, 103, 104]); p.add_argument('--smoke', action='store_true')
    p.add_argument('--tag'); p.add_argument('--out', required=True)
    E4.main(p.parse_args(REST)); print('route variant', A0.route_variant, E4.Q7.ROU, flush=True)
