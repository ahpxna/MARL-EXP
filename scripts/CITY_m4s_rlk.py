#!/usr/bin/env python3
"""M4 stage 3 runner (PROTOCOL_CITY_M4_ARTERIAL_20261004 Amendment M4-A5): the spider patches of CITY_m4s_run (Q7.NET_S = NET_A = spider,
Q7.ROU = demand/spider/p2.0) plus a call-time patch of CITY_eval4.build_light: spec RLK:<checkpoint> -> CITY_lightk.LightRLK(NetInfoK(Q7.NET_S),
Q7.load_policy(checkpoint)); every other spec is unchanged.  The target must reach E4 as an imported module (CITY_eval6_m2, CITY_eval4_sigma);
CITY_eval4.py itself re-executes as __main__ and would bypass the patch, so it is refused.  Usage: CITY_m4s_rlk.py scripts/<x>.py <args>"""
import hashlib, runpy, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_m4s_run  # noqa: E402,F401  (spider patches)
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_eval4 as E4  # noqa: E402
from scripts.CITY_lightk import NetInfoK, LightRLK  # noqa: E402
E4.SRC = f"{E4.SRC}+m4s_rlk:{hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}"
_bl = E4.build_light


def build_light(spec, info, adapter, box):
    if spec.startswith('RLK:'):
        return Q7.NET_S, LightRLK(NetInfoK(Q7.NET_S), Q7.load_policy(spec[4:])), [], None
    return _bl(spec, info, adapter, box)


E4.build_light = build_light
if __name__ == '__main__':
    target = sys.argv[1]
    if Path(target).name == 'CITY_eval4.py':
        sys.exit('CITY_eval4.py re-executes as __main__ and bypasses the RLK patch: use CITY_eval6_m2 (L-ACT:0 --guard always) for OFF')
    sys.argv = [target] + sys.argv[2:]; runpy.run_path(str(ROOT / target), run_name='__main__')
