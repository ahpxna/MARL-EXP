#!/usr/bin/env python3
"""F1-B runner (PROTOCOL_CITY_F1_SALTLAKE_20261008, Amendment A3): CITY_sl_run's Salt Lake patches plus a call-time patch of
CITY_eval4.build_light: spec RLW:<checkpoint> -> CITY_lightw.LightRLW(NetInfoK(Q7.NET_S), Q7.load_policy(checkpoint)); every other spec is
unchanged.  Usage: SL_SITE=<site> CITY_sl_runw.py scripts/<x>.py <args>"""
import hashlib, runpy, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_sl_run  # noqa: E402,F401
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_eval4 as E4  # noqa: E402
from scripts.CITY_lightk import NetInfoK  # noqa: E402
from scripts.CITY_lightw import LightRLW  # noqa: E402
E4.SRC = f"{E4.SRC}+sl_runw:{hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}"
_bl = E4.build_light


def build_light(spec, info, adapter, box):
    if spec.startswith('RLW:'):
        return Q7.NET_S, LightRLW(NetInfoK(Q7.NET_S), Q7.load_policy(spec[4:])), [], None
    return _bl(spec, info, adapter, box)


E4.build_light = build_light
if __name__ == '__main__':
    target = sys.argv[1]; sys.argv = [target] + sys.argv[2:]; runpy.run_path(str(ROOT / target), run_name='__main__')
