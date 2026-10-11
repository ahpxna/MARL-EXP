#!/usr/bin/env python3
"""F1-3 / F1-4 runner (PROTOCOL_CITY_F1_SALTLAKE_20261008, Amendment A5): CITY_sl_runw (Salt Lake patches, spec RLW:) plus
  * spec RLWQ:<checkpoint>:A:B -> CITY_lightw.LightRLWQ (the TSI adapter on all four greens' halting inputs);
  * SL_Q=<q> sets the published quantile of the n2k provider and its forecast-K branch (CITY_m4s_tsi_eval fixes 0.5);
  * the N2K forecaster generalised to four greens: scripts.CITY_n2k's KMAX, feat, build, make_provider, greens_of_net and parity are replaced
    by those of scripts.CITY_n2k4 BEFORE the target imports CITY_n2k (CITY_m4s_tsi_eval pads the feature log to NK.KMAX, so this also keeps
    the fourth green's counts).  No file is edited.  Usage: SL_SITE=<site> CITY_sl_runw4.py scripts/<x>.py <args>"""
import hashlib, runpy, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_sl_runw  # noqa: E402,F401
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_eval4 as E4  # noqa: E402
import scripts.CITY_n2k as NK  # noqa: E402
import scripts.CITY_n2k4 as NK4  # noqa: E402
from scripts.CITY_lightk import NetInfoK  # noqa: E402
from scripts.CITY_lightw import LightRLWQ  # noqa: E402
import os  # noqa: E402
import scripts.CITY_spat_forecast_k as FK  # noqa: E402
for _n in ('KMAX', 'feat', 'build', 'greens_of_net', 'parity', 'fit', 'cur_index', 'r_of'):
    setattr(NK, _n, getattr(NK4, _n))
SLQ = os.environ.get('SL_Q'); _mk = FK.make_spat_k                    # A5: the published quantile q (both branches) from SL_Q;
NK.make_provider = lambda mp, q, *a, **k: NK4.make_provider(mp, float(SLQ) if SLQ else q, *a, **k)   # CITY_m4s_tsi_eval fixes 0.5
FK.make_spat_k = lambda table, q, *a, **k: _mk(table, float(SLQ) if SLQ else q, *a, **k)
E4.SRC = f"{E4.SRC}+sl_runw4:{hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}"
_bl = E4.build_light


def build_light(spec, info, adapter, box):
    if spec.startswith('RLWQ:'):
        ck, A, B = spec[5:].rsplit(':', 2); return Q7.NET_S, LightRLWQ(NetInfoK(Q7.NET_S), Q7.load_policy(ck), float(A), float(B)), [], None
    return _bl(spec, info, adapter, box)


E4.build_light = build_light
if __name__ == '__main__':
    target = sys.argv[1]; sys.argv = [target] + sys.argv[2:]; runpy.run_path(str(ROOT / target), run_name='__main__')
