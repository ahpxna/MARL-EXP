#!/usr/bin/env python3
"""W14-3 (PROTOCOL_CITY_WAVE14_20261007, Amendment A1): publish the multi-green (N2K) forecast at quantile W14_Q instead of the 0.5 hard-coded
in CITY_m4s_tsi_eval (both the N2K network and its forecast-K table fallback, as the grid4 hybrid uses one q for both branches).  Patches
CITY_n2k.make_provider and CITY_spat_forecast_k.make_spat_k (no file is edited) before the target imports them; rows get w14_q.
Usage: W14_Q=0.1 CITY_w14_q.py <target script> <its args>"""
import os, runpy, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_n2k as NK  # noqa: E402
import scripts.CITY_spat_forecast_k as FK  # noqa: E402
import scripts.CITY_eval4 as E4  # noqa: E402
Q = float(os.environ['W14_Q']); _mp = NK.make_provider; _mk = FK.make_spat_k
NK.make_provider = lambda mp, q, *a, **k: _mp(mp, Q, *a, **k)  # noqa: E731
FK.make_spat_k = lambda tb, q, *a, **k: _mk(tb, Q, *a, **k)  # noqa: E731
_run = E4.run


def run(a, seed, end):
    out = _run(a, seed, end); out['w14_q'] = Q; return out


E4.run = run
E4.SRC = f"{getattr(E4, 'SRC', '')}+w14q:{Q}"
if __name__ == '__main__':
    target = sys.argv[1]; sys.argv = [target] + sys.argv[2:]
    runpy.run_path(str(ROOT / target), run_name='__main__')
