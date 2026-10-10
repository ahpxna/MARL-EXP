#!/usr/bin/env python3
"""M3′ light-side cost with deployment-equivalent inputs: CITY_eval_m3p (RPC lights) + CITY_eval_m3_shadow (SHADOW fleet spec: the R10 net and
member set are present for the RPC trigger / probe, the member cars drive as σ* and are never commanded).  Same CLI as CITY_eval_m3p."""
import sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_eval_m3p as P  # noqa: E402  (imports CITY_eval_m3 with --spat-arm none)
_argv = sys.argv; sys.argv = [_argv[0], '--spat-arm', 'none']
import scripts.CITY_eval_m3_shadow as SH  # noqa: E402,F401  (adds SHADOW:<fleet.pt> to E4.load_fleet)
sys.argv = _argv
if __name__ == '__main__':
    import runpy
    runpy.run_path(str(ROOT / 'scripts/CITY_eval_m3p.py'), run_name='__main__')
