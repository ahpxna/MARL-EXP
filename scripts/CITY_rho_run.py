#!/usr/bin/env python3
"""Penetration wrapper (PROTOCOL_CITY_GEN_20261005 (c)): sets CITY_q7_cross_version.RHO (the fleet share, default 0.5; read at fleet-load time
as E4.Q7.RHO) and runs the next script as __main__.  Usage: CITY_rho_run.py <rho> scripts/<x>.py <args>"""
import runpy, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
if __name__ == '__main__':
    Q7.RHO = float(sys.argv[1]); target = sys.argv[2]; sys.argv = [target] + sys.argv[3:]; runpy.run_path(str(ROOT / target), run_name='__main__')
