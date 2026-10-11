#!/usr/bin/env python3
"""W12-2 (PROTOCOL_CITY_WAVE12_20261006): open-loop replay with the K-green signal model.  CITY_eval4.Replay takes its green set from the
two-green NetInfo, which on spider misses green phase 4 of the three-green signals B1-B6 (C-163), so those greens were not held during replay.
This wrapper replaces CITY_eval4.Replay by ReplayK (greens from NetInfoK) and then runs the target evaluator unchanged.
Usage: CITY_w12_replayk.py <target script> <its args, including --replay / --replay-dir>"""
import runpy, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
TARGET, ARGS = sys.argv[1], sys.argv[2:]
import scripts.CITY_eval4 as E4  # noqa: E402
from scripts.CITY_lightk import NetInfoK  # noqa: E402
_Replay = E4.Replay


class ReplayK(_Replay):
    def __init__(self, rec, info):
        super().__init__(rec, info)
        k = NetInfoK(E4.Q7.NET_S); self.greens = {tid: set(d['greens']) for tid, d in k.tls.items()}


E4.Replay = ReplayK
E4.SRC = f"{getattr(E4, 'SRC', '')}+w12replayk"
if __name__ == '__main__':
    sys.argv = [TARGET] + ARGS; runpy.run_path(str(ROOT / TARGET), run_name='__main__')
