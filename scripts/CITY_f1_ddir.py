#!/usr/bin/env python3
"""F1 diagnostic D-dir (PROTOCOL_CITY_F1 §1; ORACLE, open-loop): the C-61 replay with the oracle ttg shifted by DELTA seconds,
ttg' = max(0.5, ttg + DELTA) (ttr unchanged).  DELTA = 0 is CITY_m3_headroom exactly (self-check KD-1).
Usage: CITY_f1_ddir.py DELTA <CITY_eval4 arguments with --replay-dir and --fleet>"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
DELTA = float(sys.argv.pop(1))
import scripts.CITY_m3_headroom as H  # noqa: E402  (rebinds spat to the oracle; patches Replay)
import hashlib  # noqa: E402
H.E4.SRC = f"{H.E4.SRC}+ddir{DELTA:g}:{hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}"
_or = H.spat_oracle


def spat_shift(tid, link):
    s = _or(tid, link)
    if DELTA != 0 and s['valid'] and s['ttg'] > 0:
        s = dict(s, ttg=max(0.5, s['ttg'] + DELTA))
    return s


for m in (H.V8, H.ES, H.GL, H.LD, H.V11):
    m.spat = spat_shift

if __name__ == '__main__':
    import argparse
    p = argparse.ArgumentParser()
    p.add_argument('--light', default='ACT'); p.add_argument('--light-obs', default='raw'); p.add_argument('--light-fallback', default='none')
    p.add_argument('--fleet', default='human'); p.add_argument('--guard', default='none')
    p.add_argument('--record'); p.add_argument('--replay'); p.add_argument('--replay-dir'); p.add_argument('--discharge', action='store_true'); p.add_argument('--delay-trace', action='store_true')
    p.add_argument('--swap-at', type=float); p.add_argument('--swap-light'); p.add_argument('--swap-fleet')
    p.add_argument('--seeds', type=int, nargs='+', default=[100, 101, 102, 103, 104]); p.add_argument('--smoke', action='store_true')
    p.add_argument('--tag'); p.add_argument('--out', required=True)
    H.E4.main(p.parse_args())
