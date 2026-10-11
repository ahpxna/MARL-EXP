#!/usr/bin/env python3
"""W20 light trainer: scripts/CITY_w19_train_light.py (the RL-H recipe, unchanged) after installing scripts/CITY_w20_bench.py, so that the
W20 families' observation (per-second RESCO / sumo-rl tracker) and training reward (DWT / WAITN / PRESS) are in force.
Usage: CITY_w20_train_light.py --out DIR --k K [--episodes 120] [--smoke]"""
import sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w20_bench as B  # noqa: E402
import scripts.CITY_w19_obs as W  # noqa: E402
import scripts.CITY_w19_train_light as T  # noqa: E402
if __name__ == '__main__':
    import argparse
    p = argparse.ArgumentParser(); p.add_argument('--out', required=True); p.add_argument('--k', type=int, required=True)
    p.add_argument('--episodes', type=int, default=120); p.add_argument('--smoke', action='store_true'); p.add_argument('--dqn-t', type=int)
    p.add_argument('--name'); a = p.parse_args()
    f = W.fam_of(a.k); assert f in B.NEWF, (a.k, f); B.TRACK.need_acc = W.FAMS[f][2] == 'DWT'
    T.main(a)
