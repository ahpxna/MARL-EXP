#!/usr/bin/env python3
"""Live viewer for M3 (04/10/2026): CITY_live_viewer.py (not edited) with the M3 evaluation stack (CITY_eval_m3: M3E / M3WC / M3B / M3CYC
lights, RL-H:k, and the SPaT arms).  --spat-arm as in CITY_eval_m3; --signals eval:<light spec>; --vehicles eval:<fleet spec>."""
import argparse, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
pre = argparse.ArgumentParser(add_help=False); pre.add_argument('--spat-arm', default='none'); A0, REST = pre.parse_known_args()
_argv = sys.argv; sys.argv = [_argv[0], '--spat-arm', A0.spat_arm]
import scripts.CITY_eval_m3 as W  # noqa: E402  (pre-parses --spat-arm at import)
sys.argv = [_argv[0]] + REST
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_live_viewer as LV  # noqa: E402
E4 = W.E4


def make_controllers(_ls, net_file, signals, vehicles, seed):
    import torch
    torch.set_grad_enabled(False); out = []
    if signals.startswith('eval:'):
        _n, light, _x, init = E4.build_light(signals[5:], E4.NetInfo(E4.Q7.NET_S), 'raw', None)
        if light is not None:
            out.append(light)
    if vehicles.startswith('eval:'):
        spec = vehicles[5:]; cars, _ = E4.load_fleet(spec, seed, 'always' if spec.startswith('L-ACT') else 'none'); out.append(cars)
    return out


CE.make_controllers = make_controllers
if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--net', required=True); ap.add_argument('--routes', required=True)
    ap.add_argument('--port', type=int, default=8796); ap.add_argument('--end', type=float, default=5400); ap.add_argument('--seed', type=int, default=0)
    ap.add_argument('--signals', default='fixed'); ap.add_argument('--vehicles', default='default'); ap.add_argument('--label', default='')
    LV.serve(ap.parse_args())
