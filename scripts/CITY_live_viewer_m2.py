#!/usr/bin/env python3
"""Live viewer for M2 (PROTOCOL_CITY_M2_COMPAT_20261004; 04/10/2026): CITY_live_viewer.py (not edited) with the evaluation stack's own
lights and fleets, and the M2 SPaT arm:
    --signals eval:<light spec>   e.g. eval:RL-H:0 (the learned light exactly as in CITY_eval4.build_light, raw input, no box) or fixed (FT)
    --vehicles eval:<fleet spec>  any CITY_eval6_v11 fleet spec (ESLD:<theta>, PL:<fleet.pt>, GLOSAL:0.3, L-ACT:0 = no fleet, ...)
    --spat-label naive|labelled   labelled: a learned light publishes NO SPaT (every spat() of the fleets returns 'unavailable'), as in
                                  CITY_eval6_m2; naive: the program-derived spat() as is.
Controllers step light first, then the fleet (as CITY_env.run_episode)."""
import argparse, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
pre = argparse.ArgumentParser(add_help=False); pre.add_argument('--spat-label', choices=['naive', 'labelled'], default='naive')
A0, REST = pre.parse_known_args(); sys.argv = [sys.argv[0]] + REST
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_live_viewer as LV  # noqa: E402
import scripts.CITY_eval4 as E4  # noqa: E402
import scripts.CITY_eval6_v11 as _E  # noqa: E402,F401
import scripts.CITY_fleet_v8 as V8  # noqa: E402
import scripts.CITY_es_glosa as ES  # noqa: E402
import scripts.CITY_glosa_lane as GL  # noqa: E402
import scripts.CITY_glosa_lane_d as LD  # noqa: E402
import scripts.CITY_fleet_v11 as V11  # noqa: E402

SIGNALS = REST[REST.index('--signals') + 1] if '--signals' in REST else 'fixed'
if A0.spat_label == 'labelled' and SIGNALS.startswith('eval:RL'):
    def _none(tid, link):
        return dict(ttg=0.0, ttr=0.0, valid=False, source='unavailable')
    for m in (V8, ES, GL, LD, V11):
        m.spat = _none


def make_controllers(_ls, net_file, signals, vehicles, seed):
    import torch
    torch.set_grad_enabled(False)
    out = []
    if signals.startswith('eval:'):
        _net, light, _extra, _init = E4.build_light(signals[5:], E4.NetInfo(E4.Q7.NET_S), 'raw', None)
        if light is not None:
            out.append(light)
    if vehicles.startswith('eval:'):
        spec = vehicles[5:]; cars, _ = E4.load_fleet(spec, seed, 'always' if spec.startswith('L-ACT') else 'none'); out.append(cars)
    return out


CE.make_controllers = make_controllers

if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--net', required=True); ap.add_argument('--routes', required=True)
    ap.add_argument('--port', type=int, default=8790); ap.add_argument('--end', type=float, default=5400); ap.add_argument('--seed', type=int, default=0)
    ap.add_argument('--signals', default='fixed'); ap.add_argument('--vehicles', default='default'); ap.add_argument('--label', default='')
    LV.serve(ap.parse_args())
