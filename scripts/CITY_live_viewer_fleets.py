#!/usr/bin/env python3
"""Live viewer for the SPaT-pilot fleets (04/10/2026): CITY_live_viewer.py (not edited) with one more vehicles spec,
    --vehicles eval:<spec>   any fleet spec of the evaluation stack (CITY_eval6_v11 -> eval6 / lane / lane2 / v11), built exactly as
                             in evaluation (deterministic, record=False), e.g. P:<v8 fleet.pt> (pilot B), R:<v9/v10 fleet.pt>,
                             GLOSA, GLOSAL:0.3 (R8 rule), GLOSAL0:0.3 (GLOSA∘σ*), ESLD:<theta json> (R9 learned), PL:<v11 fleet.pt> (R10),
                             L-ACT:0 (no fleet: always-SUMO; membership only, for colouring)
Agents (membership _stable_u(seed, vid) < 0.5) are drawn as agents.  Signals: 'fixed' = the grid4 FT programs.
Usage: CITY_live_viewer_fleets.py --net research/city_sim/net/grid4.net.xml --routes .../rou_s100.xml --seed 100 --vehicles eval:<spec> --port P"""
import sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_live_viewer as LV  # noqa: E402

_orig = CE.make_controllers


def make_controllers(_ls, net_file, signals, vehicles, seed):
    out = _orig(_ls, net_file, signals, vehicles if not vehicles.startswith('eval:') else 'default', seed)
    if vehicles.startswith('eval:'):
        import torch
        torch.set_grad_enabled(False)
        import scripts.CITY_eval4 as E4
        import scripts.CITY_eval6_v11 as _E  # noqa: F401  (registers every evaluation fleet spec on E4.load_fleet)
        spec = vehicles[5:]
        cars, _ = E4.load_fleet(spec, seed, 'always' if spec.startswith('L-ACT') else 'none')
        out.append(cars)
    return out


CE.make_controllers = make_controllers

if __name__ == '__main__':
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('--net', required=True); ap.add_argument('--routes', required=True)
    ap.add_argument('--port', type=int, default=8780); ap.add_argument('--end', type=float, default=5400); ap.add_argument('--seed', type=int, default=0)
    ap.add_argument('--signals', default='fixed'); ap.add_argument('--vehicles', default='default'); ap.add_argument('--label', default='')
    LV.serve(ap.parse_args())
