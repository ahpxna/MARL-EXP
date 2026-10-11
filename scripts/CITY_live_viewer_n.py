#!/usr/bin/env python3
"""Live viewer for the M3 night arms on grid4 (05/10/2026): CITY_live_viewer.py (not edited) with the evaluation stacks used tonight.
  --arm R     RL-H:k, fleet R10 without SPaT (drives as sigma*): the reference R
  --arm c2    RL-H:k, age-only forecast c2 at q0.1                      (C-97 / C-99: no fuel gain, agent TL +1.2)
  --arm N2    RL-H:k, state forecast N2 at q0.5, published to all         (C-99: fuel -3.4 %, agent TL +2.3 -> rejected)
  --arm N4g   RL-H:k, N2 behind the SELECT gate wh:3,10                   (C-104: benefit removed -> rejected)
  --arm RPC   RPC2 registered (forced hold, message withdrawn at yellow)  (C-95: fuel +9.4 % -> rejected)
  --arm HYB   RL-H:k, N2 with exact yellow answers                        (C-106: fuel -4.7 %, agent TL +1.8)
  --arm TSI   HYB + light-input adapter q:2:0 (frozen RL-H)               (C-110 SELECT: fuel -4.4 %, agent TL +0.18; confirmation running)
Controllers step light first, then the fleet, then the forecaster's run-length tracker (as the evaluators' logger does)."""
import argparse, json, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
pre = argparse.ArgumentParser(add_help=False); pre.add_argument('--arm', choices=['R', 'c2', 'N2', 'N4g', 'RPC', 'HYB', 'TSI'], required=True)
pre.add_argument('--k', type=int, default=0); A0, REST = pre.parse_known_args()
_argv = sys.argv
if A0.arm == 'RPC':
    sys.argv = [_argv[0]]
    import scripts.CITY_eval_m3p2 as M2  # noqa: E402  (fleet SPaT = the RPC light's spat; RPC2 light spec)
    E4 = M2.E4
else:
    sys.argv = [_argv[0], '--spat-arm', 'none']
    import scripts.CITY_eval_f1 as EF  # noqa: E402
    E4 = EF.E4
sys.argv = [_argv[0]] + REST
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_live_viewer as LV  # noqa: E402
TB = ROOT / f'research/city_sim/m3_20261004/prep/prov_rlh{A0.k}_cl.json'; MOD = ROOT / f'research/city_sim/n2_20261005/model/n2_k{A0.k}.pt'
TR = None
if A0.arm != 'RPC':
    import scripts.CITY_spat_forecast_n2 as N2  # noqa: E402
    import scripts.CITY_spat_forecast_n4 as N4  # noqa: E402
    import scripts.CITY_spat_forecast_c2 as C2  # noqa: E402
    INFO = E4.NetInfo(E4.Q7.NET_S); TR = N2.Tracker()
    if A0.arm == 'R':
        EF.BASE = lambda tid, link: dict(ttg=0.0, ttr=0.0, valid=False, source='unavailable')
    elif A0.arm == 'c2':
        EF.BASE = C2.make_spat_c2(json.loads(TB.read_text()), 0.1)[0]
    else:
        gate = {'N2': 'all', 'N4g': 'wh:3,10', 'HYB': f'hyb:{TB}', 'TSI': f'hyb:{TB}'}[A0.arm]; EF.BASE = N4.make_spat_n4(str(MOD), 0.5, INFO, TR, gate)
ADAPTER = 'q:2:0' if A0.arm == 'TSI' else 'raw'
SIGNALS = f'eval:RPC2:{A0.k}:receiver:1:1' if A0.arm == 'RPC' else f'eval:RL-H:{A0.k}'


class TrackStep:
    def __init__(self, ids):
        self.ids = ids; TR.__init__()

    def step(self, t):
        TR.step(self.ids)


def make_controllers(_ls, net_file, signals, vehicles, seed):
    import torch
    torch.set_grad_enabled(False); out = []; info = E4.NetInfo(E4.Q7.NET_S)
    _n, light, _x, _init = E4.build_light(SIGNALS[5:], info, ADAPTER, None)
    if light is not None:
        out.append(light)
    cars, _ = E4.load_fleet(vehicles[5:], seed, 'none'); out.append(cars)
    if TR is not None:
        out.append(TrackStep(sorted(info.tls)))
    return out


CE.make_controllers = make_controllers
LV.PAGE = ROOT / 'scripts' / 'CITY_live_viewer_n.html'
if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--port', type=int, default=8800); ap.add_argument('--end', type=float, default=3600); ap.add_argument('--seed', type=int, default=600)
    ap.add_argument('--vehicles', default='eval:PL:research/city_sim/spat_pilot_20261004/fleets_v11/L11_s13_fleet.pt'); ap.add_argument('--label', default='')
    a = ap.parse_args(); a.net = E4.Q7.NET_S; a.routes = E4.Q7.ROU.format(a.seed); a.signals = SIGNALS
    LV.serve(a)
