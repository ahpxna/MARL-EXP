#!/usr/bin/env python3
"""Live viewer for M4 on the spider network (04/10/2026): CITY_live_viewer.py (not edited) with the M4 stack (CITY_m4s_run spider patches;
the RLK / WCK lights of CITY_m4s_wck; the rule fleet GLOSA-L∘σ*) and one SPaT arm:
  --arm ft         static programs, fleet SPaT from the program (the rule's home condition, stage 2a / 3)
  --arm labelled   learned light RLK, no SPaT (the rule drives exactly as σ*, stage 3)
  --arm naive      learned light RLK, fleet SPaT from the static program RLK no longer follows (stage 3: harmed)
  --arm wck5       RLK with fixed-window commitment W = 5, SPaT = commitment or unavailable (stage 4a)
  --arm forecastk  RLK, multi-green empirical forecast (CITY_spat_forecast_k) at --q of --table (stage-3 forecast arm, draft)
--light <RLK checkpoint>; --vehicles eval:<fleet spec> (default eval:GLOSAL:0.3).  Controllers step light first, then the fleet."""
import argparse, json, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
pre = argparse.ArgumentParser(add_help=False); pre.add_argument('--arm', choices=['ft', 'labelled', 'naive', 'wck5', 'forecastk'], required=True)
pre.add_argument('--light', default=str(ROOT / 'research/city_sim/m4_20261004/spider/RLK_sp11.pt')); pre.add_argument('--q', type=float, default=0.5)
pre.add_argument('--table', default=str(ROOT / 'research/city_sim/m4_20261004/spider/s4b/prov/fk_rlk11.json')); A0, REST = pre.parse_known_args()
_argv = sys.argv; sys.argv = [_argv[0], '--spat-mode', 'commit']
import scripts.CITY_m4s_wck as WK  # noqa: E402  (spider patches; E4.build_light for RLK: / WCK:; fleet spat = commitment-or-unavailable)
sys.argv = [_argv[0]] + REST
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_live_viewer as LV  # noqa: E402
import scripts.CITY_spat_feature as SF  # noqa: E402
import scripts.CITY_spat_forecast_k as FK  # noqa: E402
E4 = WK.E4
UNAV = lambda tid, link: dict(ttg=0.0, ttr=0.0, valid=False, source='unavailable')  # noqa: E731
SPAT = {'ft': SF.spat, 'naive': SF.spat, 'labelled': UNAV, 'wck5': WK.spat_wck}
if A0.arm == 'forecastk':
    SPAT['forecastk'] = FK.make_spat_k(json.loads(Path(A0.table).read_text()), A0.q)[0]
for m in (WK.V8, WK.ES, WK.GL, WK.LD, WK.V11):
    m.spat = SPAT[A0.arm]
SIGNALS = {'ft': 'fixed', 'labelled': f'eval:RLK:{A0.light}', 'naive': f'eval:RLK:{A0.light}', 'wck5': f'eval:WCK:{A0.light}:5', 'forecastk': f'eval:RLK:{A0.light}'}[A0.arm]


def make_controllers(_ls, net_file, signals, vehicles, seed):
    import torch
    torch.set_grad_enabled(False); out = []
    if signals.startswith('eval:'):
        _n, light, _x, _init = E4.build_light(signals[5:], E4.NetInfo(E4.Q7.NET_S), 'raw', None)
        if light is not None:
            out.append(light)
    if vehicles.startswith('eval:'):
        spec = vehicles[5:]; cars, _ = E4.load_fleet(spec, seed, 'always' if spec.startswith('L-ACT') else 'none'); out.append(cars)
    return out


CE.make_controllers = make_controllers
LV.PAGE = ROOT / 'scripts' / 'CITY_live_viewer_m4s.html'   # same page, spider title (the shared page is not edited)
if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--routes', default=None); ap.add_argument('--port', type=int, default=8800); ap.add_argument('--end', type=float, default=5400)
    ap.add_argument('--seed', type=int, default=1000); ap.add_argument('--vehicles', default='eval:GLOSAL:0.3'); ap.add_argument('--label', default='')
    a = ap.parse_args(); a.net = E4.Q7.NET_S; a.routes = a.routes or E4.Q7.ROU.format(a.seed); a.signals = SIGNALS
    if a.signals == 'fixed' and a.vehicles != 'default':
        a.signals = 'fixed'                                   # LV calls make_controllers whenever vehicles != 'default'
    LV.serve(a)
