#!/usr/bin/env python3
"""M2b evaluation wrapper (PROTOCOL_CITY_M2_COMPAT_20261004 Amendment M2b; 04/10/2026): CITY_eval6_v11 (all fleet specs) plus the SPaT
service arm, and commanded vehicle-seconds logging (M2b-4):
  --spat-arm program   CITY_spat_feature.spat as is (exact under FT; used for the FT rows)
  --spat-arm none      the light publishes no SPaT (labelled fallback; every call 'unavailable')
  --spat-arm fc50|fc20 the causal forecast CITY_spat_forecast (table research/.../m2b/forecast_rlh<k>.json for --light RL-H:<k>),
                       median or 0.2-quantile of the remaining time
Sidecar <out>/<tag>_m2b.json: arm, light, spat calls (total / valid), commanded vehicle-seconds summed over the seeds
(GLOSA-family fleets: `fired`; the PPO residual CarPPOL: `decisions`, each of which is a command).  No file is edited; the fleet modules'
`spat` names are rebound here; source_sha256 records '+m2b<arm>:<wrapper sha>'."""
import argparse, hashlib, json, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_eval4 as E4  # noqa: E402
import scripts.CITY_eval6_v11 as _E  # noqa: E402,F401
import scripts.CITY_spat_feature as SF  # noqa: E402
import scripts.CITY_spat_forecast as FC  # noqa: E402
import scripts.CITY_fleet_v8 as V8  # noqa: E402
import scripts.CITY_es_glosa as ES  # noqa: E402
import scripts.CITY_glosa_lane as GL  # noqa: E402
import scripts.CITY_glosa_lane_d as LD  # noqa: E402
import scripts.CITY_fleet_v11 as V11  # noqa: E402

pre = argparse.ArgumentParser(add_help=False); pre.add_argument('--spat-arm', choices=['program', 'none', 'fc50', 'fc20'], required=True)
A0, REST = pre.parse_known_args()
E4.SRC = f"{E4.SRC}+m2b{A0.spat_arm}:{hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}"
LIGHT = REST[REST.index('--light') + 1] if '--light' in REST else 'ACT'
N = dict(total=0, valid=0); CARS = []
if A0.spat_arm == 'program':
    base = SF.spat
elif A0.spat_arm == 'none':
    def base(tid, link):
        return dict(ttg=0.0, ttr=0.0, valid=False, source='unavailable')
else:
    assert LIGHT.startswith('RL-H:'), 'the forecast tables exist for RL-H:k only'
    TABLE = ROOT / f'research/city_sim/spat_pilot_20261004/m2b/forecast_rlh{LIGHT.split(":")[1]}.json'
    base, _F = FC.make_spat(json.loads(TABLE.read_text()), 0.5 if A0.spat_arm == 'fc50' else 0.2)


def spat_m2b(tid, link):
    s = base(tid, link); N['total'] += 1; N['valid'] += bool(s['valid']); return s


for m in (V8, ES, GL, LD, V11):
    m.spat = spat_m2b
_lf = E4.load_fleet


def load_fleet(spec, seed, guard):
    c, p = _lf(spec, seed, guard); CARS.append(c); return c, p


E4.load_fleet = load_fleet


def commanded():
    return int(sum(c.decisions if isinstance(c, V11.CarPPOL) else getattr(c, 'fired', 0) for c in CARS))


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--light', default='ACT'); p.add_argument('--light-obs', default='raw'); p.add_argument('--light-fallback', default='none')
    p.add_argument('--fleet', default='human'); p.add_argument('--guard', default='none')
    p.add_argument('--record'); p.add_argument('--replay'); p.add_argument('--replay-dir'); p.add_argument('--discharge', action='store_true'); p.add_argument('--delay-trace', action='store_true')
    p.add_argument('--swap-at', type=float); p.add_argument('--swap-light'); p.add_argument('--swap-fleet')
    p.add_argument('--seeds', type=int, nargs='+', default=[100, 101, 102, 103, 104]); p.add_argument('--smoke', action='store_true')
    p.add_argument('--tag'); p.add_argument('--out', required=True)
    a = p.parse_args(REST); E4.main(a)
    Path(a.out, f'{a.tag}_m2b.json').write_text(json.dumps(dict(arm=A0.spat_arm, light=a.light, commanded=commanded(), **N)))
    print('spat calls', N, 'commanded vehicle-seconds', commanded(), 'arm', A0.spat_arm, 'light', a.light, flush=True)
