#!/usr/bin/env python3
"""M4 stage 4b evaluator (Amendment M4-A7) on spider (CITY_m4s_run patches): --light RLK:<checkpoint> (LightRLK) and the fleet SPaT arm
  --spat-arm none | fck:<q>:<table>    none: always 'unavailable' (the rule / a v11 residual fleet falls back to σ*-based driving);
                                       fck: CITY_spat_forecast_k at quantile q of the table
Fleets: every CITY_eval6_v11 spec (PL:<v11 fleet.pt>, GLOSAL:0.3, ...).  Sidecar <tag>_f1k.json: spat calls (total / valid), commanded, table sha."""
import argparse, hashlib, json, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
pre = argparse.ArgumentParser(add_help=False); pre.add_argument('--spat-arm', required=True); A0, REST = pre.parse_known_args()
import scripts.CITY_m4s_run  # noqa: E402,F401
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_eval4 as E4  # noqa: E402
import scripts.CITY_eval6_v11 as _E  # noqa: E402,F401
import scripts.CITY_fleet_v8 as V8, scripts.CITY_es_glosa as ES, scripts.CITY_glosa_lane as GL, scripts.CITY_glosa_lane_d as LD, scripts.CITY_fleet_v11 as V11  # noqa: E402,E401
import scripts.CITY_spat_forecast_k as FK  # noqa: E402
from scripts.CITY_lightk import NetInfoK, LightRLK  # noqa: E402
sha = lambda b: hashlib.sha256(b).hexdigest()
E4.SRC = f"{E4.SRC}+m4s_f1k{A0.spat_arm.split(':')[0]}:{sha(Path(__file__).read_bytes())}"
N = dict(total=0, valid=0); CARS = []; META = {}
if A0.spat_arm == 'none':
    BASE = lambda tid, link: dict(ttg=0.0, ttr=0.0, valid=False, source='unavailable')  # noqa: E731
else:
    _, q, tb = A0.spat_arm.split(':', 2); BASE = FK.make_spat_k(json.loads(Path(tb).read_text()), float(q))[0]; META.update(q=float(q), table=tb, table_sha256=sha(Path(tb).read_bytes()))


def spat_f(tid, link):
    s = BASE(tid, link); N['total'] += 1; N['valid'] += bool(s['valid']); return s


for m in (V8, ES, GL, LD, V11):
    m.spat = spat_f
_bl = E4.build_light


def build_light(spec, info, adapter, box):
    if spec.startswith('RLK:'):
        META['light_sha256'] = sha(Path(spec[4:]).read_bytes()); return Q7.NET_S, LightRLK(NetInfoK(Q7.NET_S), Q7.load_policy(spec[4:])), [], None
    return _bl(spec, info, adapter, box)


E4.build_light = build_light
_lf = E4.load_fleet


def load_fleet(spec, seed, guard):
    c, p = _lf(spec, seed, guard); CARS.append(c)
    if spec.startswith('PL:'):
        META['fleet_sha256'] = sha(Path(spec[3:]).read_bytes())
    return c, p


E4.load_fleet = load_fleet
if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--light', default='ACT'); p.add_argument('--light-obs', default='raw'); p.add_argument('--light-fallback', default='none')
    p.add_argument('--fleet', default='human'); p.add_argument('--guard', default='none')
    p.add_argument('--record'); p.add_argument('--replay'); p.add_argument('--replay-dir'); p.add_argument('--discharge', action='store_true'); p.add_argument('--delay-trace', action='store_true')
    p.add_argument('--swap-at', type=float); p.add_argument('--swap-light'); p.add_argument('--swap-fleet')
    p.add_argument('--seeds', type=int, nargs='+', default=[100]); p.add_argument('--smoke', action='store_true')
    p.add_argument('--tag'); p.add_argument('--out', required=True)
    a = p.parse_args(REST); E4.main(a)
    cmd = int(sum(c.decisions if isinstance(c, V11.CarPPOL) else getattr(c, 'fired', 0) for c in CARS))
    Path(a.out, f'{a.tag}_f1k.json').write_text(json.dumps(dict(arm=A0.spat_arm, light=a.light, fleet=a.fleet, commanded=cmd, **N, meta=META)))
