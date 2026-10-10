#!/usr/bin/env python3
"""F1 evaluation wrapper (PROTOCOL_CITY_F1 §0, §3): CITY_eval6_v11 (all fleet specs; CITY_eval4.run) with the fleet SPaT arm
  --spat-arm none | fcc:<q>:<table>   (fcc = the convention-corrected empirical forecast CITY_spat_forecast_c, quantile q of table)
and a sidecar <out>/<tag>_f1.json with spat calls (total / valid), commanded vehicle-seconds and the provider hash.  No file is edited."""
import argparse, hashlib, json, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_eval4 as E4  # noqa: E402
import scripts.CITY_eval6_v11 as _E  # noqa: E402,F401
import scripts.CITY_spat_forecast_c as FCC  # noqa: E402
import scripts.CITY_fleet_v8 as V8  # noqa: E402
import scripts.CITY_es_glosa as ES  # noqa: E402
import scripts.CITY_glosa_lane as GL  # noqa: E402
import scripts.CITY_glosa_lane_d as LD  # noqa: E402
import scripts.CITY_fleet_v11 as V11  # noqa: E402
sha = lambda b: hashlib.sha256(b).hexdigest()
pre = argparse.ArgumentParser(add_help=False); pre.add_argument('--spat-arm', required=True); A0, REST = pre.parse_known_args()
E4.SRC = f"{E4.SRC}+f1{A0.spat_arm.split(':')[0]}:{sha(Path(__file__).read_bytes())}"
N = dict(total=0, valid=0); CARS = []; META = {}
if A0.spat_arm == 'none':
    BASE = lambda tid, link: dict(ttg=0.0, ttr=0.0, valid=False, source='unavailable')  # noqa: E731
else:
    _, q, tb = A0.spat_arm.split(':', 2); BASE = FCC.make_spat_c(json.loads(Path(tb).read_text()), float(q))[0]; META.update(q=float(q), table=tb, table_sha256=sha(Path(tb).read_bytes()))


def spat_f1(tid, link):
    s = BASE(tid, link); N['total'] += 1; N['valid'] += bool(s['valid']); return s


for m in (V8, ES, GL, LD, V11):
    m.spat = spat_f1
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
    p.add_argument('--seeds', type=int, nargs='+', default=[100, 101, 102, 103, 104]); p.add_argument('--smoke', action='store_true')
    p.add_argument('--tag'); p.add_argument('--out', required=True)
    a = p.parse_args(REST); E4.main(a)
    cmd = int(sum(c.decisions if isinstance(c, V11.CarPPOL) else getattr(c, 'fired', 0) for c in CARS))
    Path(a.out, f'{a.tag}_f1.json').write_text(json.dumps(dict(arm=A0.spat_arm, light=a.light, fleet=a.fleet, commanded=cmd, **N, meta=META)))
