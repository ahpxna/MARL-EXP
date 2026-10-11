#!/usr/bin/env python3
"""M2 evaluation wrapper (PROTOCOL_CITY_M2_COMPAT_20261004; 04/10/2026): CITY_eval6_v11 (all fleet specs) plus a SPaT-label arm.
  --spat-label naive     the fleets call CITY_spat_feature.spat as is (program-derived; under a learned light it is out of scope and,
                         during yellow transitions, a mislabelled forecast)
  --spat-label labelled  a learned light (--light RL-*) publishes NO SPaT: every spat() call of the fleets returns 'unavailable';
                         under FT the light publishes its plan and labelled == naive
Both arms count the fleets' spat() calls (total, valid) and write <out>/<tag>_spat.json.  No file is edited: the fleet modules'
`spat` names are rebound here; source_sha256 records '+m2<arm>:<wrapper sha>'."""
import argparse, hashlib, json, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_eval4 as E4  # noqa: E402
import scripts.CITY_eval6_v11 as _E  # noqa: E402,F401  (eval6 + lane + lane2 + v11 specs)
import scripts.CITY_spat_feature as SF  # noqa: E402
import scripts.CITY_fleet_v8 as V8  # noqa: E402
import scripts.CITY_es_glosa as ES  # noqa: E402
import scripts.CITY_glosa_lane as GL  # noqa: E402
import scripts.CITY_glosa_lane_d as LD  # noqa: E402
import scripts.CITY_fleet_v11 as V11  # noqa: E402

pre = argparse.ArgumentParser(add_help=False); pre.add_argument('--spat-label', choices=['naive', 'labelled'], required=True)
A0, REST = pre.parse_known_args()
E4.SRC = f"{E4.SRC}+m2{A0.spat_label}:{hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}"
LIGHT = REST[REST.index('--light') + 1] if '--light' in REST else 'ACT'
PUBLISHES = not LIGHT.startswith('RL') or A0.spat_label == 'naive'
N = dict(total=0, valid=0)
_orig = SF.spat


def spat_m2(tid, link):
    s = _orig(tid, link) if PUBLISHES else dict(ttg=0.0, ttr=0.0, valid=False, source='unavailable')
    N['total'] += 1; N['valid'] += bool(s['valid'])
    return s


for m in (V8, ES, GL, LD, V11):
    m.spat = spat_m2

if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--light', default='ACT'); p.add_argument('--light-obs', default='raw'); p.add_argument('--light-fallback', default='none')
    p.add_argument('--fleet', default='human'); p.add_argument('--guard', default='none')
    p.add_argument('--record'); p.add_argument('--replay'); p.add_argument('--replay-dir'); p.add_argument('--discharge', action='store_true'); p.add_argument('--delay-trace', action='store_true')
    p.add_argument('--swap-at', type=float); p.add_argument('--swap-light'); p.add_argument('--swap-fleet')
    p.add_argument('--seeds', type=int, nargs='+', default=[100, 101, 102, 103, 104]); p.add_argument('--smoke', action='store_true')
    p.add_argument('--tag'); p.add_argument('--out', required=True)
    a = p.parse_args(REST); E4.main(a)
    Path(a.out, f'{a.tag}_spat.json').write_text(json.dumps(dict(arm=A0.spat_label, light=a.light, publishes=PUBLISHES, **N)))
    print('spat calls', N, 'arm', A0.spat_label, 'light', a.light, flush=True)
