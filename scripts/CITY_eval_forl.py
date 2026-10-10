#!/usr/bin/env python3
"""W11 FoRL evaluator (PROTOCOL_CITY_WAVE11_FORL_20261005): CITY_eval_f1 (UNCHANGED, imported with --spat-arm none) with
  --light FORL:<ckpt>          the FoRL signal (scripts/CITY_forl.LightFoRL, argmax per head) for every controller;
  --forl-spat on | off         on: the fleet's SPaT is the light's own forecast (CITY_forl.make_spat_forl); off: no SPaT (fleet = sigma*).
Other lights (RL-H:k, FT, ...) pass through unchanged.  Sidecar <out>/<tag>_forl.json: provider counters.
Usage: CITY_eval_forl.py --forl-spat on --light FORL:<ckpt> --fleet PL:<fleet> --seeds ... --tag T --out D"""
import argparse, hashlib, json, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
pre = argparse.ArgumentParser(add_help=False); pre.add_argument('--forl-spat', default='on', choices=['on', 'off']); A0, REST = pre.parse_known_args()
_argv = sys.argv; sys.argv = [_argv[0], '--spat-arm', 'none'] + REST
import scripts.CITY_eval_f1 as EF  # noqa: E402
sys.argv = _argv
import scripts.CITY_forl as FO  # noqa: E402
E4 = EF.E4; HOLD = {}; INFO = E4.NetInfo(E4.Q7.NET_S); sha = lambda b: hashlib.sha256(b).hexdigest()  # noqa: E731
_bl = E4.build_light


def build_light(spec, info, adapter, box):
    if spec.startswith('FORL:'):
        light = FO.LightFoRL(info, FO.load(spec[5:]), train=False); HOLD['light'] = light
        return E4.Q7.NET_S, light, [], None
    HOLD['light'] = None
    return _bl(spec, info, adapter, box)


E4.build_light = build_light
SPAT = FO.make_spat_forl(HOLD, INFO) if A0.forl_spat == 'on' else None
if SPAT is not None:
    EF.BASE = SPAT
E4.SRC = f"{E4.SRC}+forl:{sha(Path(__file__).read_bytes())}:{FO.SRC}"
if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--light', default='ACT'); p.add_argument('--light-obs', default='raw'); p.add_argument('--light-fallback', default='none')
    p.add_argument('--fleet', default='human'); p.add_argument('--guard', default='none')
    p.add_argument('--record'); p.add_argument('--replay'); p.add_argument('--replay-dir'); p.add_argument('--discharge', action='store_true'); p.add_argument('--delay-trace', action='store_true')
    p.add_argument('--swap-at', type=float); p.add_argument('--swap-light'); p.add_argument('--swap-fleet')
    p.add_argument('--seeds', type=int, nargs='+', default=[600]); p.add_argument('--smoke', action='store_true')
    p.add_argument('--tag'); p.add_argument('--out', required=True)
    a = p.parse_args(REST); E4.main(a)
    meta = dict(forl_spat=A0.forl_spat, light=a.light, provider=(SPAT.stats if SPAT else None))
    if a.light.startswith('FORL:'):
        meta['light_sha256'] = sha(Path(a.light[5:]).read_bytes())
    if a.fleet.startswith('PL:'):
        meta['fleet_sha256'] = sha(Path(a.fleet[3:]).read_bytes())
    Path(a.out, f'{a.tag}_forl.json').write_text(json.dumps(meta))
