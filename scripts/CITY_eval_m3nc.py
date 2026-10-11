#!/usr/bin/env python3
"""M3-NC descriptive arm WC5-c (PROTOCOL_CITY_M3_NEG_CONFIRM_20261004): CITY_eval_m3 UNCHANGED (imported with --spat-arm none) with its SPaT
source W.BASE replaced by 'commitc:<q>:<table>': commitment while a switch is pending at the light (exactly W's make_commit branch), else the
convention-CORRECTED empirical forecast (CITY_spat_forecast_c.make_spat_c) at quantile q.  W.spat_m3 still does the logging / query capture;
the sidecar is W's (<tag>_m3.json) with arm = commitc:...  Usage: CITY_eval_m3nc.py --spat-arm commitc:<q>:<table> --light M3WC:<k>:<W> ..."""
import argparse, hashlib, json, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
pre = argparse.ArgumentParser(add_help=False); pre.add_argument('--spat-arm', required=True); A0, REST = pre.parse_known_args()
assert A0.spat_arm.startswith('commitc:'), 'this wrapper only adds commitc:<q>:<table>'
_argv = sys.argv; sys.argv = [_argv[0], '--spat-arm', 'none']
import scripts.CITY_eval_m3 as W  # noqa: E402
sys.argv = _argv
import scripts.CITY_spat_forecast_c as FCC  # noqa: E402
import scripts.CITY_env as CE  # noqa: E402
sha = lambda b: hashlib.sha256(b).hexdigest()
W.E4.SRC = f"{W.E4.SRC}+m3nc:{sha(Path(__file__).read_bytes())}"
_, q, tb = A0.spat_arm.split(':', 2); FC_C = FCC.make_spat_c(json.loads(Path(tb).read_text()), float(q))[0]; W.LOG['meta']['table_sha256'] = sha(Path(tb).read_bytes())
W.LOG['meta']['q'] = float(q); SRC_N = dict(commitment=0, forecast=0)


def spat_cc(tid, link):
    L = W.CUR.get('light'); ls = CE.ls
    if L is not None and tid in getattr(L, 'pending', {}):
        Ts = L.pending[tid]; t = ls.simulation.getTime(); st = W._serve(tid, link); ph = ls.trafficlight.getPhase(tid); SRC_N['commitment'] += 1
        if st[ph][link] in 'Gg':
            return dict(ttg=0.0, ttr=Ts - t, valid=True, source='commitment')
        return dict(ttg=Ts - t + W.YELLOW + W.OBS, ttr=0.0, valid=True, source='commitment')
    SRC_N['forecast'] += 1; return FC_C(tid, link)


W.BASE = spat_cc; W.arm = A0.spat_arm
if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--light', default='ACT'); p.add_argument('--light-obs', default='raw'); p.add_argument('--light-fallback', default='none')
    p.add_argument('--fleet', default='human'); p.add_argument('--guard', default='none')
    p.add_argument('--record'); p.add_argument('--replay'); p.add_argument('--replay-dir'); p.add_argument('--discharge', action='store_true'); p.add_argument('--delay-trace', action='store_true')
    p.add_argument('--swap-at', type=float); p.add_argument('--swap-light'); p.add_argument('--swap-fleet')
    p.add_argument('--seeds', type=int, nargs='+', default=[100, 101, 102, 103, 104]); p.add_argument('--smoke', action='store_true')
    p.add_argument('--tag'); p.add_argument('--out', required=True)
    a = p.parse_args(REST); W.E4.main(a)
    side = dict(arm=W.arm, light=a.light, fleet=a.fleet, base_sigma=None, spat_total=W.LOG['total'], spat_valid=W.LOG['valid'], meta=W.LOG['meta'],
                per_seed=W.LOG.get('per_seed', {}), source_counts=SRC_N, source_sha256=sha(Path(__file__).read_bytes()))
    Path(a.out, f'{a.tag}_m3.json').write_text(json.dumps(side)); print('m3nc sidecar', json.dumps({k: v for k, v in side.items() if k != 'per_seed'})[:300], flush=True)
