#!/usr/bin/env python3
"""W8-1 D4 (PROTOCOL_CITY_WAVE8_20261005): CITY_m4s_tsi_eval.py (UNCHANGED, imported with its --tk) with the fleet service restricted to the
signals with K greens (--mask k2 | k3); every other signal's queries return unavailable.  Light adapter unchanged (--light as usual).
Usage: CITY_w8_spmask_eval.py --mask k2|k3 --tk n2k:<table>:<model> [CITY_m4s_tsi_eval args ...]"""
import argparse, json, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
pre = argparse.ArgumentParser(add_help=False); pre.add_argument('--mask', required=True, choices=('k2', 'k3')); B0, REST = pre.parse_known_args()
sys.argv = [sys.argv[0]] + REST
import scripts.CITY_m4s_tsi_eval as T  # noqa: E402
KEEP = 2 if B0.mask == 'k2' else 3; INNER = T.SPAT; MC = dict(kept=0, masked=0)


def masked(tid, link):
    if tid in T.INFO.tls and len(T.INFO.tls[tid]['greens']) == KEEP:
        MC['kept'] += 1; return INNER(tid, link)
    MC['masked'] += 1; return dict(ttg=0.0, ttr=0.0, valid=False, source='masked')


T.SPAT = masked; T.STATS['mask'] = dict(keep_K=KEEP, counts=MC)
if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--light', default='ACT'); p.add_argument('--light-obs', default='raw'); p.add_argument('--light-fallback', default='none')
    p.add_argument('--fleet', default='human'); p.add_argument('--guard', default='none')
    p.add_argument('--record'); p.add_argument('--replay'); p.add_argument('--replay-dir'); p.add_argument('--discharge', action='store_true'); p.add_argument('--delay-trace', action='store_true')
    p.add_argument('--swap-at', type=float); p.add_argument('--swap-light'); p.add_argument('--swap-fleet')
    p.add_argument('--seeds', type=int, nargs='+', default=[0]); p.add_argument('--smoke', action='store_true')
    p.add_argument('--tag'); p.add_argument('--out', required=True)
    a = p.parse_args(T.REST); T.E4.main(a)
    Path(a.out, f'{a.tag}_tk.json').write_text(json.dumps(dict(tk=T.A0.tk, mask_arg=B0.mask, light=a.light, fleet=a.fleet, stats=T.STATS, queries=int(sum(T.QC.values())))))
