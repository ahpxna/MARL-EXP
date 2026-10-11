#!/usr/bin/env python3
"""N1 grid4 evaluator (PROTOCOL_CITY_N1_TAIL_SUPPORT_20261005): CITY_eval_f1 (UNCHANGED, imported with --spat-arm none, so its sidecar logic,
fleet loading and E4 patches are the frozen ones) with the fleet SPaT replaced by the N1 provider:
  --n1 <mode>:<q>:<old-format table>   mode all | tail | strict; the table is augmented as provider c2.
Sidecar <tag>_n1.json: support-state counts of the fleet's queries, abstentions, totals.  Usage: CITY_eval_n1.py --n1 ... --light RL-H:k --fleet PL:..."""
import argparse, hashlib, json, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
pre = argparse.ArgumentParser(add_help=False); pre.add_argument('--n1', required=True); A0, REST = pre.parse_known_args()
_argv = sys.argv; sys.argv = [_argv[0], '--spat-arm', 'none'] + REST
import scripts.CITY_eval_f1 as EF  # noqa: E402
sys.argv = _argv
import scripts.CITY_spat_forecast_n1 as N1  # noqa: E402
import scripts.CITY_spat_forecast_c2 as C2  # noqa: E402
sha = lambda b: hashlib.sha256(b).hexdigest()
mode, q, tb = A0.n1.split(':', 2); SPAT, F, CNT = N1.make_spat_n1(C2.augment(json.loads(Path(tb).read_text())), float(q), mode)
EF.E4.SRC = f"{EF.E4.SRC}+n1{mode}:{sha(Path(__file__).read_bytes())}"; EF.META.update(n1=A0.n1, table_sha256=sha(Path(tb).read_bytes()))
EF.BASE = SPAT
if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--light', default='ACT'); p.add_argument('--light-obs', default='raw'); p.add_argument('--light-fallback', default='none')
    p.add_argument('--fleet', default='human'); p.add_argument('--guard', default='none')
    p.add_argument('--record'); p.add_argument('--replay'); p.add_argument('--replay-dir'); p.add_argument('--discharge', action='store_true'); p.add_argument('--delay-trace', action='store_true')
    p.add_argument('--swap-at', type=float); p.add_argument('--swap-light'); p.add_argument('--swap-fleet')
    p.add_argument('--seeds', type=int, nargs='+', default=[600]); p.add_argument('--smoke', action='store_true')
    p.add_argument('--tag'); p.add_argument('--out', required=True)
    a = p.parse_args(REST); EF.E4.main(a)
    Path(a.out, f'{a.tag}_n1.json').write_text(json.dumps(dict(n1=A0.n1, light=a.light, fleet=a.fleet, counts=dict(CNT), spat_total=EF.N['total'], spat_valid=EF.N['valid'])))
