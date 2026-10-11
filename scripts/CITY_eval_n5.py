#!/usr/bin/env python3
"""N5 grid4 evaluator (copy of CITY_eval_n4 using the provider variants of CITY_spat_forecast_n5).  Base docstring:
N4 grid4 evaluator (PROTOCOL_CITY_N4_SERVICE_GATE_20261005): CITY_eval_f1 (UNCHANGED, imported with --spat-arm none) with the fleet SPaT
replaced by the gated N2 provider (CITY_spat_forecast_n4), --n4 <q>:<gate>:<model.pt>.  The N2 Tracker is stepped every second by a Logger
subclass, as in CITY_eval_n2.  Sidecar <out>/<tag>_n4.json: valid queries, published, activation share.
Usage: CITY_eval_n4.py --n4 0.5:h:20:<model> --light RL-H:k --fleet PL:... --seeds ... --tag T --out D"""
import argparse, hashlib, json, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
pre = argparse.ArgumentParser(add_help=False); pre.add_argument('--n4', required=True); A0, REST = pre.parse_known_args()
_argv = sys.argv; sys.argv = [_argv[0], '--spat-arm', 'none'] + REST
import scripts.CITY_eval_f1 as EF  # noqa: E402
sys.argv = _argv
import scripts.CITY_spat_forecast_n2 as N2  # noqa: E402
import scripts.CITY_spat_forecast_n5 as N4  # noqa: E402
E4 = EF.E4; sha = lambda b: hashlib.sha256(b).hexdigest(); parts = A0.n4.split(':'); q = float(parts[0]); mp = parts[-1]; gate = ':'.join(parts[1:-1])
TR = N2.Tracker(); INFO = E4.NetInfo(E4.Q7.NET_S); SPAT = N4.make_spat_n4(mp, q, INFO, TR, gate); EF.BASE = SPAT
EF.META.update(n4=A0.n4, model_sha256=sha(Path(mp).read_bytes())); E4.SRC = f"{E4.SRC}+n5:{sha(Path(__file__).read_bytes())}"


class TLogger(E4.Logger):
    def __init__(self, *a, **k):
        super().__init__(*a, **k); self.ids_f = sorted(self.info.tls); TR.__init__()

    def step(self, t):
        super().step(t); TR.step(self.ids_f)


E4.Logger = TLogger
if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--light', default='ACT'); p.add_argument('--light-obs', default='raw'); p.add_argument('--light-fallback', default='none')
    p.add_argument('--fleet', default='human'); p.add_argument('--guard', default='none')
    p.add_argument('--record'); p.add_argument('--replay'); p.add_argument('--replay-dir'); p.add_argument('--discharge', action='store_true'); p.add_argument('--delay-trace', action='store_true')
    p.add_argument('--swap-at', type=float); p.add_argument('--swap-light'); p.add_argument('--swap-fleet')
    p.add_argument('--seeds', type=int, nargs='+', default=[600]); p.add_argument('--smoke', action='store_true')
    p.add_argument('--tag'); p.add_argument('--out', required=True)
    a = p.parse_args(REST); E4.main(a); s = SPAT.stats
    Path(a.out, f'{a.tag}_n5.json').write_text(json.dumps(dict(n4=A0.n4, gate=gate, q=q, **s, activation=s['published'] / max(1, s['valid']))))
