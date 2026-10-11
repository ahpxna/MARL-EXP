#!/usr/bin/env python3
"""W6-4 LCD evaluator (PROTOCOL_CITY_WAVE6_20261005): CITY_eval_n8.py (UNCHANGED, imported: CDC mechanism, spat_cdc exact SPaT, KN8-1 check)
with one more light kind  --light LCD:<ckpt>  = N8.CDC whose rule is the trained DQN (CITY_lcd.py), greedy.  --spat program | none as in N8.
Usage: CITY_eval_n9.py --spat program|none --light LCD:<ckpt> --fleet ... --seeds ... --tag T --out D"""
import argparse, json, sys
from pathlib import Path
import numpy as np
import torch
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_eval_n8 as N8  # noqa: E402
import scripts.CITY_lcd as LCD  # noqa: E402
E4 = N8.E4; E4.SRC = f"{E4.SRC}+n9:{N8.sha(Path(__file__).read_bytes())}"


class LCDEval(N8.CDC):
    def __init__(self, info, ckpt):
        super().__init__(info, [0.0, 0.0, 0.0, 0.0]); d = torch.load(ckpt, weights_only=False); self.q = LCD.qnet(); self.q.load_state_dict(d['state']); self.q.eval()
        self.D = np.array(d['actions'], float)

    def rule(self, tid, g):
        with torch.no_grad():
            a = int(self.q(torch.as_tensor(LCD.feats(self.info, tid, g)[None]))[0].argmax())
        return float(np.clip(self.D[a], N8.DMIN, N8.DMAX))


_bl = E4.build_light


def build_light(spec, info, adapter, box):
    if spec.startswith('LCD:'):
        L = LCDEval(info, spec[4:]); N8.CHK['light'] = L; return E4.Q7.NET_S, L, [], None
    return _bl(spec, info, adapter, box)


E4.build_light = build_light
if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--light', default='ACT'); p.add_argument('--light-obs', default='raw'); p.add_argument('--light-fallback', default='none')
    p.add_argument('--fleet', default='human'); p.add_argument('--guard', default='none')
    p.add_argument('--record'); p.add_argument('--replay'); p.add_argument('--replay-dir'); p.add_argument('--discharge', action='store_true'); p.add_argument('--delay-trace', action='store_true')
    p.add_argument('--swap-at', type=float); p.add_argument('--swap-light'); p.add_argument('--swap-fleet')
    p.add_argument('--seeds', type=int, nargs='+', default=[600]); p.add_argument('--smoke', action='store_true')
    p.add_argument('--tag'); p.add_argument('--out', required=True)
    a = p.parse_args(N8.REST); E4.main(a)
    d = N8.CHK.get('durs', []); runs = N8.CHK.get('runs', [])
    Path(a.out, f'{a.tag}_n8.json').write_text(json.dumps(dict(spat=N8.A0.spat, light=a.light, kn8_1=runs, mism=sum(r['mismatches'] for r in runs), checked=sum(r['checked'] for r in runs),
                                                          dur_mean=float(np.mean(d)) if d else None, dur_p90=float(np.percentile(d, 90)) if d else None, n_greens=len(d))))
