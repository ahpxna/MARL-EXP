#!/usr/bin/env python3
"""W12-4 DCA-task DEV selection (PROTOCOL_CITY_WAVE12_20261006, Amendment A3).  For each light t and arm (info / raw), among the saved
checkpoints b (88 / 176 / 352 rollouts) evaluated on DEV 600-611 with the development fleet L11_s13 (full horizon), apply TSI's feasibility-
first rule: checkpoints meeting every M3 limit against R on DEV (one-sided 95 % over seeds) -> lowest fuel; otherwise the lowest agent time
loss.  Writes <dir>/dev/selection.json and the DEV budget curve.  Usage: CITY_w12_dcas_select.py <dir>   (W12_SMOKE=1: one light, seed 600)"""
import json, os, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w6_report_v2 as V  # noqa: E402
from scripts.CITY_w6_validation import rows  # noqa: E402
D = Path(sys.argv[1]); SM = os.environ.get('W12_SMOKE') == '1'
S = [600] if SM else list(range(600, 612)); LT = (4,) if SM else (4, 5, 6, 7, 8); B = (3, 6, 9) if SM else (88, 176, 352)
Rt = rows(D / 'dev'); sel = {}; out = ['== W12-4 DEV selection (TSI feasibility-first rule; DEV 600-611, fleet L11_s13, full horizon)']
for t in LT:
    for m in ('info', 'raw'):
        cand = []
        for b in B:
            a = f'DEV_{m}_t{t}_b{b}'; r = V.paired(Rt, lambda l, f: a, lambda l, f: f'R_DEV_t{t}', (t,), ('s13',), S)
            ok, _ = V.limits(r, V.tele(Rt, lambda l, f: a, (t,), ('s13',), S), V.tele(Rt, lambda l, f: f'R_DEV_t{t}', (t,), ('s13',), S))
            cand.append(dict(b=b, ok=bool(ok), fuel=r['fuel_agent']['point'], tla=r['timeloss_agent']['point'], tla_up=r['timeloss_agent']['up']))
            out.append(f'  t{t} {m} b{b}: fuel {r["fuel_agent"]["point"]:+.2f} % | agent TL {r["timeloss_agent"]["point"]:+.2f} (up {r["timeloss_agent"]["up"]:+.2f}) | all limits {ok}')
        q = [c for c in cand if c['ok']]
        ch = min(q, key=lambda c: c['fuel']) if q else min(cand, key=lambda c: c['tla'])
        sel[f'{m}_t{t}'] = dict(choice=ch['b'], qualified=[c['b'] for c in q], rule='lowest fuel among qualified' if q else 'fallback: lowest agent TL', table=cand)
        out.append(f'  -> t{t} {m}: choose b{ch["b"]} ({sel[f"{m}_t{t}"]["rule"]})')
(D / 'dev' / 'selection.json').write_text(json.dumps(sel, indent=1)); (D / 'dev' / 'report_dev.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
