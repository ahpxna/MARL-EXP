#!/usr/bin/env python3
"""KMT7 (PROTOCOL_CITY_MIDTOWN_TRANSFER_20261010, MT-F resume): is CITY_n2_fit_lowmem.py the same fit as CITY_n2_fit.py?
Both were run on the grid W19 data of light t59 (16 lights, small enough for the original).  Criteria, fixed before the run:
  C1 the original rerun reproduces the stored W19 model (same best validation pinball within 1e-4, same weights within 1e-5);
  C2 best validation pinball: |lowmem - original| <= 0.5 % of the original;
  C3 predictions on every validation row, both quantiles: median |diff| <= 0.1 s and 99th percentile <= 1 s.
Usage: CITY_n2_fit_lowmem_check.py <data dir> <stored W19 model> <original rerun dir> <lowmem dir> <out json>"""
import json, sys
from pathlib import Path
import numpy as np
import torch
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_n2_fit as N2  # noqa: E402
import scripts.CITY_n2_fit_lowmem as LM  # noqa: E402

D, stored, orig_dir, low_dir, out = Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3]), Path(sys.argv[4]), Path(sys.argv[5])
import scripts.CITY_eval4 as E4
info = E4.NetInfo(E4.Q7.NET_S); greens = {t: list(info.tls[t]['greens']) for t in info.tls}
Xv, Jv, L, Yv, Wv, Kv, _ = LM.build([D / f'feat_s{s}.npz' for s in (6, 7)], greens); n = Xv.shape[1]
xv, jv, yv, wv = map(torch.as_tensor, (Xv, Jv, Yv, Wv))


def load(p):
    c = torch.load(p, weights_only=False); net = N2.QNet(c['d']); net.load_state_dict(c['state']); net.eval(); return c, net


cs, ns = load(stored); co, no = load(orig_dir / 'n2_k59.pt'); cl, nl = load(low_dir / 'n2_k59.pt')
pin = {name: LM.pinball_batched(m, xv, jv, n, yv, wv) for name, m in (('stored', ns), ('original', no), ('lowmem', nl))}
with torch.no_grad():   # the original's own full-batch forward on the explicit one-hot input, for the stored and rerun models
    dense = torch.cat([xv, torch.nn.functional.one_hot(jv, L).to(xv.dtype)], 1)
    p_orig = no(dense).numpy(); p_low = LM.predict(nl, xv, jv, n).numpy(); p_low_dense = nl(dense).numpy()
wdiff = max(float((cs['state'][k] - co['state'][k]).abs().max()) for k in cs['state'])
a = np.abs(p_low - p_orig)
res = dict(rows_val=int(len(Yv)), lights=int(L), val_pinball=pin,
           C1=dict(pinball_diff=abs(pin['stored'] - pin['original']), max_weight_diff=wdiff, ok=bool(abs(pin['stored'] - pin['original']) <= 1e-4 and wdiff <= 1e-5)),
           C2=dict(rel_diff=abs(pin['lowmem'] - pin['original']) / pin['original'], ok=bool(abs(pin['lowmem'] - pin['original']) <= 0.005 * pin['original'])),
           C3=dict(median_abs=float(np.median(a)), p99_abs=float(np.percentile(a, 99)), max_abs=float(a.max()),
                   ok=bool(np.median(a) <= 0.1 and np.percentile(a, 99) <= 1.0)),
           lookup_vs_dense_same_model_max_abs=float(np.abs(p_low - p_low_dense).max()))
res['PASS'] = bool(res['C2']['ok'] and res['C3']['ok'])
out.write_text(json.dumps(res, indent=1)); print(json.dumps(res, indent=1))
