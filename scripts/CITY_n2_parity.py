#!/usr/bin/env python3
"""KN2-1 / KN2-2 (exit 1 on failure): the provider's online feature rows (provider_rows_s<seed>.json from CITY_eval_n2 --featlog) must equal
the offline builder's rows (CITY_n2_fit.build on the same run's feat_s<seed>.npz) at the same (second, light, target green, kind), and the
online prediction must equal the model applied to the offline row.  Usage: CITY_n2_parity.py <featlog dir> <seed> <model.pt>"""
import json, sys
from pathlib import Path
import numpy as np
import torch
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_n2_fit as NF  # noqa: E402
import scripts.CITY_eval4 as E4  # noqa: E402
if __name__ == '__main__':
    D, seed, mp = Path(sys.argv[1]), sys.argv[2], sys.argv[3]; info = E4.NetInfo(E4.Q7.NET_S); greens = {t: list(info.tls[t]['greens']) for t in info.tls}
    X, Y, W, K, M = NF.build([D / f'feat_s{seed}.npz'], greens); ids = sorted(info.tls)
    idx = {(i, ids[j], g, int(k)): r for r, ((fi, i, j, g, ph, s), k) in enumerate(zip(M, K))}
    rows = json.load(open(D / f'provider_rows_s{seed}.json')); d = torch.load(mp, weights_only=False); net = NF.QNet(d['d']); net.load_state_dict(d['state']); net.eval()
    n = bad = miss = 0; badp = 0; ex = []
    for t, tid, g, kind, feat, pred in rows:
        key = (int(t) - 1, tid, int(g), int(kind)); r = idx.get(key)
        if r is None:
            miss += 1; continue                                      # censored offline (no observed end / onset) -- not comparable
        n += 1; diff = np.abs(np.array(feat, np.float32) - X[r]).max()
        if diff > 1e-6:
            bad += 1; len(ex) < 3 and ex.append((key, float(diff), list(np.flatnonzero(np.abs(np.array(feat, np.float32) - X[r]) > 1e-6))))
        with torch.no_grad():
            po = float(net(torch.as_tensor(X[r][None]))[0, list(d['qs']).index(float(json.load(open(D / 'q.json'))['q']))]) if (D / 'q.json').exists() else pred
        badp += abs(po - pred) > 1e-4
    ok = n > 0 and bad == 0 and badp == 0
    print(f'KN2-1 compared {n} provider rows ({miss} censored offline): feature mismatches {bad} {ex}; KN2-2 prediction mismatches {badp} -> {"PASS" if ok else "FAIL"}')
    sys.exit(0 if ok else 1)
