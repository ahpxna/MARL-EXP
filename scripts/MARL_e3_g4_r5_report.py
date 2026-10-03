#!/usr/bin/env python3
"""R5 of PROTOCOL_E3_G4_REPLICATION_ADDENDUM2_20261001.md (written 12:24:22 EDT before any 4×4 result).
net_Z_s(c) = acc(relayCage_st_s) − acc(Z_s) on the 4×4 development panel under c ∈ {iid, low} (e3_g4_constk_20261001/NF_s<s>_<c>,
computed before the replication report).  R5a: sign of mean net_Z(c) = sign of mean target gain(c) for iid and low;
R5b: Spearman(net_Z(low), gain(low)) ≥ 0.5 over the complete seeds.  Target rows read with the replication report's loader.
"""
from __future__ import annotations
import json, sys
from pathlib import Path
import numpy as np
from scipy.stats import spearmanr

sys.path.insert(0, str(Path(__file__).resolve().parent))
import MARL_e3_g4_replication_report as G

M = Path('research/marl_budget'); P = M / 'e3_g4_constk_20261001'


def netz(s, c):
    d = P / f'NF_s{s}_{c}'
    if not (d / 'manifest.json').exists():
        return None
    m = json.loads((d / 'manifest.json').read_text())
    if m.get('status') != 'COMPLETE' or m.get('self_check') != 'PASS':
        return None
    f = np.load(d / 'flags.npz'); return float(f['protoS'].mean() - f['zok'].mean())


def main():
    rep = json.loads((M / 'e3_g4_replication_report_20261001.json').read_text()); S = rep.get('complete', [])
    L = [f'complete seeds (replication report) {S}']
    nz = {c: {s: netz(s, c) for s in S} for c in ('iid', 'low')}
    if len(S) < 8 or any(v is None for c in nz for v in nz[c].values()):
        print('INCOMPLETE'); return
    out = {}
    for c in ('iid', 'low'):
        t, r = G.CONDS[c]; g = {}
        for s in S:
            Z = G.rows(f'Z_s{s}', 'none'); X = G.rows(f'R_s{s}_{t}', r); g[s] = -100 * G.eff(X, Z)
        mz, mg = float(np.mean(list(nz[c].values()))), float(np.mean(list(g.values())))
        rho = float(spearmanr([nz[c][s] for s in S], [g[s] for s in S]).correlation)
        out[c] = dict(mean_netZ=mz, mean_gain=mg, sign_ok=bool(np.sign(mz) == np.sign(mg)), rho=rho, netZ=nz[c], gain=g)
        L.append(f'{c}: mean dev net_Z {mz:+.4f} | mean target gain {mg:+.2f} % | sign match {out[c]["sign_ok"]} | Spearman {rho:+.3f}')
    R5a = out['iid']['sign_ok'] and out['low']['sign_ok']; R5b = out['low']['rho'] >= 0.5
    L += [f'R5a sign match at iid and low: {"SUPPORTED" if R5a else "NOT SUPPORTED"}',
          f'R5b Spearman(net_Z(low), gain(low)) {out["low"]["rho"]:+.3f} >= 0.5: {"SUPPORTED" if R5b else "NOT SUPPORTED"}']
    out.update(R5a=bool(R5a), R5b=bool(R5b))
    text = '\n'.join(L); print(text)
    (M / 'e3_g4_r5_report_20261001.json').write_text(json.dumps(out, indent=1, default=float))
    (M / 'e3_g4_r5_report_20261001.txt').write_text(text + '\n')


if __name__ == '__main__':
    main()
