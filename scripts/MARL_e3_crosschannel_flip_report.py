#!/usr/bin/env python3
"""Report of PROTOCOL_E3_CROSSCHANNEL_FLIP_20261003.md (written 04:1x EDT 03/10 before the full run).  net = PF - NF per seed."""
import json
from pathlib import Path
import numpy as np
P = Path('research/marl_budget/e3_crosschannel_flip_20261003'); out = []; V = {}
for net, seeds in (('3x3', range(5)), ('4x4', range(10))):
    S = {s: json.loads((P / f'{net}_s{s}' / 'summary.json').read_text()) for s in seeds if (P / f'{net}_s{s}' / 'manifest.json').exists()}
    out.append(f'== {net}: seeds {sorted(S)}')
    if not S:
        continue
    for tag in S[next(iter(S))]:
        acc = {c: np.mean([S[s][tag]['acc'][c] for s in S]) for c in S[next(iter(S))][tag]['acc']}
        out.append(f'{tag} acc ' + ' '.join(f'{c} {v:.3f}' for c, v in acc.items()))
        for pr in ('const1->iid', 'iid->const1', 'const2->iid', 'const2->const1'):
            x = [S[s][tag]['pairs'][pr] for s in S]
            net_ = [d['net'] for d in x]
            out.append(f'   {pr}: NF {np.mean([d["nf"] for d in x]):.3f} PF {np.mean([d["pf"] for d in x]):.3f} net {np.mean(net_):+.3f} '
                       f'({sum(v < 0 for v in net_)}/{len(net_)} < 0) BTC {np.mean([d["btc"] for d in x]):.3f} agree {np.mean([d["agree"] for d in x]):.3f}')
            V[(net, tag, pr)] = net_
            V[(net, tag, pr, 'btc')] = [d['btc'] for d in x]
def cnt(k, f):
    return sum(f(v) for v in V.get(k, []))
if ('3x3', 'relayCK1_st', 'const1->iid') in V:
    n3 = len(V[('3x3', 'relayCK1_st', 'const1->iid')]); n4 = len(V.get(('4x4', 'relayCK1_st', 'const1->iid'), []))
    fl1 = cnt(('3x3', 'relayCK1_st', 'const1->iid'), lambda v: v < 0) >= 4 and (n4 == 0 or cnt(('4x4', 'relayCK1_st', 'const1->iid'), lambda v: v < 0) >= 8)
    fl2 = cnt(('3x3', 'relay6Cage_st', 'iid->const1'), lambda v: v < 0) >= 4 and (n4 == 0 or cnt(('4x4', 'relayCage_st', 'iid->const1'), lambda v: v < 0) >= 8)
    fl3 = cnt(('3x3', 'relayMIX_st', 'const1->iid'), lambda v: v >= 0) >= 4
    b1, bm = V[('3x3', 'relayCK1_st', 'const1->iid', 'btc')], V[('3x3', 'relayMIX_st', 'const1->iid', 'btc')]
    fl4 = sum(x < y for x, y in zip(b1, bm)) >= 4
    for name, ok in (('FL1 CK1 const1->iid net < 0', fl1), ('FL2 iid-trained iid->const1 net < 0', fl2),
                     ('FL3 MIX const1->iid net >= 0', fl3), ('FL4 BTC(CK1) < BTC(MIX) const1->iid', fl4)):
        out.append(f'{name}: {"SUPPORTED" if ok else "NOT SUPPORTED"}' + ('' if n4 == 10 or not name.startswith(('FL1', 'FL2')) else f' (4x4 seeds {n4}/10)'))
txt = '\n'.join(out); print(txt); (P / 'report.txt').write_text(txt + '\n')
