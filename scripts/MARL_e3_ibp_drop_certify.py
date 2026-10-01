"""Can a SOUND interval bound (IBP through the actor MLP) certify that dropping ONE delivered packet keeps a receiver's
action?  Offline, scratch s3 actor, the post-prefix inputs x of the forced-probe v2 rows (7,776 receivers).  For every
receiver and every FRESH slot j, the dropped input differs from x only in slot j: fresh 1 -> 0, age 0 -> [0, A], content
within +-c of the delivered one (the cached copy is older).  Box = that set; certified iff the lower bound of the current
top logit exceeds the upper bound of every other valid logit.  Also the empirical flip rate of the flag-only change."""
import glob, json, sys
from pathlib import Path
import numpy as np, torch
ROOT = Path('/Users/phanan/cig-amf-main'); sys.path.insert(0, str(ROOT))
base = ROOT / 'research/marl_budget/e3_forced_v2_20260929/e3_scratch_seeds34_20260928_actor_s3'
R = []
for d in sorted(x for x in glob.glob(str(base / '*')) if Path(x).is_dir()):
    R += json.loads(Path(d, 'rows.json').read_text())
ck = torch.load(ROOT / 'research/marl_budget/e3_scratch_seeds34_20260928/actor_s3/ckpt_best.pt', weights_only=False); sd = ck['actor']
W1, b1, W2, b2, W3, b3 = (sd[k].numpy().astype(np.float64) for k in ('body.0.weight', 'body.0.bias', 'body.2.weight', 'body.2.bias', 'head.weight', 'head.bias'))
X = np.array([x for r in R for x in r['x']], np.float64); Lg = np.array([l for r in R for l in r['logits']]); valid = Lg > -1e8
def fwd(x):
    return np.tanh(np.tanh(x @ W1.T + b1) @ W2.T + b2) @ W3.T + b3
def ibp(c, rad):
    lo1, hi1 = c @ W1.T + b1 - rad @ np.abs(W1).T, c @ W1.T + b1 + rad @ np.abs(W1).T
    h_lo, h_hi = np.tanh(lo1), np.tanh(hi1); hc, hr = (h_lo + h_hi) / 2, (h_hi - h_lo) / 2
    lo2, hi2 = hc @ W2.T + b2 - hr @ np.abs(W2).T, hc @ W2.T + b2 + hr @ np.abs(W2).T
    g_lo, g_hi = np.tanh(lo2), np.tanh(hi2); gc, gr = (g_lo + g_hi) / 2, (g_hi - g_lo) / 2
    return gc @ W3.T + b3 - gr @ np.abs(W3).T, gc @ W3.T + b3 + gr @ np.abs(W3).T
L0 = fwd(X); L0 = np.where(valid, L0, -1e9); a0 = L0.argmax(1); print('argmax reproduces stored', (a0 == Lg.argmax(1)).mean())
B0, blk = 44, 29
for A, c in ((0.0, 0.0), (0.3, 0.0), (0.3, 0.05), (0.3, 0.1), (0.3, 0.2)):
    cert, n, flip = 0, 0, 0
    for k in range(8):
        s0 = B0 + k * blk; fr = X[:, s0] > 0.5
        if not fr.any():
            continue
        C = X[fr].copy(); rad = np.zeros_like(C)
        C[:, s0] = 0.5; rad[:, s0] = 0.5                       # fresh in [0, 1]
        C[:, s0 + 2] = A / 2; rad[:, s0 + 2] = A / 2           # age/100 in [0, A]
        rad[:, s0 + 13: s0 + 21] = c                            # content +- c (vehicles/30, waiting/30)
        lo, hi = ibp(C, rad); aa = a0[fr]; v = valid[fr]
        lo_top = lo[np.arange(len(aa)), aa]; hi_oth = np.where(v, hi, -np.inf); hi_oth[np.arange(len(aa)), aa] = -np.inf
        cert += int((lo_top > hi_oth.max(1)).sum()); n += int(fr.sum())
        if A == 0.0 and c == 0.0:
            Xd = X[fr].copy(); Xd[:, s0] = 0.0; Ld = np.where(v, fwd(Xd), -1e9); flip += int((Ld.argmax(1) != aa).sum())
    print(f'box: fresh 1->0, age in [0,{A}], content +-{c}: certified {cert / n:.3f} of {n} (receiver, fresh slot) pairs' + (f'; flag-only drop actually flips {flip / n:.3f}' if A == 0 and c == 0 else ''))
gap = np.sort(L0, 1)[:, -1] - np.sort(L0, 1)[:, -2]; print('logit gap quantiles 10/50/90:', np.quantile(gap, [0.1, 0.5, 0.9]).round(3))
