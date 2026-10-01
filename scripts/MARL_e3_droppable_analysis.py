"""Which prefix-stream packets does the exact lifetime oracle (greedy, H = end) drop?  Legal features only; logistic
regression with leave-episodes-out CV (4 folds by episode); AUC.  Rows: every packet of the prefix stream at every step."""
import json, sys
from pathlib import Path
import numpy as np
import torch
from torch import nn
from scipy.stats import rankdata
torch.set_num_threads(1)

def roc_auc_score(y, s):
    y = np.asarray(y); r = rankdata(s); n1 = y.sum(); n0 = len(y) - n1
    return float((r[y == 1].sum() - n1 * (n1 + 1) / 2) / (n1 * n0))

class Fit:
    def __init__(self, hidden):
        self.hidden = hidden
    def fit(self, X, y):
        torch.manual_seed(0); self.mu, self.sd = X.mean(0), X.std(0) + 1e-6
        d = X.shape[1]; self.net = nn.Linear(d, 1) if self.hidden == 0 else nn.Sequential(nn.Linear(d, self.hidden), nn.ReLU(), nn.Linear(self.hidden, 1))
        opt = torch.optim.Adam(self.net.parameters(), lr=1e-2); Xt = torch.as_tensor((X - self.mu) / self.sd, dtype=torch.float32); yt = torch.as_tensor(y, dtype=torch.float32)
        for _ in range(300):
            opt.zero_grad(); l = nn.functional.binary_cross_entropy_with_logits(self.net(Xt).squeeze(-1), yt); l.backward(); opt.step()
        return self
    def predict_proba(self, X):
        with torch.no_grad():
            q = torch.sigmoid(self.net(torch.as_tensor((X - self.mu) / self.sd, dtype=torch.float32)).squeeze(-1)).numpy()
        return np.stack([1 - q, q], 1)
ROOT = Path('/Users/phanan/cig-amf-main'); sys.path.insert(0, str(ROOT))
from models.marl_hetero_selector import prefix_sets
for tag in sys.argv[1:]:
    R = json.loads((ROOT / f'research/marl_budget/e3_zero_loss_20260929/{tag}/rows.json').read_text())
    X, y, g, names = [], [], [], None
    for e, r in enumerate(R):
        for s in r['arms']['greedy_Hend']['steps']:
            order, K, L0 = s['order'], s['K'], s['L0']; P = prefix_sets(order, K); z = s['z']; sent = set(s['sent'])
            gaps = [b['gap'] for b in s['bid']]
            for pos, j in enumerate(order[:L0]):
                blk = z[1 + 12 * j: 1 + 12 * (j + 1)]           # present, age/100, phase/10, elapsed/100, veh/100 x4, wait/100 x4
                dec = [i for i in range(len(order)) if j in P[i]]
                f = [pos / 9, L0 / 9, len(dec) / 8, min(gaps[i] for i in dec) if dec else 10.0, float(np.mean([gaps[i] for i in dec])) if dec else 10.0,
                     blk[0], blk[1], sum(blk[4:8]), sum(blk[8:12]), s['t'] / 26, gaps[j]]
                X.append(f); y.append(int(j not in sent)); g.append(e)
    X, y, g = np.array(X), np.array(y), np.array(g)
    names = ['pos', 'L0', 'n_decoders', 'min_gap_decoders', 'mean_gap_decoders', 'present', 'age', 'veh_sum', 'wait_sum', 't', 'own_gap_sender']
    folds = g % 4; aucs = {}
    for nm, mk in (('logistic', lambda: Fit(0)), ('mlp', lambda: Fit(32))):
        p = np.zeros(len(y))
        for k in range(4):
            tr, te = folds != k, folds == k; mdl = mk().fit(X[tr], y[tr]); p[te] = mdl.predict_proba(X[te])[:, 1]
        aucs[nm] = roc_auc_score(y, p)
        # precision at the threshold keeping 10% / 25% of packets flagged droppable
        for q in (0.9, 0.75):
            th = np.quantile(p, q); sel = p >= th
            aucs[f'{nm}_precision_top{int(round((1-q)*100))}'] = float(y[sel].mean())
    single = {n: roc_auc_score(y, X[:, k]) for k, n in enumerate(names)}
    print(f'{tag}: {len(y)} packets, droppable share {y.mean():.3f}; CV AUC ' + ', '.join(f'{k} {v:.3f}' for k, v in aucs.items()))
    print('   single-feature AUC: ' + ', '.join(f'{k} {v:.2f}' for k, v in sorted(single.items(), key=lambda kv: -abs(kv[1] - 0.5))))
