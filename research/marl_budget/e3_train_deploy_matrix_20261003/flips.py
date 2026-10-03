"""(4) Bansal-style flips from the existing action-level probes (development episodes 901-904 x 8/16, teacher A_0.25 labels).
NFR = P(Z acceptable AND receiver not) = negative flip vs compiled silence; PFR = P(Z not AND receiver acceptable).
Each cell is the receiver's OWN closed loop under that channel (states differ across channels)."""
import json, numpy as np
from pathlib import Path
M = Path('/Users/phanan/cig-amf-main/research/marl_budget')
rng = np.random.default_rng(0)
def sb(v, B=20000):
    v = np.asarray(v); return np.percentile(v[rng.integers(0, len(v), (B, len(v)))].mean(1), [2.5, 97.5])
def stats(paths):
    out = []
    for p in paths:
        z = np.load(p); zok, ps = z['zok'].astype(bool), z['protoS'].astype(bool)
        out.append((ps.mean(), zok.mean(), (zok & ~ps).mean(), (~zok & ps).mean(), len(ps)))
    return np.array(out)
cells = [('3x3', 'relay6Cage_st (iid-trained)', K, [M / f'e3_negflip_20261001/s{s}_K{K}/flags.npz' for s in range(10)]) for K in (1, 2, 3, 0)]
cells += [('3x3', 'relayCK1_st (K1-trained)', 1, [M / f'e3_train_match_20261001/NF_s{s}_K1/flags.npz' for s in range(5)])]
cells += [('3x3', 'relay6Cage_st s0-4 only', 1, [M / f'e3_negflip_20261001/s{s}_K1/flags.npz' for s in range(5)])]
cells += [('3x3', f'{f} (congestion-order iid-trained)', 1, [M / f'e3_cross_student_20261001/{f}_s{s}/flags.npz' for s in range(10) if (M / f'e3_cross_student_20261001/{f}_s{s}/flags.npz').exists()]) for f in ('relay6_st', 'relay6Clow_st')]
cells += [('4x4', 'relayCage_st (iid-trained)', c, [M / f'e3_g4_constk_20261001/NF_s{s}_{c}/flags.npz' for s in range(10)]) for c in ('const1', 'const2', 'const3', 'iid', 'low')]
KN = {0: 'iid', 1: 'K1', 2: 'K2', 3: 'K3'}
for grid, rec, K, paths in cells:
    A = stats(paths); n = len(paths)
    lo, hi = sb(A[:, 2]); l2, h2 = sb(A[:, 3] - A[:, 2])
    print(f'{grid} {rec:38s} {KN.get(K, K):6s} n={n} steps/seed {int(A[0, 4])} | acc {A[:, 0].mean():.3f}  Z acc {A[:, 1].mean():.3f} | NFR {A[:, 2].mean():.4f} [{lo:.4f},{hi:.4f}] | PFR {A[:, 3].mean():.4f} | '
          f'PFR-NFR {np.mean(A[:, 3] - A[:, 2]):+.4f} [{l2:+.4f},{h2:+.4f}] (seeds <0: {(A[:, 3] - A[:, 2] < 0).sum()}/{n})')
# decision accuracy (A_0.25) on own closed loop at K1 vs iid from the age-response probes (acc_actual), seeds 0-3
print('\nage-response probes: receiver accuracy acc_actual on its own closed-loop states (dev episodes), K1 vs iid')
for name, d in (('relay6Cage_st', 'e3_age_response_20261001'), ('relayCK1_st', 'e3_age_response_shift_20261001/relayCK1'), ('relayMIX_st', 'e3_regime_id_20261002')):
    a1 = json.load(open(M / d / 'age_response_K1.json')); a0 = json.load(open(M / d / 'age_response_K0.json'))
    S = sorted(set(a1) & set(a0), key=int); v1 = np.array([a1[s]['acc_actual'] for s in S]); v0 = np.array([a0[s]['acc_actual'] for s in S])
    print(f'  {name:14s} seeds {S}: K1 {v1.mean():.3f} | iid {v0.mean():.3f} | iid - K1 {np.mean(v0 - v1):+.3f} (seeds <0: {(v0 - v1 < 0).sum()}/{len(S)})')
# parity: age-response acc_actual vs negflip protoS on the same receiver/channel/seed
a1 = json.load(open(M / 'e3_age_response_20261001/age_response_K1.json'))
print('  parity relay6Cage K1 acc_actual vs negflip protoS:', [round(a1[str(s)]['acc_actual'] - float(np.load(M / f'e3_negflip_20261001/s{s}_K1/flags.npz')['protoS'].mean()), 4) for s in range(4)])
a1 = json.load(open(M / 'e3_age_response_shift_20261001/relayCK1/age_response_K1.json'))
print('  parity relayCK1 K1 acc_actual vs NF protoS:', [round(a1[str(s)]['acc_actual'] - float(np.load(M / f'e3_train_match_20261001/NF_s{s}_K1/flags.npz')['protoS'].mean()), 4) for s in range(4)])
