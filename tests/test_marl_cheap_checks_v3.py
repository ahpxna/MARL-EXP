"""Held-out-budget labels must not influence v3 training (audit §6), with a positive control."""
import unittest
import numpy as np
import torch

from scripts.MARL_cheap_checks_v3_train import train_one, centred_targets
from models.marl_screening import layer_masks


def _data(m=5, n=24, d=7, seed=0):
    rng = np.random.default_rng(seed)
    X = rng.normal(size=(n, d)).astype(np.float32)
    Y = rng.normal(size=(n, 1 << m)) * 10
    splits = {'train': list(range(0, 12)), 'val': list(range(12, 18)), 'test': list(range(18, 24))}
    return X, Y, splits


def _states(X, Y, splits, m, K_tr, use_score):
    torch.set_num_threads(1)
    nets, _, _, info = train_one(X, Y, splits, m, K_tr, seed=3, epochs=12, hidden=8, use_score=use_score)
    return {k: {n: t.clone() for n, t in net.state_dict().items()} for k, net in nets.items()}, info


def _equal(a, b):
    return all(torch.equal(a[k][n], b[k][n]) for k in a for n in a[k])


class HeldOutBudgetIsolation(unittest.TestCase):
    def test_excluded_labels_do_not_matter(self):
        m, K_tr = 5, [2, 4]
        X, Y, splits = _data(m)
        base, info = _states(X, Y, splits, m, K_tr, use_score=False)
        Y2 = Y.copy()
        for k in [0, 1, 3, 5]:
            Y2[:, layer_masks(m, k) if k in range(1, m) else [0 if k == 0 else (1 << m) - 1]] += 1000.0
        pert, info2 = _states(X, Y2, splits, m, K_tr, use_score=False)
        self.assertEqual(info['scale'], info2['scale'])
        self.assertTrue(_equal(base, pert))

    def test_positive_control_trained_label_changes_training(self):
        m, K_tr = 5, [2, 4]
        X, Y, splits = _data(m)
        base, _ = _states(X, Y, splits, m, K_tr, use_score=False)
        Y2 = Y.copy()
        Y2[splits['train'][0], layer_masks(m, 2)[0]] += 50.0
        pert, _ = _states(X, Y2, splits, m, K_tr, use_score=False)
        self.assertFalse(_equal(base, pert))

    def test_centred_targets_only_trained_sizes(self):
        m = 4
        Y = np.arange(2 * 16, dtype=float).reshape(2, 16)
        T = centred_targets(Y, m, [2])
        ix = layer_masks(m, 2)
        self.assertTrue(np.allclose(T[:, ix].mean(1), 0))
        others = [s for s in range(16) if s not in ix]
        self.assertTrue(np.isnan(T[:, others]).all())


if __name__ == '__main__':
    unittest.main()
