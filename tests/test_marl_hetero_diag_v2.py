"""The anchored, prefix-favouring selection rule of diag v2 (audit §1 synthetic case)."""
import unittest
import numpy as np

from scripts.MARL_hetero_diag_train_v2 import anchor, choose


def group(delta):
    n = len(delta)
    return dict(ip=n - 1, b0=100.0, cost=np.array([128.0] * (n - 1) + [100.0]), r1=np.array([True] * n),
                delta=np.asarray(delta, float))


class AnchoredSelection(unittest.TestCase):
    def test_audit_tie_case_keeps_prefix(self):
        g = group([-5.0, 0.0])                        # [edit, prefix]
        a = anchor(g, np.array([0.2, 0.2]))           # tied predictions
        self.assertEqual(choose(g, a, 28, True, 0.0), g['ip'])

    def test_constant_shift_does_not_change_decision(self):
        g = group([-5.0, 0.0])
        for shift in (-3.0, 0.0, 7.5):
            a = anchor(g, np.array([-0.1, -0.2]) + shift)   # edit predicted better by 0.1
            self.assertEqual(choose(g, a, 28, True, 0.0), 0)
            self.assertEqual(choose(g, a, 28, True, 0.2), g['ip'])   # below the threshold

    def test_never_edit_and_cap(self):
        g = group([3.0, 0.0])
        a = anchor(g, np.array([1.0, 0.0]))
        self.assertEqual(choose(g, a, 28, True, np.inf), g['ip'])
        self.assertEqual(choose(g, a, 0, True, 0.0), g['ip'])      # the edit costs +28 B


if __name__ == '__main__':
    unittest.main()
