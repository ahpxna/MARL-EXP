"""Information-access checks for the receiver-cache mirror (MARL_SCOPE_AFTER_CHEAP_TESTS)."""
import unittest
from dataclasses import dataclass

from models.marl_receiver_mirror import ReceiverMirror


@dataclass(frozen=True)
class P:
    sender: int
    measured_at: int
    phase: int = 0
    phase_elapsed: int = 0
    vehicles: tuple = (0, 0, 0, 0)
    waiting: tuple = (0, 0, 0, 0)


class MirrorTests(unittest.TestCase):
    def test_unselected_receiver_keeps_old_packet(self):
        mir = ReceiverMirror(3)
        old = P(2, 10, waiting=(1, 0, 0, 0)); new = P(2, 20, waiting=(9, 0, 0, 0))
        mir.update(0, {2: old}, [[2], [2], []])
        mir.update(1, {2: new}, [[2], [], []])          # only receiver 0 decodes the new packet
        self.assertEqual(mir.entry(0, 2)[0], new)
        self.assertEqual(mir.entry(1, 2)[0], old)      # receiver 1 still holds the old version
        self.assertIsNone(mir.entry(2, 0))

    def test_reset_clears(self):
        mir = ReceiverMirror(2)
        mir.update(0, {1: P(1, 5)}, [[1], []])
        mir.reset()
        self.assertIsNone(mir.entry(0, 1))
        self.assertEqual(mir.features(10.0), [0.0] * 12 * 2)

    def test_same_broadcaster_cache_different_receiver_caches(self):
        # both histories end with the scheduler's latest packet of sender 2 = p2b, but receiver 1
        # decoded p2b in history A and only p2a in history B
        p2a, p2b = P(2, 10, waiting=(3, 0, 0, 0)), P(2, 20, waiting=(7, 0, 0, 0))
        A = ReceiverMirror(3); B = ReceiverMirror(3)
        A.update(0, {2: p2a}, [[2], [2], []]); A.update(1, {2: p2b}, [[2], [2], []])
        B.update(0, {2: p2a}, [[2], [2], []]); B.update(1, {2: p2b}, [[2], [], []])
        self.assertNotEqual(A.features(30.0), B.features(30.0))

    def test_cannot_decode_untransmitted(self):
        mir = ReceiverMirror(2)
        with self.assertRaises(ValueError):
            mir.update(0, {}, [[1], []])

    def test_features_use_only_mirror_and_time(self):
        mir = ReceiverMirror(2)
        mir.update(0, {1: P(1, 5, waiting=(2, 0, 0, 0))}, [[1], []])
        f1 = mir.features(15.0)
        self.assertEqual(f1[:2], [1.0, 0.1])            # present, age (15-5)/100
        self.assertEqual(f1[12:], [0.0] * 12)           # receiver 1 never decoded sender 0


if __name__ == '__main__':
    unittest.main()
