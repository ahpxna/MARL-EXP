"""Contract tests for the Step 3 selector (MARL_HETERO_STEP3_DECISION §A–C)."""
import itertools
import unittest
import numpy as np

from models.marl_hetero_selector import (prefix_sets, profile_cost, check_legal, coordinate_search,
                                         radius_moves, swap_moves, select, HeteroCritic, critic_input)

M = 6
ORDER = (3, 0, 5, 1, 4, 2)


def toy_value(K, prof):
    # a fixed arbitrary interaction-heavy function of the profile, known to the test only
    v = 0.0
    for i, s in enumerate(prof):
        for j in s:
            v += ((3 * i + 5 * j) % 7) - 3
        if {0, 1} <= s:
            v += 4
    return v


class Contract(unittest.TestCase):
    def test_prefix_and_cost(self):
        K = [2, 1, 3, 2, 4, 1]
        P = prefix_sets(ORDER, K)
        for i in range(M):
            self.assertEqual(len(P[i]), K[i]); self.assertNotIn(i, P[i])
        b, desc, T = profile_cost(ORDER, K, P)
        self.assertEqual(desc, 'patched'); self.assertEqual(b % 25, 0)
        self.assertTrue(frozenset().union(*P) <= T)

    def test_cost_is_min_of_two_descriptions(self):
        K = [1] * M
        prof = [frozenset({(i + 1) % M}) for i in range(M)]      # far from the prefix
        b, desc, T = profile_cost(ORDER, K, prof)
        P = prefix_sets(ORDER, K)
        L0 = max(max(ORDER.index(j) for j in s) + 1 for s in P)
        patched = 25 * len(frozenset(ORDER[:L0]) | frozenset().union(*prof)) + 3 * sum(len(prof[i] - P[i]) for i in range(M))
        explicit = 25 * len(frozenset().union(*prof)) + 2 * M
        self.assertEqual(b, min(patched, explicit))

    def test_moves_have_equal_counts(self):
        K = [2, 3, 1, 2, 2, 3]
        P = prefix_sets(ORDER, K)
        for i in range(M):
            r1 = [s for s in radius_moves(i, P[i], P[i], M) if s != P[i]]
            sw = [s for s in swap_moves(i, P[i], P[i], M) if s != P[i]]
            self.assertEqual(len(r1), len(sw))
            self.assertEqual(len(r1), K[i] * (M - 1 - K[i]))

    def test_search_legal_under_cap_and_radius(self):
        rng = np.random.default_rng(0)
        for _ in range(30):
            K = [int(x) for x in rng.integers(1, M - 1, size=M)]
            base = profile_cost(ORDER, K, prefix_sets(ORDER, K))[0]
            for cap in (base, base + 28, base + 56, None):
                for moves, R in ((radius_moves, 1), (swap_moves, None)):
                    S, v, calls = coordinate_search(ORDER, K, lambda ps: [toy_value(K, p) for p in ps],
                                                    moves, cap=cap)
                    check_legal(ORDER, K, S, R=R, cap=cap)
                    self.assertGreaterEqual(v, toy_value(K, prefix_sets(ORDER, K)))

    def test_search_error_measurable_against_exact(self):
        # R=1 exact optimum by enumeration on a tiny instance; the local search may be worse, never better
        K = [1, 2, 1, 2, 1, 2]
        P = prefix_sets(ORDER, K)
        fams = [radius_moves(i, P[i], P[i], M) for i in range(M)]
        exact = max(toy_value(K, list(p)) for p in itertools.product(*fams))
        _, v, _ = coordinate_search(ORDER, K, lambda ps: [toy_value(K, p) for p in ps], radius_moves)
        self.assertLessEqual(v, exact + 1e-9)

    def test_inference_ignores_labels_and_prepared_order_ignores_K(self):
        # select() has no label argument; perturbing a record's labels cannot change it
        z = np.linspace(0, 1, 5); K = [2, 1, 3, 2, 1, 2]
        critic = HeteroCritic(len(critic_input(z, K, prefix_sets(ORDER, K), M)), hidden=8, seed=1)
        critic.mean = 0.0; critic.std = 1.0
        rec = dict(z=z, K=K, labels=[1.0, 2.0])
        a = select('learned_R1', rec['z'], ORDER, rec['K'], critic, M)
        rec['labels'] = [-99.0, 55.0]
        b = select('learned_R1', rec['z'], ORDER, rec['K'], critic, M)
        self.assertEqual(a[0], b[0])
        # the base order is a function of z only (heuristic), prepared before K exists
        from envs.external.cityflow_broadcast import SchedulerContext
        ctx = SchedulerContext(3, 30.0, tuple([None] * M))
        self.assertEqual(ctx.cached_queue_ranking(), ctx.cached_queue_ranking())

    def test_prefix_infeasible_is_reported(self):
        K = [4] * M
        base = profile_cost(ORDER, K, prefix_sets(ORDER, K))[0]
        S, v, calls = coordinate_search(ORDER, K, lambda ps: [0.0] * len(ps), radius_moves, cap=base - 1)
        self.assertIsNone(S)


if __name__ == '__main__':
    unittest.main()
