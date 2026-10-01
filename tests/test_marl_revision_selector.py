import itertools
import math
import unittest
from models.marl_revision_selector import candidate_count, reachable_sets, select_revision, complete_table_bounds


class RevisionSelectorTest(unittest.TestCase):
    def test_exact_family_all_small_budgets(self):
        # Independent definition by filtering ALL k-sets, including R=0 and saturation.
        for m in range(1, 9):
            ranking = tuple(range(m-1, -1, -1))
            for k in range(m+1):
                prefix = frozenset(ranking[:k])
                for r in range(4):
                    got = list(reachable_sets(ranking, k, r))
                    expected = {frozenset(s) for s in itertools.combinations(ranking, k)
                                if len(set(s)-prefix) <= r}
                    self.assertEqual(set(got), expected)
                    self.assertEqual(len(got), len(expected))
                    self.assertEqual(len(got), candidate_count(m, k, r))

    def test_interaction_can_require_two_replacements(self):
        f = lambda s: 10.0 if s == frozenset([30, 40]) else 0.0
        one = select_revision([10, 20, 30, 40], 2, 1, f)
        two = select_revision([10, 20, 30, 40], 2, 2, f)
        self.assertEqual(one.selected, frozenset([10, 20]))
        self.assertEqual(two.selected, frozenset([30, 40]))
        self.assertEqual(two.replacements, 2)
        self.assertEqual(two.predicted_value, 10.0)

    def test_cap_and_invalid_inputs_fail_before_evaluation(self):
        calls = []
        with self.assertRaises(ValueError):
            select_revision(range(10), 5, 2, lambda s: calls.append(s), max_candidates=3)
        self.assertEqual(calls, [])
        for ranking, k, r in [([0, 0], 1, 1), ([0], 2, 1), ([0], 1, -1)]:
            with self.assertRaises(ValueError):
                select_revision(ranking, k, r, lambda s: 0)
        with self.assertRaises(ValueError):
            select_revision([0, 1], 1, 1, lambda s: math.nan)

    def test_conditional_bounds_cover_hidden_high_order_interaction(self):
        items = [0, 1, 2]
        sets = [frozenset(c) for n in range(4) for c in itertools.combinations(items, n)]
        true = {s: float(sum(i+1 for i in s) + (4 if len(s)==3 else 0)) for s in sets}
        estimates = {s: v + (0.2 if len(s)%2 else -0.2) for s,v in true.items()}
        radii = {s: 0.2 for s in sets}
        scores = {i: float(i+1) for i in items}
        b = complete_table_bounds(items, estimates, radii, scores)
        self.assertGreaterEqual(b['delta_upper'] + 1e-12, 4.0)
        for i in items:
            for A in sets:
                if i not in A:
                    self.assertLessEqual(abs(true[A|{i}]-true[A]-scores[i]),
                                         b['score_residual_upper']+1e-12)
        del estimates[frozenset(items)]
        with self.assertRaises(ValueError):
            complete_table_bounds(items, estimates, radii, scores)


if __name__ == '__main__':
    unittest.main()
