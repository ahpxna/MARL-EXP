import unittest
import numpy as np

from run_experiment import _pair_replay_support_diagnostics
from research_chains.support import SupportModel


class TestChainV4Semantics(unittest.TestCase):
    def test_pair_replay_support_is_not_policy_entropy(self):
        rows=[]
        for ep in range(3):
            for a in (0,1):
                rows.append({
                    "ego_id":0,"neighbor_id":1,"episode_id":ep,
                    "target_action_executed":a,"observed_action_j":a,
                    "valid_action_mask":np.asarray([True,True]),
                    "behaviour_prob_j":0.5,
                })
        out=_pair_replay_support_diagnostics(rows,2,min_action_count=2,min_action_ess=2.0)
        self.assertEqual(out["poor_pair_count"],0)
        self.assertEqual(out["support_scope"],"pair_aggregated_replay_over_typed_rows_not_state_conditional")

    def test_projected_rectangularity_definition(self):
        omega={(0,0)}
        p0={x[0] for x in omega}; p1={x[1] for x in omega}
        self.assertEqual(omega,{(a,b) for a in p0 for b in p1})


if __name__ == '__main__':
    unittest.main()
