import copy
import unittest
import numpy as np
from research_chains.oracle import CloneStateJointOracle
from research_chains.estimation import standardize_response_bank, validate_estimator_target
from research_chains.contracts import HistoryTargetKind

class ToyEnv:
    n_agents=3
    def __init__(self): self.state={'t':0}; self.last_actions=[0,0,0]
    def clone_state(self): return copy.deepcopy(self.state)
    def restore_state(self,s): self.state=copy.deepcopy(s)
    def step(self,actions):
        self.last_actions=list(actions); self.state['t']+=1
        rewards=[float(actions[1]-actions[2]),float(actions[0]+actions[2]),float(actions[0]-actions[1])]
        return [None]*3,rewards,False,{}


class DictActionToyEnv(ToyEnv):
    def __init__(self):
        super().__init__()
        self.last_actions={0:0,1:0,2:0}
    def step(self,actions):
        self.last_actions={idx:int(action) for idx,action in enumerate(actions)}
        self.state['t']+=1
        rewards=[float(actions[1]-actions[2]),float(actions[0]+actions[2]),float(actions[0]-actions[1])]
        return [None]*3,rewards,False,{}

class NewChainOracleAdapterTests(unittest.TestCase):
    def test_clone_state_joint_oracle_restores_and_enumerates(self):
        env=ToyEnv(); snap=env.clone_state(); oracle=CloneStateJointOracle(env,snapshot=snap,outcome_agent=0,baseline_actions=[0,0,0])
        table=oracle.response_table([1,2],[[0,1],[0,1]])
        self.assertEqual(len(table),4)
        self.assertEqual(env.state,snap)
        self.assertEqual(table[(1,0)],1.0)
        self.assertEqual(table[(0,1)],-1.0)
        support=oracle.feasible_support([1,2],[[0,1],[0,1]])
        self.assertEqual(len(support.omega),4)

    def test_mapping_last_actions_are_read_by_agent_id_not_dict_key_iteration(self):
        env=DictActionToyEnv(); snap=env.clone_state(); oracle=CloneStateJointOracle(env,snapshot=snap,outcome_agent=0,baseline_actions=[0,0,0])
        rec=oracle.evaluate([1,2],[1,0])
        self.assertTrue(rec.execution_verified)
        self.assertEqual(rec.executed_joint_actions,(0,1,0))
        self.assertEqual(rec.requested_joint_actions,(0,1,0))

    def test_frozen_standardization_is_explicit(self):
        mu=np.array([[0.,2.],[2.,4.]])
        q=standardize_response_bank(mu,[.25,.75])
        self.assertTrue(np.allclose(q,[1.5,3.5]))
        self.assertEqual(validate_estimator_target(HistoryTargetKind.FROZEN_STANDARDIZED),'direct_history_level_mu_then_frozen_standardization')
        with self.assertRaises(ValueError): validate_estimator_target(HistoryTargetKind.TRANSPORTED)

if __name__=='__main__': unittest.main()
