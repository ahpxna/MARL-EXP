import unittest
from envs.external.cityflow_budgeted import BudgetTraceSpec, canonical_view_bytes
from envs.external.cityflow_broadcast import BroadcastCityFlowEnv
from models.marl_screening import no_oracle_access, headroom
from scripts.MARL_cheap_screen import joint_table, fingerprint
from tests.test_cityflow_budgeted import _EngineDouble, star_roadnet


def env(k=2, R=None, perturb=None, mode='oracle'):
    roadnet=star_roadnet()
    e=BroadcastCityFlowEnv(_EngineDouble(roadnet, perturb), roadnet,
        budget_spec=BudgetTraceSpec(kind='fixed',k=k), R=R,
        n_decisions=3, action_interval=2, mode=mode)
    e.reset()
    return e


class BroadcastScreenTest(unittest.TestCase):
    def test_global_cardinality_and_bytes(self):
        e=env(k=2,R=1)
        e.commit_global_ranking((0,1,2,3)); self.assertEqual(e.reveal_budget(),2)
        with self.assertRaises(ValueError): e.submit_broadcast((2,3))
        with self.assertRaises(ValueError): e.submit_broadcast((0,))
        e.submit_broadcast((0,2)); views=e.transmit()
        for i,v in views.items():
            self.assertEqual({x.sender for x in v.inbox}, {0,2}-{i})
        self.assertEqual(e._comm_record['payload_bytes'],50)
        self.assertEqual(e._comm_record['messages'],2)
        self.assertEqual(e._comm_record['request_bytes'],5)
        self.assertEqual(e.check_access_invariants(views),[])
        _,_,rec=e.step({i:e.public_topology(i).valid_phases[0] for i in views})
        self.assertEqual(rec['revisions'],1)
        self.assertEqual(e.episode_summary()['messages'],2)

    def test_scheduler_cannot_see_unpaid_fresh_payload(self):
        base=env(k=1)
        lane=base._lanes[1][next(s for s,x in enumerate(base._lanes[1]) if x)][0]
        changed=env(k=1,perturb={(lane,0):100})
        self.assertEqual(base.scheduler_context(),changed.scheduler_context())
        for e in (base,changed):
            e.commit_global_ranking((0,1,2,3)); e.reveal_budget()
        # Receiver 0 cannot see the unselected sender's fresh count either.
        a=base.counterfactual_broadcast_views((2,))[0]
        b=changed.counterfactual_broadcast_views((2,))[0]
        self.assertEqual(canonical_view_bytes(a),canonical_view_bytes(b))
        # Positive control: selected sender changes the views AND scheduler context.
        a=base.counterfactual_broadcast_views((1,))[0]
        b=changed.counterfactual_broadcast_views((1,))[0]
        self.assertNotEqual(canonical_view_bytes(a),canonical_view_bytes(b))
        for e in (base,changed): e.submit_broadcast((1,)); e.transmit()
        self.assertNotEqual(base.scheduler_context(),changed.scheduler_context())

    def test_all_receivers_change_under_same_subset_and_cf_matches_live(self):
        e=env(k=1); e.commit_global_ranking((0,1,2,3)); e.reveal_budget()
        cf=e.counterfactual_broadcast_views((1,))
        for i,v in cf.items(): self.assertEqual({x.sender for x in v.inbox},{1}-{i})
        # Actor may inspect stage, budget and final-set, so CFs must say post-transmit.
        def actor(i,v):
            self.assertEqual(v.stage,'act')
            return e.public_topology(i).valid_phases[len(v.inbox)%2]
        predicted={i:actor(i,v) for i,v in cf.items()}
        e.submit_broadcast((1,)); real=e.transmit()
        self.assertEqual(predicted,{i:actor(i,v) for i,v in real.items()})

    def test_oracle_guard_actually_fails(self):
        e=env(); e.commit_global_ranking((0,1,2,3)); e.reveal_budget()
        with self.assertRaises(AssertionError):
            with no_oracle_access(e): e.counterfactual_broadcast_views((0,1))
        deploy=env(mode='deploy'); deploy.commit_global_ranking((0,1,2,3)); deploy.reveal_budget()
        with self.assertRaises(PermissionError): deploy.counterfactual_broadcast_views((0,1))

    def test_whole_table_preserves_live_state_and_keeps_zero_gaps(self):
        e=env(); e.commit_global_ranking((0,1,2,3)); e.reveal_budget()
        before=fingerprint(e)
        def actor(i,v): return e.public_topology(i).valid_phases[len(v.inbox)%2]
        values,actions,n=joint_table(e,actor,1)
        self.assertEqual(len(values),16); self.assertEqual(len(actions),16)
        self.assertEqual(before,fingerprint(e)); self.assertGreater(n,1)
        rows=headroom([0.0]*16,(0,1,2,3))
        self.assertEqual(len(rows),3)
        self.assertTrue(all(r['repair_gain']==[0,0,0] for r in rows))

    def test_known_nontrivial_headroom(self):
        f=[0.0]*16; f[12]=10.0
        row=headroom(f,(0,1,2,3))[1]
        self.assertEqual(row['regret'],[10,10,0])
        self.assertEqual(row['repair_gain'],[0,0,10])


if __name__=='__main__': unittest.main()
