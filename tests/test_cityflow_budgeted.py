"""Information-access tests for envs/external/cityflow_budgeted.py (dependency-free).

Core test: non-interference.  Two engines are identical except that one
neighbour's FRESH incoming-lane counts are perturbed at the current time.  If
that neighbour is not transmitted to agent 0, agent 0's view must be
byte-identical in both runs, at every stage.  Two controls show the test can
fail:
* positive control: when the neighbour IS transmitted, the views must differ;
* mutation control: a deliberately leaky env (a view that reads a neighbour's
  fresh sensor, as the old adapter's relation_features does) must be detected.
"""
from __future__ import annotations

import copy
import unittest

import numpy as np

from envs.external.cityflow_budgeted import (
    AgentView, BudgetTraceSpec, BudgetedCityFlowEnv, MessagePayload, PAYLOAD_BYTES, REQUEST_BYTES,
    canonical_view_bytes, decode_payload, encode_payload, generate_budget_trace, run_protocol_step,
)


def _road(rid, a, b, pa, pb, lanes=1):
    return {"id": rid, "startIntersection": a, "endIntersection": b,
            "points": [{"x": pa[0], "y": pa[1]}, {"x": pb[0], "y": pb[1]}],
            "lanes": [{"width": 3.0, "maxSpeed": 16.67}] * lanes}


def star_roadnet():
    """Centre c0 with leaves l1 (east), l2 (north), l3 (west); roads both ways; 2 lanes."""
    pos = {"c0": (0, 0), "l1": (300, 0), "l2": (0, 300), "l3": (-300, 0)}
    roads = []
    for leaf in ("l1", "l2", "l3"):
        roads.append(_road(f"r_c0_{leaf}", "c0", leaf, pos["c0"], pos[leaf], lanes=2))
        roads.append(_road(f"r_{leaf}_c0", leaf, "c0", pos[leaf], pos["c0"], lanes=2))
    inters = []
    for iid in ("c0", "l1", "l2", "l3"):
        incoming = [r["id"] for r in roads if r["endIntersection"] == iid]
        outgoing = [r["id"] for r in roads if r["startIntersection"] == iid]
        links = [{"startRoad": s, "endRoad": e} for s in incoming for e in outgoing]
        phases = [{"time": 5, "availableRoadLinks": []},
                  {"time": 30, "availableRoadLinks": list(range(len(links)))},
                  {"time": 30, "availableRoadLinks": list(range(0, len(links), 2))}]
        inters.append({"id": iid, "virtual": False, "point": {"x": pos[iid][0], "y": pos[iid][1]},
                       "roads": incoming + outgoing, "roadLinks": links,
                       "trafficLight": {"lightphases": phases}})
    return {"intersections": inters, "roads": roads}


class _EngineDouble:
    """Lane counts are a deterministic function of (lane, time) plus an optional perturbation."""

    def __init__(self, roadnet, perturb=None):
        self.lanes = [f"{r['id']}_{k}" for r in roadnet["roads"] for k in range(len(r["lanes"]))]
        self.perturb = dict(perturb or {})  # (lane, time) -> added vehicles
        self.t = 0
        self.phases = {}

    def _base(self, lane, t):
        return (sum(map(ord, lane)) * 7 + 13 * t) % 17

    def get_lane_vehicle_count(self):
        return {l: self._base(l, self.t) + self.perturb.get((l, self.t), 0) for l in self.lanes}

    def get_lane_waiting_vehicle_count(self):
        return {l: (self._base(l, self.t) + self.perturb.get((l, self.t), 0)) // 2 for l in self.lanes}

    def get_current_time(self): return float(self.t)
    def get_vehicles(self, include_waiting=False): return [f"v{self.t % 5}", f"w{self.t % 3}"]
    def get_average_travel_time(self): return 0.0
    def reset(self, seed=False): self.t = 0; self.phases = {}
    def set_tl_phase(self, iid, p): self.phases[iid] = int(p)
    def next_step(self): self.t += 1
    def snapshot(self): return copy.deepcopy((self.t, self.phases))
    def load(self, a): self.t, self.phases = copy.deepcopy(a)


def make_env(perturb=None, spec=None, R=0, mode="deploy", n_decisions=4, delay=0):
    rn = star_roadnet()
    return BudgetedCityFlowEnv(_EngineDouble(rn, perturb), rn,
                               budget_spec=spec or BudgetTraceSpec("fixed", k=1), R=R,
                               n_decisions=n_decisions, action_interval=2, delivery_delay=delay, mode=mode)


class _LeakyEnv(BudgetedCityFlowEnv):
    """MUTATION: agent views carry every neighbour's fresh sensor (the old adapter's leak)."""

    def _build_view(self, i, **kw):
        v = super()._build_view(i, **kw)
        extra = [self._sensor(j)[0] for j in self.neighbours[i]]
        leaked = np.concatenate([v.lane_vehicles] + extra, axis=1)
        leaked.setflags(write=False)
        return AgentView(**{**v.__dict__, "lane_vehicles": leaked})


def _stage_views(env, ranking0, actions=None):
    """Run one protocol step with agent 0's ranking fixed; return agent 0's views per stage."""
    out = {}
    out["rank"] = canonical_view_bytes(env.views()[0])
    rankings = {i: env.neighbours[i] for i in range(env.n_agents)}
    rankings[0] = tuple(ranking0)
    env.commit_rankings(rankings)
    out["reveal"] = canonical_view_bytes(env.views()[0])
    k = env.reveal_budget()
    out["revise"] = canonical_view_bytes(env.views()[0])
    env.submit_final_sets({i: rankings[i][:min(k[i], len(env.neighbours[i]))] for i in range(env.n_agents)})
    out["act"] = canonical_view_bytes(env.transmit()[0])
    env.step(actions or {i: env.public_topology(i).valid_phases[0] for i in range(env.n_agents)})
    return out


def _lanes_of(env, j):
    return [l for lanes in env._lanes[j] for l in lanes]


class NonInterferenceTests(unittest.TestCase):
    def _pair(self, env_cls=BudgetedCityFlowEnv, ranking0=None):
        base = make_env()
        idx = {iid: k for k, iid in enumerate(base.agent_ids)}
        c0, l2 = idx["c0"], idx["l2"]
        self.assertEqual(c0, 0)
        # Perturb l2's fresh incoming lanes at every time of step 1 (t = 2 after one step of 2 s).
        perturb = {(l, t): 5 for l in _lanes_of(base, l2) for t in range(0, 20)}
        rn = star_roadnet()
        A = env_cls(_EngineDouble(rn), rn, budget_spec=BudgetTraceSpec("fixed", k=1), R=0,
                    n_decisions=4, action_interval=2)
        B = env_cls(_EngineDouble(rn, perturb), rn, budget_spec=BudgetTraceSpec("fixed", k=1), R=0,
                    n_decisions=4, action_interval=2)
        A.reset(budget_seed=1); B.reset(budget_seed=1)
        return A, B, c0, l2

    def _differs(self, A, B, ranking0, steps=3):
        diffs = []
        for s in range(steps):
            va, vb = _stage_views(A, ranking0), _stage_views(B, ranking0)
            diffs += [(s, st) for st in va if va[st] != vb[st]]
        return diffs

    def test_nontransmitted_neighbour_fresh_obs_never_reaches_agent(self):
        A, B, c0, l2 = self._pair()
        others = [j for j in A.neighbours[c0] if j != l2]
        ranking = [others[0], l2] + others[1:]  # k = 1 -> T = {others[0]}; l2 never heard
        self.assertEqual(self._differs(A, B, ranking), [],
                         "a non-transmitted neighbour's fresh observation reached agent 0")

    def test_positive_control_transmitted_neighbour_is_seen(self):
        A, B, c0, l2 = self._pair()
        ranking = [l2] + [j for j in A.neighbours[c0] if j != l2]
        diffs = self._differs(A, B, ranking)
        self.assertIn((0, "act"), diffs, "detector blind: a transmitted change did not reach the view")
        self.assertNotIn((0, "rank"), diffs)
        self.assertNotIn((0, "revise"), diffs)

    def test_mutation_control_leaky_view_is_detected(self):
        A, B, c0, l2 = self._pair(env_cls=_LeakyEnv)
        others = [j for j in A.neighbours[c0] if j != l2]
        ranking = [others[0], l2] + others[1:]
        self.assertNotEqual(self._differs(A, B, ranking), [], "the leak detector missed a planted leak")

    def test_cache_holds_last_transmitted_value_with_age(self):
        env = make_env()
        env.reset(budget_seed=0)
        c0 = 0
        j = env.neighbours[c0][0]
        _stage_views(env, [j] + [x for x in env.neighbours[c0] if x != j])  # heard at t=0
        sent_time = 0
        other = [x for x in env.neighbours[c0] if x != j]
        _stage_views(env, other + [j])  # not heard at step 1
        v = env.views()[c0]
        e = v.message_from(j)
        self.assertIsNotNone(e)
        self.assertEqual(e.measured_at, sent_time)
        self.assertEqual(e.age, v.sim_time - sent_time)
        self.assertEqual(e.age, 4.0)
        self.assertTrue(e in v.cache and e not in v.inbox)


class ProtocolTests(unittest.TestCase):
    def test_stage_order_is_enforced(self):
        env = make_env()
        env.reset()
        with self.assertRaises(RuntimeError):
            env.reveal_budget()
        with self.assertRaises(RuntimeError):
            env.transmit()
        with self.assertRaises(RuntimeError):
            env.step({i: 1 for i in range(env.n_agents)})

    def test_budget_hidden_before_reveal(self):
        env = make_env(spec=BudgetTraceSpec("fixed", k=2))
        views = env.reset()
        self.assertTrue(all(v.budget is None for v in views.values()))
        env.commit_rankings({i: env.neighbours[i] for i in range(env.n_agents)})
        self.assertTrue(all(v.budget is None for v in env.views().values()))
        env.reveal_budget()
        self.assertTrue(all(v.budget == 2 for v in env.views().values()))

    def test_revision_bound_and_cardinality(self):
        env = make_env(spec=BudgetTraceSpec("fixed", k=2), R=1)
        env.reset()
        rk = {i: env.neighbours[i] for i in range(env.n_agents)}
        env.commit_rankings(rk)
        env.reveal_budget()
        c = rk[0]  # (1, 2, 3); prefix_2 = {1, 2}
        bad = {i: rk[i][:min(2, len(rk[i]))] for i in rk}
        bad[0] = (c[2],)  # wrong size
        with self.assertRaises(ValueError):
            env.submit_final_sets(bad)
        ok = dict(bad); ok[0] = (c[0], c[2])  # one replacement
        self.assertEqual(env.submit_final_sets(ok)[0], 1)

    def test_revision_above_R_rejected(self):
        env = make_env(spec=BudgetTraceSpec("fixed", k=2), R=0)
        env.reset()
        rk = {i: env.neighbours[i] for i in range(env.n_agents)}
        env.commit_rankings(rk); env.reveal_budget()
        fs = {i: rk[i][:min(2, len(rk[i]))] for i in rk}
        fs[0] = (rk[0][0], rk[0][2])
        with self.assertRaises(ValueError):
            env.submit_final_sets(fs)

    def test_ranking_must_be_permutation(self):
        env = make_env()
        env.reset()
        rk = {i: env.neighbours[i] for i in range(env.n_agents)}
        rk[0] = rk[0][:2]
        with self.assertRaises(ValueError):
            env.commit_rankings(rk)

    def test_bytes_accounting(self):
        env = make_env(spec=BudgetTraceSpec("fixed", k=2))
        env.reset()
        rk = {i: env.neighbours[i] for i in range(env.n_agents)}
        env.commit_rankings(rk); k = env.reveal_budget()
        env.submit_final_sets({i: rk[i][:min(k[i], len(rk[i]))] for i in rk})
        env.transmit()
        _, _, rec = env.step({i: 1 for i in range(env.n_agents)})
        n_msgs = sum(min(2, len(env.neighbours[i])) for i in range(env.n_agents))  # 2 + 1 + 1 + 1
        self.assertEqual(rec["messages"], n_msgs)
        self.assertEqual(rec["payload_bytes"], n_msgs * PAYLOAD_BYTES)
        self.assertEqual(rec["request_bytes"], n_msgs * REQUEST_BYTES)
        self.assertEqual(PAYLOAD_BYTES, 25)

    def test_invalid_action_raises(self):
        env = make_env(); env.reset()
        rk = {i: env.neighbours[i] for i in range(env.n_agents)}
        env.commit_rankings(rk); k = env.reveal_budget()
        env.submit_final_sets({i: rk[i][:min(k[i], len(rk[i]))] for i in rk}); env.transmit()
        with self.assertRaises(ValueError):
            env.step({i: 0 for i in range(env.n_agents)})  # phase 0 is the clearance phase

    def test_oracle_entry_points_forbidden_in_deploy(self):
        env = make_env(); env.reset()
        with self.assertRaises(PermissionError):
            env.oracle_payloads(0)
        with self.assertRaises(PermissionError):
            env.clone_state()

    def test_oracle_counterfactual_and_rollout_leave_state_unchanged(self):
        env = make_env(mode="oracle"); env.reset()
        rk = {i: env.neighbours[i] for i in range(env.n_agents)}
        env.commit_rankings(rk); k = env.reveal_budget()
        before = {i: canonical_view_bytes(v) for i, v in env.views().items()}
        cf = env.counterfactual_view(0, env.neighbours[0])
        self.assertEqual(len(cf.inbox), len(env.neighbours[0]))
        env.oracle_rollout_value({i: 1 for i in range(env.n_agents)}, horizon_decisions=2)
        after = {i: canonical_view_bytes(v) for i, v in env.views().items()}
        self.assertEqual(before, after)
        self.assertEqual(env.access_log["counterfactual_view"], 1)
        self.assertEqual(env.access_log["oracle_rollout"], 1)
        self.assertTrue(env.episode_summary()["oracle_access_used"])

    def test_invariants_clean_on_protocol_run(self):
        env = make_env(spec=BudgetTraceSpec("bursty", k=2, k_low=0), R=1, n_decisions=5)
        env.reset(budget_seed=3)

        class P:
            def rank(self, v, t): return v.neighbours
            def revise(self, v, r, k, R): return r[:min(k, len(r))]
            def act(self, v, t): return t.valid_phases[0]

        done = False
        while not done:
            _, done, rec = run_protocol_step(env, P())
            self.assertEqual(rec["violations"], [])

    def test_views_are_immutable_data(self):
        env = make_env(); views = env.reset()
        v = views[0]
        with self.assertRaises(ValueError):
            v.lane_vehicles[0, 0] = 99.0
        with self.assertRaises(Exception):
            v.agent = 3


class CodecAndTraceTests(unittest.TestCase):
    def test_codec_roundtrip_and_clipping(self):
        p = MessagePayload(3, 1200, 4, 17, (1, 2, 3, 70000), (0, 1, 2, 3))
        data, clipped = encode_payload(p)
        self.assertEqual(len(data), PAYLOAD_BYTES)
        self.assertEqual(clipped, 1)
        q = decode_payload(data)
        self.assertEqual(q.vehicles, (1, 2, 3, 65535))
        self.assertEqual((q.sender, q.measured_at, q.phase, q.phase_elapsed), (3, 1200, 4, 17))

    def test_traces_deterministic_and_typed(self):
        for kind in ("fixed", "drops", "bursty", "per_episode"):
            spec = BudgetTraceSpec(kind, k=3, k_low=0, p_drop=0.3)
            a = generate_budget_trace(spec, 50, 4, seed=7)
            b = generate_budget_trace(spec, 50, 4, seed=7)
            np.testing.assert_array_equal(a, b)
            self.assertEqual(a.shape, (50, 4))
            self.assertTrue((a[:, 0:1] == a).all())  # common trace across receivers
        self.assertTrue((generate_budget_trace(BudgetTraceSpec("fixed", k=2), 9, 2, 0) == 2).all())
        drops = generate_budget_trace(BudgetTraceSpec("drops", k=3, k_low=0, p_drop=0.3), 200, 1, 1)
        self.assertEqual(set(np.unique(drops)), {0, 3})
        ep = generate_budget_trace(BudgetTraceSpec("per_episode", k_choices=(1, 2)), 30, 1, 5)
        self.assertEqual(len(np.unique(ep)), 1)
        pa = generate_budget_trace(BudgetTraceSpec("bursty", k=3, per_agent=True), 100, 3, 2)
        self.assertFalse((pa[:, 0] == pa[:, 1]).all())


if __name__ == "__main__":
    unittest.main()
