import json
from pathlib import Path
import tempfile
import unittest

import numpy as np

from research_chains.functionals import (
    direction_sign_boundary_diagnostics,
    functional_boundary_diagnostics,
    relation_ranking_diagnostics,
)
from research_chains.h1_fixed_panel import load_fixed_panel, save_fixed_panel


class V7FunctionalGeometryTests(unittest.TestCase):
    def test_local_extrema_stability_does_not_imply_global_rank_stability(self):
        q1 = np.array([0.0, 1.00])
        h1 = np.array([0.01, 0.99])
        q2 = np.array([0.0, 0.99])
        h2 = np.array([-0.01, 1.00])
        b1 = functional_boundary_diagnostics(h1, q1)
        b2 = functional_boundary_diagnostics(h2, q2)
        self.assertEqual(b1["extrema_stability_certified"], 1)
        self.assertEqual(b2["extrema_stability_certified"], 1)
        self.assertEqual(b1["extrema_stability_violation"], 0)
        self.assertEqual(b2["extrema_stability_violation"], 0)

        learned = [np.ptp(h1), np.ptp(h2)]
        oracle = [np.ptp(q1), np.ptp(q2)]
        diag = relation_ranking_diagnostics(
            [10, 11], learned, oracle,
            [b1["q_gauge_sup_error"], b2["q_gauge_sup_error"]],
            top_k=1,
        )
        self.assertEqual(diag["capacity_topk_match"], 0)
        self.assertEqual(diag["capacity_topk_q_certified"], 0)
        self.assertGreaterEqual(diag["lambda_topk_Q"], 1.0)

    def test_topk_q_margin_certificate_has_no_false_safe(self):
        oracle = [2.0, 1.0, 0.2]
        learned = [1.95, 1.03, 0.22]
        diag = relation_ranking_diagnostics(
            [0, 1, 2], learned, oracle, [0.03, 0.03, 0.03], top_k=1
        )
        self.assertEqual(diag["capacity_topk_q_certified"], 1)
        self.assertEqual(diag["capacity_topk_match"], 1)
        self.assertEqual(diag["capacity_topk_q_certified_violation"], 0)
        self.assertEqual(diag["capacity_q_error_bound_violation_count"], 0)

    def test_direction_sign_margin_certificate(self):
        q = np.array([0.0, 1.0])
        qhat = np.array([0.1, 0.9])
        diag = direction_sign_boundary_diagnostics(
            qhat, q, np.array([-0.5, 0.5])
        )
        self.assertEqual(diag["direction_sign_certified"], 1)
        self.assertEqual(diag["direction_sign_violation"], 0)
        self.assertLess(diag["lambda_D"], 1.0)


class V7FixedPanelArtifactTests(unittest.TestCase):
    def _step(self):
        return {
            "obs_all": [np.array([1.0, 2.0]), np.array([3.0, 4.0])],
            "actions": [0, 1],
            "rewards": [0.5, -0.2],
            "proxy_context_excluding": {0: {1: (np.array([1.0]), np.array([2.0]))}},
            "proxy_context_blocks": {0: {"neighbor_ids": np.array([1]), "items": np.array([[1.0, 2.0]])}},
            "belief_summary_cache": {0: np.array([0.1, 0.2])},
            "geom_snapshot": {"positions": np.array([[1, 2], [3, 4]])},
            "behaviour_probs": np.array([[0.5, 0.5], [0.4, 0.6]]),
            "policy_probs": np.array([[0.5, 0.5], [0.4, 0.6]]),
            "h1_target_policy_probs": np.array([[0.5, 0.5], [0.4, 0.6]]),
            "valid_action_masks": np.array([[True, True], [True, True]]),
            "env_snapshot_before_step": {
                "positions": [[1, 2], [3, 4]],
                "rng_state": ("MT19937", np.arange(5, dtype=np.uint32), 1, 0, 0.0),
            },
        }

    def test_fixed_panel_roundtrip_and_tamper_detection(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "panel.pkl.gz"
            saved = save_fixed_panel(path, [self._step()], {"experiment_seed": 7})
            loaded = load_fixed_panel(path)
            self.assertEqual(saved["panel_fingerprint"], loaded["panel_fingerprint"])
            self.assertEqual(len(loaded["step_hashes"]), 1)
            sidecar = json.loads(Path(str(path) + ".json").read_text())
            self.assertEqual(sidecar["panel_fingerprint"], loaded["panel_fingerprint"])

            # Tamper with the compressed file; the sidecar hash must reject it.
            raw = bytearray(path.read_bytes())
            raw[-1] ^= 1
            path.write_bytes(raw)
            with self.assertRaises(Exception):
                load_fixed_panel(path)


class V7ResumeAggregationTests(unittest.TestCase):
    def _write_cell(self, root: Path, seed: int, checkpoint: int, fingerprint: str = "abc"):
        run_dir = root / "runs" / f"ep{checkpoint}" / f"seed{seed}"
        run_dir.mkdir(parents=True, exist_ok=True)
        pair = {
            "fixed_panel_fingerprint": [fingerprint],
            "fixed_panel_step_hash": [f"step-{seed}"],
            "ego_id": [0],
            "neighbor_id": [1],
            "oracle_range": [1.0],
            "oracle_signed": [0.1],
            "oracle_argmax_action": [1],
            "oracle_argmin_action": [0],
            "oracle_extrema_gap": [0.2],
            "oracle_topk_gap": [0.3],
        }
        state = {"fixed_panel_step_hash": [f"step-{seed}"], "ego_id": [0]}
        import pandas as pd
        pd.DataFrame(pair).to_csv(run_dir / "tiny_oracle_pair_rows.csv", index=False)
        pd.DataFrame(state).to_csv(run_dir / "tiny_oracle_calibration_by_state.csv", index=False)
        (run_dir / "tiny_oracle_summary.json").write_text(json.dumps({
            "v7_checkpoint_episodes": checkpoint,
            "v7_fixed_panel_fingerprint": fingerprint,
        }))
        return run_dir

    def test_discovery_backfills_complete_and_preserves_partial(self):
        from scripts.run_h1_fixed_panel_v7 import _discover_run_cells
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            complete = self._write_cell(root, 3001, 20)
            partial = root / "runs" / "ep320" / "seed3002"
            partial.mkdir(parents=True)
            (partial / "tiny_oracle_summary.json").write_text("{}")
            cells = _discover_run_cells(root)
            keyed = {(c["seed"], c["checkpoint"]): c for c in cells}
            self.assertTrue(keyed[(3001, 20)]["complete"])
            self.assertFalse(keyed[(3002, 320)]["complete"])
            self.assertTrue((complete / "v7_complete.json").is_file())

    def test_partial_grid_consistency_compares_only_available_checkpoints(self):
        from scripts.run_h1_fixed_panel_v7 import _assert_panel_consistency
        import pandas as pd
        rows = []
        for seed in [3001, 3002]:
            checkpoints = [20, 80, 320] if seed == 3001 else [20, 80]
            for checkpoint in checkpoints:
                rows.append({
                    "experiment_seed": seed,
                    "checkpoint": checkpoint,
                    "fixed_panel_fingerprint": f"fp-{seed}",
                    "fixed_panel_step_hash": f"step-{seed}",
                    "ego_id": 0,
                    "neighbor_id": 1,
                    "oracle_range": 1.0,
                    "oracle_signed": 0.1,
                    "oracle_argmax_action": 1,
                    "oracle_argmin_action": 0,
                    "oracle_extrema_gap": 0.2,
                    "oracle_topk_gap": 0.3,
                })
        result = _assert_panel_consistency(pd.DataFrame(rows))
        self.assertTrue(result["pass"])
        self.assertEqual(result["seeds"]["3001"]["completed_checkpoints"], [20, 80, 320])
        self.assertEqual(result["seeds"]["3002"]["completed_checkpoints"], [20, 80])


if __name__ == "__main__":
    unittest.main()
