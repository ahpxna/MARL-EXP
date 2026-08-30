import inspect
import unittest
import run_experiment
from models.crossfit_aipw import CrossFittedConditionalAIPW

class LegacySemanticHardeningTests(unittest.TestCase):
    def test_crossfit_diagnostics_declare_natural_history_target(self):
        est=CrossFittedConditionalAIPW(2)
        self.assertEqual(est.history_target,'natural_history')

    def test_unavailable_metrics_are_not_encoded_as_zero_in_h1_aggregator(self):
        source=inspect.getsource(run_experiment.run_tiny_task)
        self.assertIn('"unavailable"',source)
        self.assertIn('summary[f"{key}_mean"] = None',source)

    def test_dr_exercised_has_literal_semantics(self):
        source=inspect.getsource(run_experiment._evaluate_h1_exact_protocol)
        self.assertIn('"dr_estimator_applied": bool(dr_requested and dr_rows > 0)',source)
        self.assertIn('"dr_exercised": bool(dr_requested and dr_rows > 0)',source)
        self.assertIn('"dr_integrity_gate_pass": bool((not dr_requested) or dr_rows > 0)',source)

if __name__=='__main__': unittest.main()
