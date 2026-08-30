import unittest
import numpy as np
from research_chains.reference import ConditionalReferenceKernel, reference_fidelity_characterization
from scripts.run_chain_e_semantic_lab import run as run_e
from scripts.run_chain_f3_shadow_smoke import run as run_f3
from scripts.run_chain_reference_fidelity_search import run as run_ref

class NewChainExtendedTests(unittest.TestCase):
    def test_reference_fidelity_product_and_counterexample(self):
        product=ConditionalReferenceKernel.product((2,2,2),0,{0:[.5,.5],1:[.3,.7],2:[.4,.6]})
        self.assertTrue(reference_fidelity_characterization(product)['marginal_invariant'])
        rows={
            0:{(0,0,0):1.0},
            1:{(1,1,0):1.0},
        }
        conditional=ConditionalReferenceKernel(0,(2,2,2),rows)
        result=reference_fidelity_characterization(conditional)
        self.assertFalse(result['marginal_invariant'])
        self.assertIsNotNone(result['witness'])
        self.assertGreater(result['witness']['oscillation'],0.0)

    def test_reference_fidelity_search_small(self):
        self.assertEqual(run_ref(50,99)['failure_count'],0)

    def test_query_semantics_primitive_worlds(self):
        self.assertEqual(run_e()['overall_status'],'PASS')

    def test_f3_shadow_plumbing(self):
        result=run_f3()
        self.assertTrue(result['gate_pass'])
        self.assertGreater(result['target_drift'],0.0)
        self.assertEqual(result['evidence_class'],'PLUMBING_SMOKE_ONLY')

if __name__=='__main__': unittest.main()
