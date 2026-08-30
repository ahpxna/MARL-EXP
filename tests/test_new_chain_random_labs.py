import unittest
from scripts.run_chain_bh_lab import run as run_bh
from scripts.run_chain_rp_lab import run as run_rp

class NewChainRandomLabTests(unittest.TestCase):
    def test_bh_randomized_falsification_small(self):
        result=run_bh(instances=25,seed=123)
        self.assertEqual(result['failure_count'],0,result.get('failures'))
    def test_rp_randomized_falsification_small(self):
        result=run_rp(instances=25,seed=456)
        self.assertEqual(result['failure_count'],0,result.get('failures'))

if __name__=='__main__': unittest.main()
