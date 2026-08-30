import tempfile, unittest
from pathlib import Path
from scripts.run_p11_d0_omni import collect, main
class P11D0OmniTests(unittest.TestCase):
    def test_quick_complete_exact_grid_and_cost(self):
        payload=collect(mode="quick",seeds=(7,),replicates_per_seed=2,horizon=2,burn_in=1); rows=payload["records"]
        self.assertEqual(len(rows),12); self.assertEqual({x["regime"] for x in rows},{"reset","frozen_policy","live_learning"})
        self.assertEqual({x["arm"] for x in rows},{"force_left","force_right"}); self.assertEqual({x["immediate_cost"] for x in rows},{1.0})
        self.assertTrue(all(x["action_verified"] for x in rows)); self.assertEqual(payload["d0_status"],"SMOKE_ONLY")
    def test_confirmatory_cli_fails_closed_if_underpowered(self):
        with tempfile.TemporaryDirectory() as directory:
            output=Path(directory)/"d0.json"; code=main(["--confirmatory","--seeds","0","--replicates-per-seed","2","--horizon","4","--out",str(output)])
            self.assertEqual(code,2); self.assertIn('"collection_complete": false',output.read_text())
if __name__=="__main__": unittest.main()

def test_quick_mode_reports_requested_vs_used_seeds(tmp_path):
    out = tmp_path / 'quick.json'
    rc = main(['--quick','--seeds','11','12','13','--replicates-per-seed','1','--horizon','1','--out',str(out)])
    assert rc == 0
    import json
    payload = json.loads(out.read_text())
    assert payload['requested_seeds'] == [11,12,13]
    assert payload['used_seeds'] == [11]
    assert payload['quick_uses_first_seed_only'] is True
