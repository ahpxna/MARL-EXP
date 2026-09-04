import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]

def test_current_plan_has_exactly_six_reports():
    plan=json.loads((ROOT/'config/CURRENT_SIX_REPORT_TEST_PLAN.json').read_text())
    assert set(plan['reports'])=={'MASTER','FUNCTIONAL','SUPPORT','STRUCTURAL','D6','QUERY'}


def test_current_registry_contains_new_live_targets_and_marks_old_d6_historical():
    data=json.loads((ROOT/'config/PROPOSAL_EXPERIMENT_REGISTRY.json').read_text())
    by={x['proposal_id']:x for x in data['items']}
    for pid in ('D6.CONTRAST_RANK_B1','D6.CONTRAST_RANK_BPRODUCT','D6.CONTRAST_RANK_B2','D6.CONTRAST_RANK_B3','STRUCTURAL.STAIRCASE_EXACT_CHI','PORTFOLIO.CURRENT_SIX_REPORT_SUITE'):
        assert by[pid]['status']=='ACTIVE'
    for pid in ('D6.S2','D6.S2_ADVERSARIAL','D6.HALF_FACTOR_EXACT','D6.HALF_FACTOR_OPTIMIZER'):
        assert by[pid]['status']=='HISTORICAL_FALSIFIED_GENERAL_LAW'
