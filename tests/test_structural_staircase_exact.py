from research_chains.structural_staircase import (
    staircase_block_mask, staircase_selected_mask, staircase_radius,
    staircase_exact_prefix_dimension,
)


def test_designated_blocks_have_zero_radius():
    for r in range(1,5):
        for t in range(r):
            assert staircase_radius(r, staircase_selected_mask(r,t)) == 0.0


def test_exact_chi_equals_r_small():
    for r in range(1,5):
        row=staircase_exact_prefix_dimension(r,verify_milp=True)
        assert row['dimension']==r
        assert row['dp_milp_agree']
        assert row['all_designated_unique']
        assert row['designated_pairwise_incomparable']
