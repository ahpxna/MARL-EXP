import numpy as np
from research_chains.d6_contrast_rank import (
    generated_rank_one_world, decision_diagnostics, delta_square,
    product_response, interaction_profile_matrices,
)


def test_generated_rank_one_families_are_rank_one():
    rng=np.random.default_rng(123)
    for family in ('B1_pairwise','Bproduct','B2_multiaffine'):
        F,q,_=generated_rank_one_world(rng,family=family,m=4,K=3,reference_mode='rational')
        d=decision_diagnostics(F,q,rank_tol=1e-8)
        assert d['rank_one']['all_coordinates_rank_one']
        assert d['rank_one']['max_rank_one_tail_l2'] < 1e-8


def test_profile_cycle_geometry_matches_delta_on_small_world():
    rng=np.random.default_rng(7)
    F,q,_=generated_rank_one_world(rng,family='B2_multiaffine',m=4,K=3,reference_mode='uniform')
    mats=interaction_profile_matrices(F,q)
    # Max context variation of profile differences equals delta_square.
    best=0.0
    for M in mats:
        for u in range(M.shape[0]):
            for v in range(u+1,M.shape[0]):
                z=M[u]-M[v]
                best=max(best,float(z.max()-z.min()))
    assert abs(best-delta_square(F)) < 1e-10


def test_product_response_point_reference_matches_anchor_slices():
    rng=np.random.default_rng(9)
    F,q,_=generated_rank_one_world(rng,family='B1_pairwise',m=4,K=3,reference_mode='point0')
    Q=product_response(F,q)
    for i in range(4):
        for u in range(3):
            a=[0,0,0,0]; a[i]=u
            assert abs(Q[i,u]-F[tuple(a)]) < 1e-10
