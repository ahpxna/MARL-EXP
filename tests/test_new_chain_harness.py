import copy
import unittest
import numpy as np

from models.crossfit_aipw import CrossFittedConditionalAIPW
from research_chains.certificates import (
    deficit_terms, exact_optimum, global_extremizability_defect,
    lp_lower_bound, quotient_sup_distance, support_bracket_regret_bound,
    topc_regret, topk_indices, zeta_def,
)
from research_chains.contracts import HistoryTargetKind, RelationTargetKind, TypedEstimandKey
from research_chains.finite_world import FiniteResponseWorld
from research_chains.functionals import (
    functional_boundary_diagnostics, linear_contrast_variance, neyman_allocation,
)
from research_chains.pairwise import operational_gamma, pairwise_master_bound, sharp_gamma, topk_interval_certified
from research_chains.reference import ConditionalReferenceKernel
from research_chains.structural import scalar_prefix_order_exists
from research_chains.support import SupportBracket, SupportModel, projected_span_bracket


class NewChainHarnessTests(unittest.TestCase):
    def setUp(self):
        self.support = SupportModel((2,2,2), ((0,0,0),(0,1,1),(1,0,0),(1,1,1)), key='coupled')
        self.world = FiniteResponseWorld(
            self.support,
            (np.array([-0.5,0.5]), np.array([-2.,2.]), np.array([2.,-2.])),
        )

    def test_typed_estimand_fingerprint_changes_semantics(self):
        a = TypedEstimandKey('i','j',1,'rho',HistoryTargetKind.NATURAL,RelationTargetKind.PRIMITIVE_ISOLATED,'k','o','p')
        b = TypedEstimandKey('i','j',1,'rho',HistoryTargetKind.NATURAL,RelationTargetKind.FEASIBLE_KAPPA_RESPONSE,'k','o','p')
        self.assertNotEqual(a.fingerprint(), b.fingerprint())

    def test_aipw_rejects_non_natural_history_target(self):
        with self.assertRaises(ValueError):
            CrossFittedConditionalAIPW(2, history_target='frozen_standardized')

    def test_deficit_identity_and_half_bounds(self):
        for omitted in ((0,), (1,), (2,), (0,1), (0,2), (1,2), (0,1,2)):
            t = deficit_terms(self.world, omitted)
            self.assertAlmostEqual(t['d'], t['e_plus'] + t['e_minus'], places=10)
            self.assertGreaterEqual(t['d'], -1e-10)
        for k in (1,2,3):
            regret = topc_regret(self.world, k)
            self.assertLessEqual(regret, zeta_def(self.world,k)/2 + 1e-10)
            self.assertLessEqual(regret, global_extremizability_defect(self.world)/2 + 1e-10)

    def test_gauge_invariant_error_ignores_constants(self):
        truth=np.array([-2.,0.,4.]); estimate=truth+17.0
        self.assertAlmostEqual(quotient_sup_distance(estimate,truth),0.0,places=12)

    def test_lp_is_lower_bound(self):
        for k in (1,2):
            lp,_=lp_lower_bound(self.world,k); exact,_=exact_optimum(self.world,k)
            self.assertLessEqual(lp, exact+1e-9)

    def test_support_bracket_and_span_bracket(self):
        lower=SupportModel((2,2,2),((0,0,0),(1,1,1)),key='lower')
        upper=SupportModel((2,2,2),tuple(np.ndindex(2,2,2)),key='upper')
        bracket=SupportBracket(lower,upper)
        retained=topk_indices(self.world.component_spans(),1)
        opt,_=exact_optimum(self.world,1)
        actual=self.world.additive_radius(retained)-opt
        self.assertLessEqual(actual,support_bracket_regret_bound(self.world,bracket,retained,1)+1e-10)
        lo,hi=projected_span_bracket(self.world.primitives,bracket); truth=self.world.component_spans()
        self.assertTrue(np.all(lo<=truth+1e-12)); self.assertTrue(np.all(truth<=hi+1e-12))

    def test_reference_isolation_and_tv_bound(self):
        kernel=ConditionalReferenceKernel.uniform_feasible(self.support,0)
        q=kernel.response_vector(self.world,true_response=False)
        measured=float(np.max(q)-np.min(q)); primitive=self.world.component_span(0)
        chi=kernel.isolation_deviation(self.world)
        self.assertLessEqual(abs(measured-primitive),chi+1e-10)
        self.assertLessEqual(chi,kernel.tv_isolation_upper_bound(self.world)+1e-10)

    def test_product_reference_has_invariant_complement_marginals(self):
        marg={0:[.5,.5],1:[.3,.7],2:[.6,.4]}
        kernel=ConditionalReferenceKernel.product((2,2,2),0,marg)
        self.assertTrue(kernel.complement_marginals_invariant())

    def test_pairwise_operational_bound_dominates_actual(self):
        scores=self.world.component_spans(); estimated=scores+np.array([.2,-.1,.05]); errors=np.abs(estimated-scores)+.01; k=1
        selected=topk_indices(estimated,k); opt,_=exact_optimum(self.world,k); actual=self.world.additive_radius(selected)-opt
        sg=sharp_gamma(scores,estimated,errors,k); og=operational_gamma(estimated,errors,k,selected); z=zeta_def(self.world,k)
        self.assertLessEqual(actual,pairwise_master_bound(sg,z,0.0)+1e-10)
        self.assertLessEqual(actual,pairwise_master_bound(og,z,0.0)+1e-10)

    def test_interval_topk_certification(self):
        self.assertTrue(topk_interval_certified([3,2,0],[.1,.1,.1],2))
        self.assertFalse(topk_interval_certified([3,2,1.95],[.1,.1,.1],2))


    def test_functional_boundary_is_gauge_invariant(self):
        q=np.array([0.,1.,3.]); qhat=q+100.0
        d=functional_boundary_diagnostics(qhat,q)
        self.assertAlmostEqual(d["q_gauge_sup_error"],0.0,places=12)
        self.assertAlmostEqual(d["lambda_C"],0.0,places=12)
        self.assertEqual(d["both_extrema_match"],1)
        self.assertEqual(d["extrema_stability_certified"],1)
        self.assertEqual(d["extrema_stability_violation"],0)

    def test_functional_boundary_half_gap_certifies_extrema(self):
        q=np.array([0.,1.,3.]); qhat=q+np.array([0.15,-0.05,0.05])
        d=functional_boundary_diagnostics(qhat,q,action_ids=[4,7,9])
        self.assertLess(d["lambda_C"],0.5)
        self.assertEqual(d["learned_argmax_action"],9)
        self.assertEqual(d["learned_argmin_action"],4)
        self.assertEqual(d["both_extrema_match"],1)
        self.assertEqual(d["extrema_stability_certified"],1)
        self.assertEqual(d["extrema_stability_violation"],0)

    def test_functional_boundary_tie_is_not_certified(self):
        q=np.array([0.,1.,1.]); qhat=np.array([0.,1.01,.99])
        d=functional_boundary_diagnostics(qhat,q)
        self.assertEqual(d["oracle_extrema_unique"],0)
        self.assertEqual(d["extrema_gap_zero"],1)
        self.assertTrue(np.isinf(d["lambda_C"]))
        self.assertEqual(d["extrema_stability_certified"],0)
        self.assertEqual(d["extrema_stability_violation"],0)

    def test_floor_constrained_neyman_improves_or_matches_uniform(self):
        w=np.array([.5,-.3,-.2,0.0]); sig=np.array([1.,2.,.5,3.]); budget=40.; floor=2.
        targeted=neyman_allocation(w,sig,budget,floor=floor); uniform=np.full(4,budget/4)
        self.assertAlmostEqual(float(targeted.sum()),budget,places=8)
        self.assertTrue(np.all(targeted>=floor-1e-9))
        self.assertLessEqual(linear_contrast_variance(w,sig,targeted),linear_contrast_variance(w,sig,uniform)+1e-10)

    def test_coupled_family_can_have_no_single_optimal_prefix_order(self):
        exists,_=scalar_prefix_order_exists(self.world)
        self.assertFalse(exists)


if __name__ == '__main__':
    unittest.main()
