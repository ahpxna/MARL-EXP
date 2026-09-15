import «LeanStructuralUnbalancedToleranceUpperV1»
import «LeanStructuralApproximateAnchorV1»
import «LeanPrefixBudgetMetricCoverSlackV1»

/-! Approximate-anchor menu theorem for the actual support-radius objective.
Anchor solving remains an explicit oracle premise; it need not be exact. -/
namespace CIGAMF.P13.StructuralApproximateMenu
open Finset
open scoped BigOperators
open CIGAMF.V4.SupportGeometry CIGAMF.V4.StructuralRankability
open CIGAMF.P13.StructuralPrefixCoverDimension CIGAMF.P13.StructuralOrderedRadiusStep
open CIGAMF.P13.StructuralUnbalancedToleranceUpper
open CIGAMF.P13.StructuralApproximateAnchor CIGAMF.P13.PrefixBudgetMetricCoverSlack
noncomputable section
variable {m : ℕ} {Ω : Type*} [Fintype Ω] [Nonempty Ω]

theorem approximate_menu (f : Fin m → Ω → ℝ) (c : Fin m → ℝ)
    (hc : Monotone c) (hc0 : ∀ i,0 ≤ c i) (hf : ∀ i,osc (f i)/2 ≤ c i)
    (sigma eps : ℝ) (hgap : sigma < eps)
    (oracle : ∀ a,a ≤ m → ∃ S : Finset (Fin m),EpsilonOptimalAt (selectedRadius f) sigma a S) :
    PrefixCoverDimensionAtMost (selectedRadius f) eps (⌊(2*∑ i,c i)/(eps-sigma)⌋₊+1) := by
  have hanch : ∀ a,a ≤ Fintype.card (Fin m) → ∃ r : List (Fin m),IsFullRanking r ∧
      ∀ k,a ≤ k → k ≤ Fintype.card (Fin m) →
        EpsilonOptimalAt (selectedRadius f) (sigma+potential c k-potential c a) k (prefixSet r k) := by
    intro a ha
    obtain ⟨S,hS⟩ := oracle a (by simpa using ha)
    have hcard : S.card=a := hS.1
    have hS' : EpsilonOptimalAt (selectedRadius f) sigma S.card S := by rw [hcard];exact hS
    obtain ⟨r,hr,hall⟩ := approximate_anchored_ranking f c hc hf S sigma hS'
    refine ⟨r,hr,?_⟩
    intro k hak hk
    have hsum : S.card+(k-a)=k := by omega
    have h := hall (k-a) (by simpa [hsum] using hk)
    have hacc : accumulated c S.card (k-a)=potential c k-potential c a := by
      change CIGAMF.P13.StructuralOrderedRadiusChain.accumulated c S.card (k-a)=_
      rw [accumulated_eq,hsum,hcard]
    rw [hacc,hsum] at h
    simpa only [add_sub_assoc] using h
  have hh := metric_cover_with_anchor_slack (selectedRadius f) (potential c)
    (potential_mono c hc0) (fun k => sum_nonneg (fun z _ => charge_nonneg c hc0 z)) sigma hanch eps hgap
  have hpot : potential c m=2*∑ i,c i := total_charge c
  simpa only [Fintype.card_fin,hpot] using hh

/-- Explicit normalized tolerance, with no component-balance assumption. -/
theorem normalized_approximate_menu (f : Fin m → Ω → ℝ) (c : Fin m → ℝ)
    (hc : Monotone c) (hc0 : ∀ i,0 ≤ c i) (hf : ∀ i,osc (f i)/2 ≤ c i)
    (hB : 0 < ∑ i,c i) (eta eps : ℝ) (heta : 0 ≤ eta) (hgap : eta < eps)
    (oracle : ∀ a,a ≤ m → ∃ S : Finset (Fin m),
      EpsilonOptimalAt (selectedRadius f) (eta*(∑ i,c i)) a S) :
    PrefixCoverDimensionAtMost (selectedRadius f) (eps*(∑ i,c i)) (⌊2/(eps-eta)⌋₊+1) := by
  have h := approximate_menu f c hc hc0 hf (eta*(∑ i,c i)) (eps*(∑ i,c i))
    (mul_lt_mul_of_pos_right hgap hB) oracle
  have heq : (2*(∑ i,c i))/(eps*(∑ i,c i)-eta*(∑ i,c i))=2/(eps-eta) := by
    rw [← sub_mul]
    exact mul_div_mul_right _ _ hB.ne'
  rwa [heq] at h

#print axioms approximate_menu
#print axioms normalized_approximate_menu
end
end CIGAMF.P13.StructuralApproximateMenu
