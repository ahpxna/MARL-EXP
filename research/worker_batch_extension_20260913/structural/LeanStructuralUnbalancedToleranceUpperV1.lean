import «LeanStructuralOrderedRadiusChainV1»
import «LeanPrefixBudgetMetricCoverV1»

/-! Dimension-free tolerance upper bound without component balance. Sorted
radii are a coordinate order, not an equal-weight assumption. -/
namespace CIGAMF.P13.StructuralUnbalancedToleranceUpper
open scoped BigOperators
open Finset
open CIGAMF.V4.SupportGeometry CIGAMF.V4.StructuralRankability
open CIGAMF.P13.StructuralPrefixCoverDimension CIGAMF.P13.StructuralToleranceBudgetNet
open CIGAMF.P13.StructuralOrderedRadiusStep CIGAMF.P13.StructuralOrderedRadiusChain
open CIGAMF.P13.PrefixBudgetMetricCover
noncomputable section
variable {m : ℕ} {Ω : Type*} [Fintype Ω] [Nonempty Ω]

def potential (c : Fin m → ℝ) (k : ℕ) := ∑ z ∈ range k,charge c z

lemma charge_nonneg (c : Fin m → ℝ) (hc : ∀ i, 0 ≤ c i) (k : ℕ) : 0 ≤ charge c k := by
  have hw (j : ℕ) : 0 ≤ weight c j := by
    unfold weight
    split_ifs
    · exact hc _
    · exact le_rfl
  exact add_nonneg (hw _) (hw _)

lemma potential_mono (c : Fin m → ℝ) (hc : ∀ i, 0 ≤ c i) : Monotone (potential c) := by
  apply monotone_nat_of_le_succ
  intro k
  simp only [potential,sum_range_succ]
  exact le_add_of_nonneg_right (charge_nonneg c hc k)

lemma accumulated_eq (c : Fin m → ℝ) (a t : ℕ) :
    accumulated c a t=potential c (a+t)-potential c a := by
  unfold accumulated potential
  rw [sum_range_add]
  ring

theorem sorted_unbalanced_upper (f : Fin m → Ω → ℝ) (c : Fin m → ℝ)
    (hc : Monotone c) (hc0 : ∀ i, 0 ≤ c i)
    (hf : ∀ i, osc (f i)/2 ≤ c i) (eps : ℝ) (heps : 0 < eps) :
    PrefixCoverDimensionAtMost (selectedRadius f) eps (⌊(2*∑ i,c i)/eps⌋₊+1) := by
  have hpot : potential c m=2*∑ i,c i := total_charge c
  rw [← hpot]
  have hanch : ∀ a, a ≤ Fintype.card (Fin m) → ∃ r : List (Fin m), IsFullRanking r ∧
      ∀ k, a ≤ k → k ≤ Fintype.card (Fin m) →
        EpsilonOptimalAt (selectedRadius f) (potential c k-potential c a) k (prefixSet r k) := by
    intro a ha
    obtain ⟨r,hr,ho⟩ := exact_ranking f a ha
    let S := prefixSet r a
    have hcard : S.card=a := ho.1
    have hS : EpsilonOptimalAt (selectedRadius f) 0 S.card S := by rw [hcard];exact ho
    obtain ⟨r',hr',hall⟩ := anchored_ranking f c hc hf S hS
    refine ⟨r',hr',?_⟩
    intro k hak hk
    have hsum : S.card+(k-a)=k := by omega
    have h := hall (k-a) (by simpa [hsum] using hk)
    rw [accumulated_eq,hsum,hcard] at h
    exact h
  have hh := metric_cover (selectedRadius f) (potential c) (potential_mono c hc0)
    (fun k => sum_nonneg (fun z _ => charge_nonneg c hc0 z)) hanch eps heps
  simpa using hh

#print axioms accumulated_eq
#print axioms sorted_unbalanced_upper
end
end CIGAMF.P13.StructuralUnbalancedToleranceUpper
