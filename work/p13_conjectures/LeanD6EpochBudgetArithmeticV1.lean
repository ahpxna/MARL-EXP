import «LeanD6WeightedEpochCompositionV1»

/-! Exact cancellation for doubling-epoch recommendation bounds. Acquisition
cost is stated separately and grows geometrically, not logarithmically.
This module alone proves neither total regret nor a stopping rate. -/
namespace CIGAMF.P13.D6EpochBudgetArithmetic
open scoped BigOperators ENNReal
open Finset
open CIGAMF.P13.D6WeightedEpochComposition
noncomputable section

lemma finite_half_sum (E : ℕ) : (∑ s : Fin E,(2⁻¹:ℝ≥0∞)^s.val) ≤ 2 := by
  rw [Fin.sum_univ_eq_sum_range]
  exact (ENNReal.sum_le_tsum _).trans_eq ENNReal.tsum_geometric_two

lemma cancel_estimation (q : ℕ) (hq : 0 < q) (L : ℕ) (hL : 0 < L) :
    (L:ℝ≥0∞)*(ENNReal.ofReal (64/(q:ℝ)^2)*
      ENNReal.ofReal (((2*q+1:ℕ):ℝ)/((L:ℝ)*(q:ℝ)^4)))=
      ENNReal.ofReal (64*((2*q+1:ℕ):ℝ)/(q:ℝ)^6) := by
  have hqr : (0:ℝ)<q := by exact_mod_cast hq
  have hlr : (0:ℝ)<L := by exact_mod_cast hL
  rw [show (L:ℝ≥0∞)=ENNReal.ofReal (L:ℝ) by simp,
    ← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  <;> ring

/-- Weighted recommendation upper bound after cancelling the cyclic L. -/
theorem doubling_recommendation_sum (q L0 E : ℕ) (hq : 0 < q) (hL0 : 0 < L0)
    (V eta : ℝ≥0∞) :
    (∑ s : Fin E,((L0*2^s.val:ℕ):ℝ≥0∞)*
      (ENNReal.ofReal (64/(q:ℝ)^2)*
        ENNReal.ofReal (((2*q+1:ℕ):ℝ)/(((L0*2^s.val:ℕ):ℝ)*(q:ℝ)^4))+
        V*(eta*(4⁻¹:ℝ≥0∞)^s.val))) ≤
      (E:ℝ≥0∞)*ENNReal.ofReal (64*((2*q+1:ℕ):ℝ)/(q:ℝ)^6)+2*((L0:ℝ≥0∞)*V*eta) := by
  have hp (s : Fin E) : 0 < L0*2^s.val := Nat.mul_pos hL0 (by positivity)
  have he (s : Fin E) : ((L0*2^s.val:ℕ):ℝ≥0∞)*
      (ENNReal.ofReal (64/(q:ℝ)^2)*
        ENNReal.ofReal (((2*q+1:ℕ):ℝ)/(((L0*2^s.val:ℕ):ℝ)*(q:ℝ)^4))+
        V*(eta*(4⁻¹:ℝ≥0∞)^s.val))=
      ENNReal.ofReal (64*((2*q+1:ℕ):ℝ)/(q:ℝ)^6)+
        ((L0:ℝ≥0∞)*V*eta)*(2⁻¹:ℝ≥0∞)^s.val := by
    rw [mul_add,cancel_estimation q hq _ (hp s)]
    congr 1
    push_cast
    rw [← two_mul_quarter_pow]
    ring
  simp_rw [he]
  rw [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,← mul_sum]
  have hh := mul_le_mul_of_nonneg_left (finite_half_sum E)
    (show 0 ≤ (L0:ℝ≥0∞)*V*eta from zero_le)
  calc _ ≤ (E:ℝ≥0∞)*ENNReal.ofReal (64*((2*q+1:ℕ):ℝ)/(q:ℝ)^6)+
      ((L0:ℝ≥0∞)*V*eta)*2 := add_le_add le_rfl hh
       _ = _ := by ring

/-- Acquisition grows geometrically if a doubling pilot is repeated. It
cannot be called a logarithmic query cost. -/
theorem exploration_fraction_doubling (d L0 H0 E : ℕ) :
    d*(∑ s ∈ range E,L0*2^s)=d*L0*(2^E-1) ∧
    (∑ s ∈ range E,H0*2^s)=H0*(2^E-1) := by
  constructor
  · rw [doubling_budget];ring
  · exact doubling_budget H0 E

#print axioms cancel_estimation
#print axioms doubling_recommendation_sum
#print axioms exploration_fraction_doubling
end
end CIGAMF.P13.D6EpochBudgetArithmetic
