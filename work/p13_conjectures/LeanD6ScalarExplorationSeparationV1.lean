import «LeanD6BlindActualMomentsV1»
import «LeanD6AllocationRiskBridgeV1»

/-! Actual information supplied by forced scalar exploration. The inequalities
hold for all wrong labels and nuisance margins. No termination or rate premise
is hidden in this deterministic separation result. -/
namespace CIGAMF.P13.D6ScalarExplorationSeparation
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6AllocationSharp CIGAMF.P13.D6AllocationRiskBridge
open CIGAMF.P13.D6BlindActualMoments
noncomputable section

lemma quadratic_separation (q d mu z : ℝ) (hq : 0 < q) (hd : 1 ≤ d) (hdq : d ≤ q) :
    mu^2/2 ≤ q*z^2/2+d*mu*z+d*mu^2 := by
  have he : q*z^2/2+d*mu*z+d*mu^2-d*mu^2/2=
      (q*z+d*mu)^2/(2*q)+d*(q-d)*mu^2/(2*q) := by field_simp; ring
  have hp : 0 ≤ (q*z+d*mu)^2/(2*q)+d*(q-d)*mu^2/(2*q) := by
    have hdd : 0 ≤ q-d := sub_nonneg.mpr hdq
    positivity
  nlinarith only [he,hp,mul_nonneg (sub_nonneg.mpr hd) (sq_nonneg mu)]

theorem one_round_information (q : ℕ) (hq : 3 ≤ q) (j : I (2*q+1))
    (A A' : Finset (I (2*q+1))) (hj : j ∉ A) (hj' : j ∉ A')
    (hc : A'.card=A.card) (hB : (others A j).card=q) (hne : A' ≠ A) (mu nu : ℝ) :
    mu^2/2 ≤ ∑ i ∈ univ.erase j,scalarKL A A' j i mu nu := by
  have hd := alternative_distance_bounds A A' j q hj' hc hne (by exact_mod_cast hB)
  have he := actual_scalar_average A A' j q mu (nu-mu) hj hj' hc (by exact_mod_cast hB)
  rw [show mu+(nu-mu)=nu by ring] at he
  have hn : ((2*q+1:ℕ):ℝ) ≠ 0 := by positivity
  have hs := (div_left_inj hn).mp he
  rw [hs]
  exact quadratic_separation q _ mu (nu-mu) (by exact_mod_cast (show 0 < q by omega)) hd.1 hd.2

theorem forced_rounds_information (q : ℕ) (hq : 3 ≤ q) (j : I (2*q+1))
    (A A' : Finset (I (2*q+1))) (hj : j ∉ A) (hj' : j ∉ A')
    (hc : A'.card=A.card) (hB : (others A j).card=q) (hne : A' ≠ A) (mu nu r : ℝ)
    (hr : 0 ≤ r) (E : Finset (Measurement (2*q+1))) (count : Measurement (2*q+1) → ℝ)
    (hcount : ∀ e ∈ E,0 ≤ count e)
    (hinclude : ∀ i ∈ univ.erase j,(.inl i : Measurement (2*q+1)) ∈ E)
    (hforced : ∀ i ∈ univ.erase j,r ≤ count (.inl i)) :
    r*mu^2/2 ≤ ∑ e ∈ E,count e*information A A' j mu nu e := by
  have hsub : ((univ.erase j).image (Sum.inl : I (2*q+1) → Measurement (2*q+1))) ⊆ E := by
    intro e he
    obtain ⟨i,hi,rfl⟩ := mem_image.mp he
    exact hinclude i hi
  calc
    _ ≤ r*(∑ i ∈ univ.erase j,scalarKL A A' j i mu nu) := by
      have h := mul_le_mul_of_nonneg_left (one_round_information q hq j A A' hj hj' hc hB hne mu nu) hr
      nlinarith only [h]
    _ ≤ ∑ i ∈ univ.erase j,count (.inl i)*information A A' j mu nu (.inl i) := by
      rw [mul_sum]
      apply sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (hforced i hi) (information_nonnegative A A' j mu nu (.inl i))
    _ = ∑ e ∈ (univ.erase j).image (Sum.inl : I (2*q+1) → Measurement (2*q+1)),count e*information A A' j mu nu e := by
      rw [sum_image]
      intro i hi k hk he
      exact Sum.inl.inj he
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun e he _ =>
      mul_nonneg (hcount e he) (information_nonnegative A A' j mu nu e))

#print axioms quadratic_separation
#print axioms one_round_information
#print axioms forced_rounds_information
end
end CIGAMF.P13.D6ScalarExplorationSeparation
