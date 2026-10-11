import «LeanD6ReferenceMatchingMinimaxV1»

/-! D05: explicit minimax certificates for the entire actual same-response family.
Both active and inactive phases are covered, within the numerical restrictions
in Region. The lower bound quantifies over EVERY finite randomized decision
rule of the original budget. No WLOG or symmetry premise is used.
-/
namespace CIGAMF.P13.D6ReferenceCertifiedPhaseValue
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6ReferenceBridge
open CIGAMF.P13.D6ReferenceResponseJoin CIGAMF.P13.D6ReferenceCenteredCompensated
open CIGAMF.P13.D6ReferenceLegalCountMinimum CIGAMF.P13.D6ReferencePhaseRegretBridge
open CIGAMF.P13.D6ReferenceEndpointWorlds CIGAMF.P13.D6ReferenceEndpointWorlds.Region
open CIGAMF.P13.D6ReferenceMatchingMinimax CIGAMF.P13.D6ReferencePhaseValue
open CIGAMF.P13.D6SameResponseMarginCertificate
open CIGAMF.V4.SupportGeometry
noncomputable section
variable {q : ℕ} {j : I (2*q+1)} {T : Finset (I (2*q+1))}

/-- An actual adversarial world exists for every randomized policy. -/
theorem worst_world_lower (M : Region q j T) (hact : M.e ≤ ((q:ℝ)+1)*M.r)
    (decisions : Finset (Finset (I (2*q+1)))) (w : Finset (I (2*q+1)) → ℝ)
    (hw : ∀ S ∈ decisions,0 ≤ w S) (hn : ∑ S ∈ decisions,w S=1) :
    ∃ A ∈ worlds q j,phaseValue ((q:ℝ)+1) M.p M.c M.e M.r ≤
      ∑ S ∈ decisions,w S*M.regret A S := by
  obtain ⟨A,hA,hmax⟩ := Finset.exists_max_image (worlds q j)
    (fun A => ∑ S ∈ decisions,w S*M.regret A S) ⟨T,M.hT⟩
  refine ⟨A,hA,?_⟩
  have hlo := randomized_dual_lower M hact decisions w hw hn
  have hb := region_bounds M
  have he : 0 ≤ M.e := hb.1.trans hb.2.1
  have hr : 0 ≤ M.r := by nlinarith [show (0:ℝ) ≤ q by positivity]
  have hq := M.hq
  have hk : (3:ℝ) ≤ (q:ℝ)+1 := by exact_mod_cast (show 3≤q+1 by omega)
  have hpr : M.p+M.r=2*M.c := by dsimp [p,r,c]; ring
  have hc : 0 < M.c*(((q:ℝ)+1)-1) := by
    rw [add_sub_cancel_right]
    exact mul_pos hb.2.2.2 (by exact_mod_cast (show 0<q by omega))
  have hweights := weights_valid ((q:ℝ)+1) M.p M.c M.e M.r hk he hr hb.2.2.1 M.hp hact hpr hc
  simp only [add_sub_cancel_right] at hweights
  have ht := hmax T M.hT
  have hs : (∑ i ∈ T,∑ S ∈ decisions,w S*M.regret (singletonWorld T j i) S)/((q:ℝ)+1) ≤
      ∑ S ∈ decisions,w S*M.regret A S := by
    have h := Finset.sum_le_sum (fun i hi => hmax _ (singleton_valid q M.hq j T M.hT i hi))
    have hd := div_le_div_of_nonneg_right h (by positivity : (0:ℝ) ≤ (q:ℝ)+1)
    rw [Finset.sum_const,nsmul_eq_mul,(world_parameters q j M.hq M.hT).2.1] at hd
    push_cast at hd
    have hnz : (q:ℝ)+1 ≠ 0 := by positivity
    simpa only [mul_div_cancel_left₀ _ hnz] using hd
  have h1 := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ 1-(vTerm ((q:ℝ)+1) M.p M.e M.r-uOne M.r M.e)/(M.c*q) by linarith [hweights.2.2.2])
  have h2 := mul_le_mul_of_nonneg_left ht hweights.2.2.1
  nlinarith only [hlo,h1,h2]

lemma regret_nonnegative (M : Region q j T) (A S : Finset (I (2*q+1))) (hS : S.card=T.card) :
    0 ≤ M.regret A S := by
  have h := minVal_le (fun U : {U : Finset (I (2*q+1)) // U.card=T.card} =>
    actualLoss A T U.val j M.rho M.t) ⟨S,hS⟩
  change legalMinimum A T j M.rho M.t ≤ actualLoss A T S j M.rho M.t at h
  exact sub_nonneg.mpr h

/-- Inactive phase: one actual decision is optimal simultaneously in every world. -/
theorem inactive_T_optimal (M : Region q j T) (hinact : ((q:ℝ)+1)*M.r ≤ M.e)
    (A : Finset (I (2*q+1))) (hA : A ∈ worlds q j) : M.regret A T=0 := by
  have hb := region_bounds M
  have he : 0 ≤ M.e := hb.1.trans hb.2.1
  have hh : (0:ℝ) ≤ (T ∩ A).card := by positivity
  have hhk : ((T ∩ A).card:ℝ) ≤ (q:ℝ)+1 := by
    have h := Finset.card_le_card (Finset.inter_subset_left : T ∩ A ⊆ T)
    rw [(world_parameters q j M.hq M.hT).2.1] at h
    exact_mod_cast h
  have hbound : M.r*((T ∩ A).card:ℝ) ≤ M.e := by
    by_cases hr : 0 ≤ M.r
    · have h := mul_le_mul_of_nonneg_left hhk hr
      nlinarith
    · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hr) hh).trans he
  rw [regret_counts M A T hA]
  simp only [Finset.sdiff_self,Finset.empty_inter,Finset.card_empty,variable_zero]
  rw [max_eq_left hbound]
  simp [e]

/-- Matching upper and lower certificates for the full phase value.
The prior proof covers all randomized policies; no restriction to the two
primal actions is imposed on the lower bound. -/
theorem full_actual_minimax_certificates (M : Region q j T) :
    (∃ w : ℝ,0 ≤ w ∧ w ≤ 1 ∧ Tᶜ.card=T.card ∧
      ∀ A ∈ worlds q j,w*M.regret A T+(1-w)*M.regret A Tᶜ ≤
        phaseValueFull ((q:ℝ)+1) M.p M.c M.e M.r) ∧
    (∀ (decisions : Finset (Finset (I (2*q+1)))) (w : Finset (I (2*q+1)) → ℝ),
      (∀ S ∈ decisions,0 ≤ w S) → (∑ S ∈ decisions,w S=1) →
      (∀ S ∈ decisions,S.card=T.card) →
      ∃ A ∈ worlds q j,phaseValueFull ((q:ℝ)+1) M.p M.c M.e M.r ≤
        ∑ S ∈ decisions,w S*M.regret A S) := by
  by_cases hact : M.e ≤ ((q:ℝ)+1)*M.r
  · have hb := region_bounds M
    have hc : M.c*(((q:ℝ)+1)-1) ≠ 0 := by
      rw [add_sub_cancel_right]
      exact ne_of_gt (mul_pos hb.2.2.2 (by exact_mod_cast (show 0<q by have := M.hq; omega)))
    rw [phaseValueFull_eq _ _ _ _ _ hact hc]
    constructor
    · exact ⟨vTerm ((q:ℝ)+1) M.p M.e M.r/(M.c*q),actual_primal_upper M hact⟩
    · intro decisions w hw hn hlegal
      exact worst_world_lower M hact decisions w hw hn
  · have hinact : ((q:ℝ)+1)*M.r ≤ M.e := le_of_lt (lt_of_not_ge hact)
    rw [phaseValueFull_zero _ _ _ _ _ hinact]
    constructor
    · refine ⟨1,by norm_num,by norm_num,(world_parameters q j M.hq M.hT).2.2.1,?_⟩
      intro A hA
      simp [inactive_T_optimal M hinact A hA]
    · intro decisions w hw hn hlegal
      refine ⟨T,M.hT,?_⟩
      exact Finset.sum_nonneg (fun S hS => mul_nonneg (hw S hS) (regret_nonnegative M T S (hlegal S hS)))

#print axioms worst_world_lower
#print axioms regret_nonnegative
#print axioms inactive_T_optimal
#print axioms full_actual_minimax_certificates
end
end CIGAMF.P13.D6ReferenceCertifiedPhaseValue
