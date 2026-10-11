import «LeanD6OracleValueStabilityV1»

/-! A07 without a fixed-correct-label fiction. The uniform loss cap is proved
for the actual information game. Wrong-label events are retained and multiplied
by the full deployment length. No independence is assumed. The optimization
hypothesis here is discharged separately by a finite solver. -/
namespace CIGAMF.P13.D6AdaptiveLabelAccounting
open scoped BigOperators ENNReal
open Finset MeasureTheory
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6AllocationRiskBridge CIGAMF.P13.D6LocalOracleRegret
open CIGAMF.P13.D6AllocationTrackingStability CIGAMF.P13.D6OracleValueStability
open CIGAMF.P13.D6AdaptiveOracleRegret
noncomputable section
variable {n : ℕ}

/-- C_q = (q+2)^2/2 bounds actual oracle regret, uniformly in the reported label. -/
theorem oracle_regret_cap (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (halt : ∃ A' nu,Admissible A A' j nu) (q mu : ℝ)
    (hq : 0 ≤ q) (hm : 0 ≤ mu) (hm1 : mu ≤ 1)
    (E : Finset (Measurement n)) (w : Measurement n → ℝ)
    (hw : ∀ e ∈ E,0 ≤ w e) : oracleRegret A j q mu E w ≤ informationCap q := by
  have ho : oracleValue A j q mu ≤ informationCap q := by
    apply csSup_le (game_values_nonempty A j q mu)
    rintro v ⟨F,u,hf,rfl⟩
    obtain ⟨A',nu,ha⟩ := halt
    apply (allocationValue_le_actual A A' j mu nu F u hf.2.1 ha).trans
    calc
      _ ≤ ∑ e ∈ F,u e*informationCap q := by
        apply sum_le_sum
        intro e he
        apply mul_le_mul_of_nonneg_left _ (hf.2.1 e he)
        exact (le_abs_self _).trans (actual_information_cap A A' j hj ha.2.2.1 q mu nu
          hq hm hm1 ha.2.2.2.1 ha.2.2.2.2 e (hf.1 e he))
      _ = _ := by rw [← sum_mul,hf.2.2,one_mul]
  have hc : 0 ≤ informationCap q := by unfold informationCap;positivity
  exact (oracle_regret_bounded A j q mu E w hw).trans (max_le hc ho)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A pointwise good-label/bad-label split for any data-dependent recommendation. -/
theorem label_split (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (halt : ∃ A' nu,Admissible A A' j nu) (q mu : ℝ) (hq : 1 ≤ q)
    (hm : 0 ≤ mu) (hm1 : mu ≤ 1) (E : Finset (Measurement n))
    (Ahat : Ω → Finset (I n)) (mhat tau : Ω → ℝ) (w : Ω → Measurement n → ℝ)
    (hh : ∀ x,0 ≤ mhat x ∧ mhat x ≤ 1) (ht : ∀ x,0 ≤ tau x)
    (hf : ∀ x,Feasible j q E (w x))
    (hopt : ∀ x,oracleValue (Ahat x) j q (mhat x) ≤
      allocationValue (Ahat x) j (mhat x) E (w x)+tau x) (x : Ω) :
    oracleRegret A j q mu E (w x) ≤
      (if Ahat x=A then 2*marginModulus q*|mu-mhat x|+tau x else informationCap q) := by
  by_cases hx : Ahat x=A
  · rw [if_pos hx]
    have ho := hopt x
    rw [hx] at ho
    exact estimated_optimizer_regret A j hj halt q mu (mhat x) (tau x) hq hm hm1
      (hh x).1 (hh x).2 (ht x) E (w x) (hf x) ho
  · rw [if_neg hx]
    exact oracle_regret_cap A j hj halt q mu (by linarith) hm hm1 E (w x) (hf x).2.1

/-- Lower-integral expectation form; valid even before loss integrability is
proved. The good term is restricted to the correct-label event. -/
theorem expected_label_split (P : Measure Ω) (A : Finset (I n)) (j : I n)
    (hj : j ∉ A) (halt : ∃ A' nu,Admissible A A' j nu)
    (q mu : ℝ) (hq : 1 ≤ q) (hm : 0 ≤ mu) (hm1 : mu ≤ 1)
    (E : Finset (Measurement n)) (Ahat : Ω → Finset (I n))
    (mhat tau : Ω → ℝ) (w : Ω → Measurement n → ℝ)
    (hb : MeasurableSet {x | Ahat x ≠ A})
    (hg : Measurable (fun x => ENNReal.ofReal (2*marginModulus q*|mu-mhat x|+tau x)))
    (hh : ∀ x,0 ≤ mhat x ∧ mhat x ≤ 1) (ht : ∀ x,0 ≤ tau x)
    (hf : ∀ x,Feasible j q E (w x))
    (hopt : ∀ x,oracleValue (Ahat x) j q (mhat x) ≤
      allocationValue (Ahat x) j (mhat x) E (w x)+tau x) :
    (∫⁻ x,ENNReal.ofReal (oracleRegret A j q mu E (w x)) ∂P) ≤
      (∫⁻ x,({x | Ahat x ≠ A}ᶜ).indicator
        (fun x => ENNReal.ofReal (2*marginModulus q*|mu-mhat x|+tau x)) x ∂P)+
      ENNReal.ofReal (informationCap q)*P {x | Ahat x ≠ A} := by
  let B : Set Ω := {x | Ahat x ≠ A}
  have hpoint (x : Ω) : ENNReal.ofReal (oracleRegret A j q mu E (w x)) ≤
      Bᶜ.indicator (fun x => ENNReal.ofReal (2*marginModulus q*|mu-mhat x|+tau x)) x+
      B.indicator (fun _ => ENNReal.ofReal (informationCap q)) x := by
    have h := ENNReal.ofReal_le_ofReal (label_split A j hj halt q mu hq hm hm1 E Ahat mhat tau w hh ht hf hopt x)
    by_cases hx : Ahat x=A <;> simpa [B,hx] using h
  calc
    _ ≤ ∫⁻ x,Bᶜ.indicator (fun x => ENNReal.ofReal (2*marginModulus q*|mu-mhat x|+tau x)) x+
        B.indicator (fun _ => ENNReal.ofReal (informationCap q)) x ∂P := lintegral_mono hpoint
    _ = _ := by
      rw [lintegral_add_left (hg.indicator hb.compl),lintegral_indicator_const hb]

/-- This is the length multiplier that cannot be omitted for epoch deployment. -/
theorem epoch_wrong_label_cost (P : Measure Ω) (B : Set Ω) (hB : MeasurableSet B)
    (C : ℝ≥0∞) (H : ℕ) :
    (∫⁻ x,B.indicator (fun _ => (H:ℝ≥0∞)*C) x ∂P)=(H:ℝ≥0∞)*C*P B :=
  lintegral_indicator_const hB _

/-- Doubling deployment lengths and quarter-rate errors have summable cost. -/
theorem doubling_wrong_label_sum (C eta : ℝ≥0∞) (H : ℕ) :
    (∑' s : ℕ,C*(H:ℝ≥0∞)*2^s*(eta*(4⁻¹:ℝ≥0∞)^s))=2*(C*(H:ℝ≥0∞)*eta) := by
  have he (s : ℕ) : C*(H:ℝ≥0∞)*2^s*(eta*(4⁻¹:ℝ≥0∞)^s)=
      (C*(H:ℝ≥0∞)*eta)*(2⁻¹:ℝ≥0∞)^s := by
    have hp : (2:ℝ≥0∞)*(4⁻¹:ℝ≥0∞)=2⁻¹ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num
    rw [← hp,mul_pow]
    ring
  simp_rw [he]
  rw [ENNReal.tsum_mul_left,ENNReal.tsum_geometric_two]
  ring

#print axioms oracle_regret_cap
#print axioms label_split
#print axioms expected_label_split
#print axioms epoch_wrong_label_cost
#print axioms doubling_wrong_label_sum
end
end CIGAMF.P13.D6AdaptiveLabelAccounting
