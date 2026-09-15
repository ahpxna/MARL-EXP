import «LeanD6AllocationStabilityV1»
import «LeanD6ConstructiveTrackingV1»

/-! A07: phase-independent stability of the ACTUAL infimum/supremum game.
The admissible alternative class is independent of mu. No continuity of an
optimizer, known allocation phase, or closed-form Gamma formula is assumed.
Label A is fixed here: using a wrong decoded label is a separate risk term.
The optimization tolerance is a solver contract, not a solver-existence claim.
-/
namespace CIGAMF.P13.D6OracleValueStability
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6AllocationFiniteBridge CIGAMF.P13.D6AllocationRiskBridge
open CIGAMF.P13.D6LocalOracleRegret CIGAMF.P13.D6AllocationStability
open CIGAMF.P13.D6AllocationTrackingStability CIGAMF.P13.D6ConstructiveTracking
noncomputable section
variable {n : ℕ}

def marginModulus (q : ℝ) : ℝ := 2*q*(2*q+1)

theorem allocation_margin_one_sided (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (halt : ∃ A' nu, Admissible A A' j nu) (q mu mhat : ℝ) (hq : 1 ≤ q)
    (hm : 0 ≤ mu) (hm1 : mu ≤ 1) (hh : 0 ≤ mhat) (hh1 : mhat ≤ 1)
    (E : Finset (Measurement n)) (w : Measurement n → ℝ) (hf : Feasible j q E w) :
    allocationValue A j mu E w ≤ allocationValue A j mhat E w+marginModulus q*|mu-mhat| := by
  have hinf : allocationValue A j mu E w-marginModulus q*|mu-mhat| ≤
      allocationValue A j mhat E w := by
    apply le_csInf (value_nonempty A j halt mhat E w)
    rintro z ⟨A',nu,ha,rfl⟩
    have h1 := allocationValue_le_actual A A' j mu nu E w hf.2.1 ha
    have h2 := weighted_information_stability A A' j q mu mhat nu hq hj ha.2.2.1
      hm hm1 hh hh1 ha.2.2.2.1 ha.2.2.2.2 E w hf.1 hf.2.1 hf.2.2
    have h3 := (abs_le.mp h2).2
    change _ ≤ marginModulus q*|mu-mhat| at h3
    linarith
  linarith

theorem allocation_margin_modulus (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (halt : ∃ A' nu, Admissible A A' j nu) (q mu mhat : ℝ) (hq : 1 ≤ q)
    (hm : 0 ≤ mu) (hm1 : mu ≤ 1) (hh : 0 ≤ mhat) (hh1 : mhat ≤ 1)
    (E : Finset (Measurement n)) (w : Measurement n → ℝ) (hf : Feasible j q E w) :
    |allocationValue A j mu E w-allocationValue A j mhat E w| ≤ marginModulus q*|mu-mhat| := by
  have h1 := allocation_margin_one_sided A j hj halt q mu mhat hq hm hm1 hh hh1 E w hf
  have h2 := allocation_margin_one_sided A j hj halt q mhat mu hq hh hh1 hm hm1 E w hf
  rw [abs_sub_comm mhat mu] at h2
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- A legal normalized allocation exists for every q: a scalar query suffices. -/
theorem feasible_exists (j : I n) (q : ℝ) : ∃ E w, Feasible j q E w := by
  classical
  refine ⟨{.inl j},fun _ => 1,?_,?_,?_⟩
  · intro e he
    have : e = .inl j := Finset.mem_singleton.mp he
    subst e
    trivial
  · intro e he; norm_num
  · simp

theorem game_values_nonempty (A : Finset (I n)) (j : I n) (q mu : ℝ) :
    (gameValues A j q mu).Nonempty := by
  obtain ⟨E,w,hf⟩ := feasible_exists j q
  exact ⟨_,E,w,hf,rfl⟩

theorem game_values_bounded (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (halt : ∃ A' nu, Admissible A A' j nu) (q mu : ℝ) (hq : 0 ≤ q)
    (hm : 0 ≤ mu) (hm1 : mu ≤ 1) : BddAbove (gameValues A j q mu) := by
  refine ⟨informationCap q,?_⟩
  rintro v ⟨E,w,hf,rfl⟩
  obtain ⟨A',nu,ha⟩ := halt
  apply (allocationValue_le_actual A A' j mu nu E w hf.2.1 ha).trans
  calc
    _ ≤ ∑ e ∈ E,w e*informationCap q := by
      apply sum_le_sum
      intro e he
      apply mul_le_mul_of_nonneg_left _ (hf.2.1 e he)
      exact (le_abs_self _).trans (actual_information_cap A A' j hj ha.2.2.1 q mu nu
        hq hm hm1 ha.2.2.2.1 ha.2.2.2.2 e (hf.1 e he))
    _ = _ := by rw [← sum_mul,hf.2.2,one_mul]

theorem oracle_margin_one_sided (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (halt : ∃ A' nu, Admissible A A' j nu) (q mu mhat : ℝ) (hq : 1 ≤ q)
    (hm : 0 ≤ mu) (hm1 : mu ≤ 1) (hh : 0 ≤ mhat) (hh1 : mhat ≤ 1) :
    oracleValue A j q mu ≤ oracleValue A j q mhat+marginModulus q*|mu-mhat| := by
  apply csSup_le (game_values_nonempty A j q mu)
  rintro v ⟨E,w,hf,rfl⟩
  have h1 := allocation_margin_one_sided A j hj halt q mu mhat hq hm hm1 hh hh1 E w hf
  have h2 : allocationValue A j mhat E w ≤ oracleValue A j q mhat :=
    le_csSup (game_values_bounded A j hj halt q mhat (by linarith) hh hh1) ⟨E,w,hf,rfl⟩
  linarith

/-- Gamma is Lipschitz across all allocation phases on the model interval. -/
theorem oracle_margin_modulus (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (halt : ∃ A' nu, Admissible A A' j nu) (q mu mhat : ℝ) (hq : 1 ≤ q)
    (hm : 0 ≤ mu) (hm1 : mu ≤ 1) (hh : 0 ≤ mhat) (hh1 : mhat ≤ 1) :
    |oracleValue A j q mu-oracleValue A j q mhat| ≤ marginModulus q*|mu-mhat| := by
  have h1 := oracle_margin_one_sided A j hj halt q mu mhat hq hm hm1 hh hh1
  have h2 := oracle_margin_one_sided A j hj halt q mhat mu hq hh hh1 hm hm1
  rw [abs_sub_comm mhat mu] at h2
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- Optimizing at the estimate costs twice the margin modulus, even when an
optimizer changes discontinuously. tau is a nonnegative optimization error. -/
theorem estimated_optimizer_regret (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (halt : ∃ A' nu, Admissible A A' j nu) (q mu mhat tau : ℝ) (hq : 1 ≤ q)
    (hm : 0 ≤ mu) (hm1 : mu ≤ 1) (hh : 0 ≤ mhat) (hh1 : mhat ≤ 1) (ht : 0 ≤ tau)
    (E : Finset (Measurement n)) (w : Measurement n → ℝ) (hf : Feasible j q E w)
    (hopt : oracleValue A j q mhat ≤ allocationValue A j mhat E w+tau) :
    oracleRegret A j q mu E w ≤ 2*marginModulus q*|mu-mhat|+tau := by
  have h1 := oracle_margin_one_sided A j hj halt q mu mhat hq hm hm1 hh hh1
  have h2 := allocation_margin_one_sided A j hj halt q mhat mu hq hh hh1 hm hm1 E w hf
  rw [abs_sub_comm mhat mu] at h2
  unfold oracleRegret
  apply max_le
  · have hL : 0 ≤ marginModulus q := by unfold marginModulus; positivity
    positivity
  · linarith

/-- Estimation, optimization, and arbitrary L1 tracking errors remain separate. -/
theorem estimated_tracked_regret (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (halt : ∃ A' nu, Admissible A A' j nu) (q mu mhat tau : ℝ) (hq : 1 ≤ q)
    (hm : 0 ≤ mu) (hm1 : mu ≤ 1) (hh : 0 ≤ mhat) (hh1 : mhat ≤ 1) (ht : 0 ≤ tau)
    (E : Finset (Measurement n)) (w v : Measurement n → ℝ) (hf : Feasible j q E w)
    (hv : ∀ e ∈ E,0 ≤ v e)
    (hopt : oracleValue A j q mhat ≤ allocationValue A j mhat E w+tau) :
    oracleRegret A j q mu E v ≤ 2*marginModulus q*|mu-mhat|+tau+
      informationCap q*(∑ e ∈ E,|w e-v e|) := by
  have h1 := estimated_optimizer_regret A j hj halt q mu mhat tau hq hm hm1 hh hh1 ht E w hf hopt
  have h2 := allocation_one_sided A j hj halt q mu (by linarith) hm hm1 E w v hf.1 hf.2.1 hv
  have hc : 0 ≤ informationCap q*(∑ e ∈ E,|w e-v e|) := by unfold informationCap; positivity
  unfold oracleRegret at h1 ⊢
  apply max_le
  · have hL : 0 ≤ marginModulus q := by unfold marginModulus; positivity
    positivity
  · have h3 := le_max_right (0:ℝ) (oracleValue A j q mu-allocationValue A j mu E w)
    linarith

/-- The discrepancy term is supplied by the existing constructive tracker.
This remains pathwise and fixed-label; it does not hide discovery failures. -/
theorem realized_estimated_tracking (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (halt : ∃ A' nu, Admissible A A' j nu) (q mu : ℝ) (hq : 1 ≤ q)
    (hm : 0 ≤ mu) (hm1 : mu ≤ 1) (E : Finset (Measurement n)) (hE : E.Nonempty)
    (mhat tau : ℕ → ℝ) (w : ℕ → Measurement n → ℝ)
    (hh : ∀ t,0 ≤ mhat t ∧ mhat t ≤ 1) (ht : ∀ t,0 ≤ tau t)
    (hf : ∀ t,Feasible j q E (w t))
    (hopt : ∀ t,oracleValue A j q (mhat t) ≤ allocationValue A j (mhat t) E (w t)+tau t) :
    ∃ schedule : ℕ → Measurement n,
      (∀ t,schedule t ∈ E ∧ Legal j q (schedule t)) ∧
      ∀ N : ℕ,0 < N →
        oracleRegret A j q mu E (fun e => (((range N).filter (fun t => schedule t=e)).card:ℝ)/(N:ℝ)) ≤
          (∑ t ∈ range N,(2*marginModulus q*|mu-mhat t|+tau t))/(N:ℝ)
            +informationCap q*(E.card:ℝ)^2/(N:ℝ) := by
  obtain ⟨schedule,hs,hrate⟩ := realized_tracking A j hj halt q mu (by linarith) hm hm1 E hE w
    (hf 0).1 (fun t => (hf t).2.1) (fun t => (hf t).2.2)
  refine ⟨schedule,hs,?_⟩
  intro N hN
  have h1 := hrate N hN
  have h2 := average_oracle_regret A j halt q mu E w (fun t => (hf t).2.1) N hN
  have h3 : (∑ t ∈ range N,oracleRegret A j q mu E (w t)) ≤
      ∑ t ∈ range N,(2*marginModulus q*|mu-mhat t|+tau t) := by
    apply sum_le_sum
    intro t _
    exact estimated_optimizer_regret A j hj halt q mu (mhat t) (tau t) hq hm hm1
      (hh t).1 (hh t).2 (ht t) E (w t) (hf t) (hopt t)
  have h4 := div_le_div_of_nonneg_right h3 (by positivity : (0:ℝ) ≤ N)
  linarith

/-- The nonempty-alternative premise is discharged on actual D6 worlds. -/
theorem actual_world_oracle_modulus (q : ℕ) (hq : 3 ≤ q) (j : I (2*q+1))
    (A : Finset (I (2*q+1))) (hA : A ∈ worlds q j) (mu mhat : ℝ)
    (hm : 0 ≤ mu) (hm1 : mu ≤ 1) (hh : 0 ≤ mhat) (hh1 : mhat ≤ 1) :
    |oracleValue A j q mu-oracleValue A j q mhat| ≤ marginModulus q*|mu-mhat| := by
  have hp := world_parameters q j (by omega) hA
  exact oracle_margin_modulus A j hp.1 (world_has_alternative q j (by omega) A hA)
    q mu mhat (by exact_mod_cast (show 1 ≤ q by omega)) hm hm1 hh hh1

#print axioms allocation_margin_modulus
#print axioms feasible_exists
#print axioms game_values_bounded
#print axioms oracle_margin_modulus
#print axioms estimated_optimizer_regret
#print axioms estimated_tracked_regret
#print axioms realized_estimated_tracking
#print axioms actual_world_oracle_modulus
end
end CIGAMF.P13.D6OracleValueStability
