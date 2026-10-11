import «LeanD6FiniteSolverMeasurabilityV1»
import «LeanD6AdaptiveLabelAccountingV1»

/-! Ordinary finite expectation of the actual finite solver's information loss.
Measurability and integrability are proved; optimizer quality is not a hypothesis.
Estimator concentration is deliberately a separate theorem. -/
namespace CIGAMF.P13.D6FiniteSolverExpectation
open scoped BigOperators
open Finset MeasureTheory
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6AllocationRiskBridge CIGAMF.P13.D6LocalOracleRegret
open CIGAMF.P13.D6AllocationTrackingStability CIGAMF.P13.D6OracleValueStability
open CIGAMF.P13.D6ConstructiveTracking CIGAMF.P13.D6FiniteGridAllocation
open CIGAMF.P13.FiniteGridSolver CIGAMF.P13.D6FiniteSolverMeasurability
open CIGAMF.P13.D6AdaptiveLabelAccounting
noncomputable section
attribute [local instance] Classical.propDecidable
variable {Ω : Type*} [MeasurableSpace Ω]

lemma finite_selected_measurable {K : Type*} [Fintype K] [MeasurableSpace K]
    [MeasurableSingletonClass K] (k : Ω → K) (hk : Measurable k)
    (f : K → Ω → ℝ) (hf : ∀ a,Measurable (f a)) :
    Measurable (fun x => f (k x) x) := by
  classical
  have hs : Measurable (fun x => ∑ a : K,{x | k x=a}.indicator (f a) x) := by
    apply Finset.measurable_sum
    intro a _
    exact (hf a).indicator (measurableSet_eq_fun hk measurable_const)
  convert hs using 1
  funext x
  rw [sum_eq_single (k x)]
  · simp
  · intro a _ hn
    exact Set.indicator_of_notMem (by simpa [eq_comm] using hn) _
  · simp

/-- Any real statistic of the returned finite grid point is measurable. -/
theorem solver_statistic_measurable (q : ℕ) (hq : 2 ≤ q) (j : I (2*q+1))
    (Ahat : Ω → worlds q j) (hA : Measurable Ahat)
    (mhat : Ω → Margin) (hm : Measurable mhat) (H : ℕ) (hH : 0 < H)
    (loss : (Measurement (2*q+1) → ℝ) → ℝ) :
    Measurable (fun x => loss (solverWeight (Ahat x).val j (mhat x).val
      (allQueries j q) (allQueries_nonempty j q) H)) := by
  apply finite_selected_measurable Ahat hA (fun B x => loss (solverWeight B.val j (mhat x).val
    (allQueries j q) (allQueries_nonempty j q) H))
  intro B
  let E := allQueries j q
  letI : Nonempty E := (allQueries_nonempty j q).to_subtype
  have hs : Measurable (fun x => solve H (fun v : E → ℝ =>
      allocationValue B.val j (mhat x).val E (liftWeight E v))) := by
    apply solve_measurable
    intro g
    apply (score_continuous B.val j (world_parameters q j hq B.property).1
      (world_has_alternative q j hq B.val B.property) q
      (by exact_mod_cast (show 1 ≤ q by omega)) E (liftWeight E (weight g)) ?_).measurable.comp hm
    refine ⟨fun e he => (allQueries_mem j q e).mp he,?_,?_⟩
    · intro e he
      simpa [liftWeight,he] using weight_nonneg g (⟨e,he⟩ : E)
    · rw [lift_sum]
      exact weight_total hH g
  exact (measurable_of_finite (fun g : Grid E H => loss (liftWeight E (weight g)))).comp hs

/-- Ordinary expected regret, including the actual wrong-label probability. -/
theorem expected_solver_regret (P : Measure Ω) [IsProbabilityMeasure P]
    (q : ℕ) (hq : 2 ≤ q) (j : I (2*q+1)) (A : Finset (I (2*q+1)))
    (hA : A ∈ worlds q j) (mu : ℝ) (hmu : mu ∈ Set.Icc 0 1)
    (Ahat : Ω → worlds q j) (hAh : Measurable Ahat)
    (mhat : Ω → Margin) (hm : Measurable mhat) (H : ℕ) (hH : 0 < H) :
    let E := allQueries j q
    let w := fun x => solverWeight (Ahat x).val j (mhat x).val E (allQueries_nonempty j q) H
    let good := fun x => 2*marginModulus q*|mu-(mhat x).val|+informationCap q*(E.card:ℝ)^2/(H:ℝ)
    Integrable (fun x => oracleRegret A j q mu E (w x)) P ∧
      (∫ x,oracleRegret A j q mu E (w x) ∂P) ≤
        (∫ x,{x | (Ahat x).val=A}.indicator good x ∂P)+
          informationCap q*P.real {x | (Ahat x).val ≠ A} := by
  dsimp only
  let E := allQueries j q
  let w := fun x => solverWeight (Ahat x).val j (mhat x).val E (allQueries_nonempty j q) H
  let tau := informationCap q*(E.card:ℝ)^2/(H:ℝ)
  let good := fun x => 2*marginModulus q*|mu-(mhat x).val|+tau
  let B : Set Ω := {x | (Ahat x).val ≠ A}
  have hB : MeasurableSet B := (measurableSet_eq_fun (measurable_subtype_coe.comp hAh) measurable_const).compl
  have hf (x : Ω) : Feasible j q E (w x) := solver_feasible _ j q _ E
    (allQueries_nonempty j q) (fun e he => (allQueries_mem j q e).mp he) H hH
  have hcap (x : Ω) : oracleRegret A j q mu E (w x) ≤ informationCap q :=
    oracle_regret_cap A j (world_parameters q j hq hA).1 (world_has_alternative q j hq A hA)
      q mu (by positivity) hmu.1 hmu.2 E (w x) (hf x).2.1
  have hi : Integrable (fun x => oracleRegret A j q mu E (w x)) P := by
    apply Integrable.of_bound (solver_statistic_measurable q hq j Ahat hAh mhat hm H hH
      (oracleRegret A j q mu E)).aestronglyMeasurable (informationCap q)
    apply ae_of_all
    intro x
    have hn : 0 ≤ oracleRegret A j q mu E (w x) := le_max_left (0:ℝ) _
    change ‖oracleRegret A j q mu E (w x)‖ ≤ informationCap q
    rw [Real.norm_eq_abs,abs_of_nonneg hn]
    exact hcap x
  have hgood : Integrable good P := by
    apply Integrable.of_bound (by dsimp [good];fun_prop) (2*marginModulus q+tau)
    apply ae_of_all
    intro x
    have habs : |mu-(mhat x).val| ≤ 1 := abs_le.mpr ⟨by linarith [hmu.1,(mhat x).property.2],by linarith [hmu.2,(mhat x).property.1]⟩
    have hL : 0 ≤ marginModulus q := by unfold marginModulus;positivity
    have ht : 0 ≤ tau := by dsimp [tau];unfold informationCap;positivity
    rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ good x by dsimp [good];positivity)]
    dsimp [good]
    nlinarith
  have hg := hgood.indicator hB.compl
  have hb : Integrable (B.indicator (fun _ => informationCap q)) P := (integrable_const _).indicator hB
  have hpoint (x : Ω) : oracleRegret A j q mu E (w x) ≤
      Bᶜ.indicator good x+B.indicator (fun _ => informationCap q) x := by
    have hh := label_split A j (world_parameters q j hq hA).1
      (world_has_alternative q j hq A hA) q mu (by exact_mod_cast (show 1 ≤ q by omega))
      hmu.1 hmu.2 E (fun x => (Ahat x).val) (fun x => (mhat x).val) (fun _ => tau) w
      (fun x => (mhat x).property) (fun _ => by dsimp [tau];unfold informationCap;positivity) hf
      (fun x => full_solver_contract _ j (world_parameters q j hq (Ahat x).property).1
        (world_has_alternative q j hq _ (Ahat x).property) q (mhat x).val (by positivity)
        (mhat x).property.1 (mhat x).property.2 H hH) x
    by_cases hx : (Ahat x).val=A <;> simpa [B,hx,good,tau] using hh
  refine ⟨hi,?_⟩
  have h := integral_mono hi (hg.add hb) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add hg hb,integral_indicator_const _ hB] at h
  have hcompl : Bᶜ={x | (Ahat x).val=A} := by ext x;simp [B]
  rw [hcompl] at h
  simpa [B,good,tau,E,w,smul_eq_mul,mul_comm] using h

#print axioms solver_statistic_measurable
#print axioms expected_solver_regret
end
end CIGAMF.P13.D6FiniteSolverExpectation
