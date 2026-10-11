import «LeanD6FiniteGridAllocationV1»

/-! The finite D6 solver is a measurable function of the decoded label and
estimated margin. Combined with the tracker theorem this gives an adapted
query process; the true label is not an input to the policy. -/
namespace CIGAMF.P13.D6FiniteSolverMeasurability
open scoped BigOperators
open Finset MeasureTheory
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6AllocationRiskBridge CIGAMF.P13.D6LocalOracleRegret
open CIGAMF.P13.D6AllocationTrackingStability CIGAMF.P13.D6OracleValueStability
open CIGAMF.P13.D6ConstructiveTracking CIGAMF.P13.D6FiniteGridAllocation
open CIGAMF.P13.FiniteGridSolver CIGAMF.P13.FiniteTrackerCausality
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}
abbrev Margin := Set.Icc (0:ℝ) 1

lemma score_continuous (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (halt : ∃ A' nu,Admissible A A' j nu) (q : ℝ) (hq : 1 ≤ q)
    (E : Finset (Measurement n)) (w : Measurement n → ℝ) (hf : Feasible j q E w) :
    Continuous (fun m : Margin => allocationValue A j m.val E w) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hc : Continuous (fun y : Margin => marginModulus q*|y.val-x.val|) := by fun_prop
  have ht : Filter.Tendsto (fun y : Margin => marginModulus q*|y.val-x.val|)
      (nhds x) (nhds 0) := by simpa using (hc.continuousAt (x:=x)).tendsto
  apply squeeze_zero (fun y => norm_nonneg _) ?_ ht
  intro y
  simpa only [Real.norm_eq_abs] using allocation_margin_modulus A j hj halt q y.val x.val hq
    y.property.1 y.property.2 x.property.1 x.property.2 E w hf

lemma fixed_label_weight_measurable {Ω : Type*} [MeasurableSpace Ω]
    (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (halt : ∃ A' nu,Admissible A A' j nu) (q : ℝ) (hq : 1 ≤ q)
    (E : Finset (Measurement n)) (hE : E.Nonempty) (hl : ∀ e ∈ E,Legal j q e)
    (H : ℕ) (hH : 0 < H) (mhat : Ω → Margin) (hm : Measurable mhat)
    (e : Measurement n) :
    Measurable (fun x => solverWeight A j (mhat x).val E hE H e) := by
  letI : Nonempty E := hE.to_subtype
  have hs : Measurable (fun x => solve H (fun v : E → ℝ =>
      allocationValue A j (mhat x).val E (liftWeight E v))) := by
    apply solve_measurable
    intro g
    apply (score_continuous A j hj halt q hq E (liftWeight E (weight g)) ?_).measurable.comp hm
    refine ⟨hl,?_,?_⟩
    · intro e he
      simpa [liftWeight,he] using weight_nonneg g (⟨e,he⟩ : E)
    · rw [lift_sum]
      exact weight_total hH g
  exact (measurable_of_finite (fun g : Grid E H => liftWeight E (weight g) e)).comp hs

/-- The estimator may choose any valid label using the observations. -/
theorem data_weight_measurable {Ω : Type*} [MeasurableSpace Ω]
    (q : ℕ) (hq : 2 ≤ q) (j : I (2*q+1))
    (Ahat : Ω → worlds q j) (hA : Measurable Ahat)
    (mhat : Ω → Margin) (hm : Measurable mhat) (H : ℕ) (hH : 0 < H)
    (e : Measurement (2*q+1)) :
    Measurable (fun x => solverWeight (Ahat x).val j (mhat x).val
      (allQueries j q) (allQueries_nonempty j q) H e) := by
  let f (B : worlds q j) (x : Ω) := solverWeight B.val j (mhat x).val
    (allQueries j q) (allQueries_nonempty j q) H e
  have hf (B : worlds q j) : Measurable (f B) :=
    fixed_label_weight_measurable B.val j (world_parameters q j hq B.property).1
      (world_has_alternative q j hq B.val B.property) q
      (by exact_mod_cast (show 1 ≤ q by omega)) _ (allQueries_nonempty j q)
      (fun e he => (allQueries_mem j q e).mp he) H hH mhat hm e
  have hs : Measurable (fun x => ∑ B : worlds q j,{x | Ahat x=B}.indicator (f B) x) := by
    apply Finset.measurable_sum
    intro B hB
    exact (hf B).indicator (measurableSet_eq_fun hA measurable_const)
  convert hs using 1
  funext x
  rw [sum_eq_single (Ahat x)]
  · simp [f]
  · intro B hB hn
    exact Set.indicator_of_notMem (by simpa [eq_comm] using hn) _
  · simp

/-- Actual full-library target on the finite query subtype. -/
def dataTarget {Ω : Type*} (q : ℕ) (j : I (2*q+1))
    (Ahat : Ω → worlds q j) (mhat : Ω → Margin) (H : ℕ)
    (x : Ω) (e : allQueries j q) : ℝ :=
  solverWeight (Ahat x).val j (mhat x).val (allQueries j q) (allQueries_nonempty j q) H e.val

/-- The emitted query is measurable in F_N, before observation N+1. -/
theorem solver_tracker_adapted {Ω : Type*} {m : MeasurableSpace Ω}
    (F : Filtration ℕ m) (q : ℕ) (hq : 2 ≤ q) (j : I (2*q+1))
    (Ahat : ℕ → Ω → worlds q j) (hA : ∀ t,Measurable[F t] (Ahat t))
    (mhat : ℕ → Ω → Margin) (hm : ∀ t,Measurable[F t] (mhat t))
    (H : ℕ → ℕ) (hH : ∀ t,0 < H t) (N : ℕ) :
    letI : MeasurableSpace (allQueries j q) := ⊤
    letI : Nonempty (allQueries j q) := (allQueries_nonempty j q).to_subtype
    Measurable[F N] (fun x => CIGAMF.P13.FiniteAllocationTracker.query
      (fun t => dataTarget q j (Ahat t) (mhat t) (H t) x) N) := by
  letI : MeasurableSpace Ω := m
  letI : MeasurableSpace (allQueries j q) := ⊤
  letI : Nonempty (allQueries j q) := (allQueries_nonempty j q).to_subtype
  apply query_adapted F (fun t => dataTarget q j (Ahat t) (mhat t) (H t))
  intro t e
  exact @data_weight_measurable Ω (F t) q hq j (Ahat t) (hA t) (mhat t) (hm t) (H t) (hH t) e.val

#print axioms score_continuous
#print axioms fixed_label_weight_measurable
#print axioms data_weight_measurable
#print axioms solver_tracker_adapted
end
end CIGAMF.P13.D6FiniteSolverMeasurability
