import «LeanD6FiniteSolverMeasurabilityV1»
import «LeanD6AdaptiveLabelAccountingV1»

/-! Finite-horizon information-regret of the same concrete tracker whose
adaptedness was proved. Estimation, finite solver error, tracking error, and
wrong-label loss are explicit. N counts exploitation queries; exploration and
discovery queries must be added to total cost separately. -/
namespace CIGAMF.P13.D6FiniteAdaptiveTracking
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6AllocationRiskBridge CIGAMF.P13.D6LocalOracleRegret
open CIGAMF.P13.D6AllocationTrackingStability CIGAMF.P13.D6ConstructiveTracking
open CIGAMF.P13.D6OracleValueStability CIGAMF.P13.D6FiniteGridAllocation
open CIGAMF.P13.D6FiniteSolverMeasurability CIGAMF.P13.D6AdaptiveLabelAccounting
open CIGAMF.P13.FiniteAllocationTracker
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def trackedWeight (E : Finset (Measurement n)) (hE : E.Nonempty)
    (w : ℕ → Measurement n → ℝ) (N : ℕ) : Measurement n → ℝ :=
  letI : Nonempty E := hE.to_subtype
  liftWeight E (fun e => (counts (fun (t : ℕ) (i : E) => w t i.val) N e:ℝ)/(N:ℝ))

/-- These are frequencies of the actual emitted queries, not hypothetical counts. -/
theorem trackedWeight_occurrences (E : Finset (Measurement n)) (hE : E.Nonempty)
    (w : ℕ → Measurement n → ℝ) (N : ℕ) (e : E) :
    letI : Nonempty E := hE.to_subtype
    trackedWeight E hE w N e.val=
      ((((range N).filter (fun t => query (fun (t : ℕ) (i : E) => w t i.val) t=e)).card:ℝ)/(N:ℝ)) := by
  letI : Nonempty E := hE.to_subtype
  unfold trackedWeight
  rw [lift_at,counts_eq_occurrences]

/-- Direct bound for the concrete query/count recursion, valid pathwise. -/
theorem concrete_tracking_bound (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (halt : ∃ A' nu,Admissible A A' j nu) (q mu : ℝ)
    (hq : 0 ≤ q) (hm : 0 ≤ mu) (hm1 : mu ≤ 1)
    (E : Finset (Measurement n)) (hE : E.Nonempty) (w : ℕ → Measurement n → ℝ)
    (hf : ∀ t,Feasible j q E (w t)) (N : ℕ) (hN : 0 < N) :
    oracleRegret A j q mu E (trackedWeight E hE w N) ≤
      (∑ t ∈ range N,oracleRegret A j q mu E (w t))/(N:ℝ)+
        informationCap q*(E.card:ℝ)^2/(N:ℝ) := by
  letI : Nonempty E := hE.to_subtype
  let v : ℕ → E → ℝ := fun t e => w t e.val
  let C : Measurement n → ℕ := fun e => if h : e ∈ E then counts v N ⟨e,h⟩ else 0
  have hv : ∀ t,∑ e : E,v t e=1 := by
    intro t
    rw [sum_coe_sort]
    exact (hf t).2.2
  have htrack : ∀ e ∈ E,|(C e:ℝ)-(N:ℝ)*averageWeight w N e| ≤ (E.card:ℝ) := by
    intro e he
    let i : E := ⟨e,he⟩
    have ht : (N:ℝ)*averageWeight w N e=target v N i := by
      unfold averageWeight target
      dsimp only [v,i]
      field_simp
    have hc : C e=counts v N i := by simp [C,he,i]
    rw [hc,ht]
    simpa using discrepancy_bound v (fun t e => (hf t).2.1 e.val e.property) hv N i
  have havg : ∀ e ∈ E,0 ≤ averageWeight w N e := by
    intro e he
    exact div_nonneg (sum_nonneg (fun t _ => (hf t).2.1 e he)) (by positivity)
  have h := tracked_counts_regret A j hj halt q mu hq hm hm1 E (averageWeight w N) C N hN
    E.card (hf 0).1 havg htrack
  have he : (fun e => (C e:ℝ)/(N:ℝ))=trackedWeight E hE w N := by
    funext e
    by_cases he : e ∈ E <;> simp [C,trackedWeight,liftWeight,he,v]
  rw [he] at h
  have ha := average_oracle_regret A j halt q mu E w (fun t => (hf t).2.1) N hN
  have heq : informationCap q*(E.card:ℝ)*(E.card:ℝ)/(N:ℝ)=
      informationCap q*(E.card:ℝ)^2/(N:ℝ) := by ring
  rw [heq] at h
  linarith

/-- The true label is used only to evaluate loss. Targets use the decoded label. -/
theorem adaptive_exploitation_bound (q : ℕ) (hq : 2 ≤ q) (j : I (2*q+1))
    (A : Finset (I (2*q+1))) (hA : A ∈ worlds q j) (mu : ℝ) (hm : mu ∈ Set.Icc 0 1)
    (Ahat : ℕ → worlds q j) (mhat : ℕ → Margin) (H : ℕ → ℕ) (hH : ∀ t,0 < H t)
    (N : ℕ) (hN : 0 < N) :
    let E := allQueries j q
    let w := fun t => solverWeight (Ahat t).val j (mhat t).val E (allQueries_nonempty j q) (H t)
    oracleRegret A j q mu E (trackedWeight E (allQueries_nonempty j q) w N) ≤
      (∑ t ∈ range N,if (Ahat t).val=A then
        2*marginModulus q*|mu-(mhat t).val|+informationCap q*(E.card:ℝ)^2/(H t:ℝ)
        else informationCap q)/(N:ℝ)+informationCap q*(E.card:ℝ)^2/(N:ℝ) := by
  dsimp only
  let E := allQueries j q
  let w := fun t => solverWeight (Ahat t).val j (mhat t).val E (allQueries_nonempty j q) (H t)
  have hf (t : ℕ) : Feasible j q E (w t) :=
    solver_feasible _ j q _ E (allQueries_nonempty j q)
      (fun e he => (allQueries_mem j q e).mp he) (H t) (hH t)
  have hh := concrete_tracking_bound A j (world_parameters q j hq hA).1
    (world_has_alternative q j hq A hA) q mu (by positivity) hm.1 hm.2 E
    (allQueries_nonempty j q) w hf N hN
  have hpoint (t : ℕ) : oracleRegret A j q mu E (w t) ≤
      if (Ahat t).val=A then 2*marginModulus q*|mu-(mhat t).val|+
        informationCap q*(E.card:ℝ)^2/(H t:ℝ) else informationCap q := by
    by_cases ha : (Ahat t).val=A
    · rw [if_pos ha]
      dsimp only [w]
      rw [ha]
      exact estimated_full_solver_regret A j (world_parameters q j hq hA).1
        (world_has_alternative q j hq A hA) q mu _ (by exact_mod_cast (show 1≤q by omega))
        hm.1 hm.2 (mhat t).property.1 (mhat t).property.2 (H t) (hH t)
    · rw [if_neg ha]
      exact oracle_regret_cap A j (world_parameters q j hq hA).1
        (world_has_alternative q j hq A hA) q mu (by positivity) hm.1 hm.2 E (w t) (hf t).2.1
  exact hh.trans (add_le_add (div_le_div_of_nonneg_right
    (sum_le_sum (fun t _ => hpoint t)) (show (0:ℝ) ≤ N by positivity)) le_rfl)

/-- Raw cost bookkeeping keeps every discovery/exploration query visible. -/
theorem total_query_count (q rounds discovery exploitation : ℕ) :
    discovery+(2*q+1)*rounds+exploitation=
      exploitation+discovery+(2*q+1)*rounds := by omega

/-- Explicit crude library size bound for studying growing dimension. -/
theorem full_library_size (j : I n) (q : ℝ) :
    (allQueries j q).card ≤ (n+1)+2*2^(n+1) := by
  have h := card_le_univ (s:=allQueries j q)
  simpa [Measurement,I,Fintype.card_sum,Fintype.card_prod,mul_comm] using h

#print axioms trackedWeight_occurrences
#print axioms concrete_tracking_bound
#print axioms adaptive_exploitation_bound
#print axioms total_query_count
#print axioms full_library_size
end
end CIGAMF.P13.D6FiniteAdaptiveTracking
