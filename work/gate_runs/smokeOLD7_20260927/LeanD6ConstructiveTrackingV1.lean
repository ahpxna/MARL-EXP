import «LeanFiniteAllocationTrackerV1»
import «LeanD6AllocationTrackingStabilityV1»

/-! The discrepancy hypothesis in the D6 stability theorem is supplied by an
explicit legal-query schedule. Targets may change at every step. The bound is
finite but deliberately not claimed sharp in the growing-q regime. -/
namespace CIGAMF.P13.D6ConstructiveTracking
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6AllocationRiskBridge CIGAMF.P13.D6LocalOracleRegret
open CIGAMF.P13.D6AllocationTrackingStability
open CIGAMF.P13.FiniteAllocationTracker
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def averageWeight (w : ℕ → Measurement n → ℝ) (N : ℕ) (e : Measurement n) :=
  (∑ t ∈ range N,w t e)/(N:ℝ)

set_option maxHeartbeats 800000 in
/-- For every adaptive sequence of legal simplex targets there exists a legal
realized query schedule whose oracle regret is within cap(q)*|E|^2/N of the
regret of the average intended allocation. The assertion is pathwise. -/
theorem realized_tracking (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (halt : ∃ A' nu,Admissible A A' j nu) (q mu : ℝ)
    (hq : 0 ≤ q) (hm : 0 ≤ mu) (hm1 : mu ≤ 1)
    (E : Finset (Measurement n)) (hE : E.Nonempty)
    (w : ℕ → Measurement n → ℝ) (hl : ∀ e ∈ E,Legal j q e)
    (hw0 : ∀ t e,e ∈ E → 0 ≤ w t e) (hw : ∀ t,∑ e ∈ E,w t e=1) :
    ∃ schedule : ℕ → Measurement n,
      (∀ t,schedule t ∈ E ∧ Legal j q (schedule t)) ∧
      ∀ N : ℕ,0 < N →
        oracleRegret A j q mu E (fun e => (((range N).filter (fun t => schedule t=e)).card:ℝ)/(N:ℝ)) ≤
          oracleRegret A j q mu E (averageWeight w N)+informationCap q*(E.card:ℝ)^2/(N:ℝ) := by
  letI : Nonempty E := hE.to_subtype
  let v : ℕ → E → ℝ := fun t e => w t e.val
  have hv0 : ∀ t e,0 ≤ v t e := fun t e => hw0 t e.val e.property
  have hv : ∀ t,∑ e : E,v t e=1 := by
    intro t
    change (∑ e : E,w t e.val)=1
    rw [sum_coe_sort]
    exact hw t
  let schedule : ℕ → Measurement n := fun t => (FiniteAllocationTracker.query v t).val
  refine ⟨schedule,fun t => ⟨(FiniteAllocationTracker.query v t).property,hl _ (FiniteAllocationTracker.query v t).property⟩,?_⟩
  intro N hN
  let C : Measurement n → ℕ := fun e => ((range N).filter (fun t => schedule t=e)).card
  have htrack : ∀ e ∈ E, |(C e:ℝ)-(N:ℝ)*averageWeight w N e| ≤ (E.card:ℝ) := by
    intro e he
    let i : E := ⟨e,he⟩
    have hcnt : C e=counts v N i := by
      rw [counts_eq_occurrences]
      change ((range N).filter (fun t => schedule t=e)).card = _
      apply congrArg Finset.card
      ext t
      simp only [mem_filter]
      have heq : schedule t=e ↔ FiniteAllocationTracker.query v t=i := by
        exact ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩
      exact and_congr_right (fun _ => heq)
    have h := discrepancy_bound v hv0 hv N i
    have ht : (N:ℝ)*averageWeight w N e=target v N i := by
      unfold averageWeight target
      have hn : (N:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
      dsimp [v,i]
      field_simp
    rw [hcnt,ht]
    simpa using h
  have hwavg : ∀ e ∈ E,0 ≤ averageWeight w N e := by
    intro e he
    exact div_nonneg (sum_nonneg (fun t _ => hw0 t e he)) (by positivity)
  have hh := tracked_counts_regret A j hj halt q mu hq hm hm1 E (averageWeight w N) C N hN E.card hl hwavg htrack
  simpa [C,pow_two,mul_assoc] using hh

lemma world_has_alternative (r : ℕ) (j : I (2*r+1)) (hr : 2 ≤ r)
    (A : Finset (I (2*r+1))) (hA : A ∈ worlds r j) :
    ∃ A' nu,Admissible A A' j nu := by
  have hp := world_parameters r j hr hA
  have ha : A.Nonempty := card_pos.mp (by rw [hp.2.1];omega)
  have hb : (others A j).Nonempty := card_pos.mp (by have hc := hp.2.2.2;omega)
  obtain ⟨a,ha⟩ := ha
  obtain ⟨b,hb⟩ := hb
  refine ⟨D6AllocationFiniteBridge.swapped A a b,0,?_,?_,?_,by norm_num,by norm_num⟩
  · exact D6AllocationFiniteBridge.swapped_ne A j a b hb
  · exact D6AllocationFiniteBridge.swapped_card A j a b ha hb
  · exact D6AllocationFiniteBridge.swapped_j_not A j a b hp.1 hb

/-- Averaging target allocations can only improve their worst-alternative
information relative to the average of their individual values. -/
theorem average_allocation_value (A : Finset (I n)) (j : I n)
    (halt : ∃ A' nu,Admissible A A' j nu)
    (mu : ℝ) (E : Finset (Measurement n)) (w : ℕ → Measurement n → ℝ)
    (hw0 : ∀ t e,e ∈ E → 0 ≤ w t e) (N : ℕ) (hN : 0 < N) :
    (∑ t ∈ range N,allocationValue A j mu E (w t))/(N:ℝ) ≤
      allocationValue A j mu E (averageWeight w N) := by
  apply le_csInf (value_nonempty A j halt mu E (averageWeight w N))
  rintro z ⟨A',nu,ha,rfl⟩
  have hh := sum_le_sum (fun t (_ : t ∈ range N) =>
    allocationValue_le_actual A A' j mu nu E (w t) (hw0 t) ha)
  have hh' := div_le_div_of_nonneg_right hh (by positivity : (0:ℝ) ≤ N)
  convert hh' using 1
  unfold averageWeight
  simp only [sum_div,div_mul_eq_mul_div]
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  rw [sum_mul]
  apply sum_congr rfl
  intro t ht
  ring

/-- The oracle regret of the averaged target is at most the average target
regret. Together with realized_tracking this gives the complete deterministic
tracking contribution, before adding statistical estimation and discovery. -/
theorem average_oracle_regret (A : Finset (I n)) (j : I n)
    (halt : ∃ A' nu,Admissible A A' j nu) (q mu : ℝ)
    (E : Finset (Measurement n)) (w : ℕ → Measurement n → ℝ)
    (hw0 : ∀ t e,e ∈ E → 0 ≤ w t e) (N : ℕ) (hN : 0 < N) :
    oracleRegret A j q mu E (averageWeight w N) ≤
      (∑ t ∈ range N,oracleRegret A j q mu E (w t))/(N:ℝ) := by
  have hv := average_allocation_value A j halt mu E w hw0 N hN
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have hh : (∑ t ∈ range N,(oracleValue A j q mu-allocationValue A j mu E (w t))) ≤
      ∑ t ∈ range N,oracleRegret A j q mu E (w t) := by
    apply sum_le_sum;intro t ht;exact le_max_right _ _
  simp only [sum_sub_distrib,sum_const,card_range,nsmul_eq_mul] at hh
  have hd := div_le_div_of_nonneg_right hh hNp.le
  have he : ((N:ℝ)*oracleValue A j q mu-∑ t ∈ range N,allocationValue A j mu E (w t))/(N:ℝ)=
      oracleValue A j q mu-(∑ t ∈ range N,allocationValue A j mu E (w t))/(N:ℝ) := by field_simp
  rw [he] at hd
  unfold oracleRegret at hd ⊢
  apply max_le
  · exact div_nonneg (sum_nonneg (fun t _ => le_max_left _ _)) hNp.le
  · linarith

#print axioms realized_tracking
#print axioms average_allocation_value
#print axioms average_oracle_regret
#print axioms world_has_alternative
end
end CIGAMF.P13.D6ConstructiveTracking
