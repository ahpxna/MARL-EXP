import «LeanFiniteGridSolverV1»
import «LeanD6OracleValueStabilityV1»

/-! Finite simplex solver for the actual D6 information objective. The complete
legal-query library is finite, so its library-loss term is exactly zero. A grid
with denominator H incurs at most cap(q)*|E|^2/H. The score is the actual
worst-alternative value; this module proves the optimization contract rather
than assuming it. Exact score evaluation is a separate computational concern. -/
namespace CIGAMF.P13.D6FiniteGridAllocation
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6AllocationRiskBridge CIGAMF.P13.D6LocalOracleRegret
open CIGAMF.P13.D6AllocationTrackingStability CIGAMF.P13.D6OracleValueStability
open CIGAMF.P13.FiniteGridSolver
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def liftWeight (E : Finset (Measurement n)) (v : E → ℝ) (e : Measurement n) : ℝ :=
  if h : e ∈ E then v ⟨e,h⟩ else 0

lemma lift_at (E : Finset (Measurement n)) (v : E → ℝ) (e : E) :
    liftWeight E v e.val=v e := by simp [liftWeight]

lemma lift_sum (E : Finset (Measurement n)) (v : E → ℝ) :
    (∑ e ∈ E,liftWeight E v e)=∑ e : E,v e := by
  rw [← sum_coe_sort]
  exact sum_congr rfl (fun e _ => lift_at E v e)

def allQueries (j : I n) (q : ℝ) : Finset (Measurement n) := univ.filter (Legal j q)

lemma allQueries_mem (j : I n) (q : ℝ) (e : Measurement n) :
    e ∈ allQueries j q ↔ Legal j q e := by simp [allQueries]

lemma allQueries_nonempty (j : I n) (q : ℝ) : (allQueries j q).Nonempty :=
  ⟨.inl j,(allQueries_mem j q _).mpr trivial⟩

def solverWeight (A : Finset (I n)) (j : I n) (mu : ℝ)
    (E : Finset (Measurement n)) (hE : E.Nonempty) (H : ℕ) : Measurement n → ℝ :=
  letI : Nonempty E := hE.to_subtype
  liftWeight E (weight (solve H (fun v => allocationValue A j mu E (liftWeight E v))))

lemma solver_feasible (A : Finset (I n)) (j : I n) (q mu : ℝ)
    (E : Finset (Measurement n)) (hE : E.Nonempty) (hl : ∀ e ∈ E,Legal j q e)
    (H : ℕ) (hH : 0 < H) : Feasible j q E (solverWeight A j mu E hE H) := by
  letI : Nonempty E := hE.to_subtype
  refine ⟨hl,?_,?_⟩
  · intro e he
    change 0 ≤ liftWeight E _ e
    rw [show e = (⟨e,he⟩ : E).val from rfl,lift_at]
    exact weight_nonneg _ _
  · change (∑ e ∈ E,liftWeight E _ e)=1
    rw [lift_sum]
    exact weight_total hH _

/-- No optimizer quality is assumed: compare the finite solver with any
simplex on the same library, using the actual information L1 theorem. -/
theorem finite_solver_comparison (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (halt : ∃ A' nu,Admissible A A' j nu) (q mu : ℝ)
    (hq : 0 ≤ q) (hm : 0 ≤ mu) (hm1 : mu ≤ 1)
    (E : Finset (Measurement n)) (hE : E.Nonempty) (hl : ∀ e ∈ E,Legal j q e)
    (H : ℕ) (hH : 0 < H) (w : Measurement n → ℝ)
    (hw : ∀ e ∈ E,0 ≤ w e) (hn : ∑ e ∈ E,w e=1) :
    allocationValue A j mu E w ≤ allocationValue A j mu E (solverWeight A j mu E hE H)+
      informationCap q*(E.card:ℝ)^2/(H:ℝ) := by
  letI : Nonempty E := hE.to_subtype
  let f : (E → ℝ) → ℝ := fun v => allocationValue A j mu E (liftWeight E v)
  have hf : ∀ v u : E → ℝ,(∀ i,0 ≤ v i) → (∀ i,0 ≤ u i) →
      f v ≤ f u+informationCap q*(∑ i,|v i-u i|) := by
    intro v u hv hu
    have h := allocation_one_sided A j hj halt q mu hq hm hm1 E
      (liftWeight E v) (liftWeight E u) hl
      (fun e he => by simpa [liftWeight,he] using hv ⟨e,he⟩)
      (fun e he => by simpa [liftWeight,he] using hu ⟨e,he⟩)
    have he : (∑ e ∈ E,|liftWeight E v e-liftWeight E u e|)=∑ e : E,|v e-u e| := by
      rw [← sum_coe_sort]
      exact sum_congr rfl (fun e _ => by rw [lift_at,lift_at])
    rw [he] at h
    exact h
  have hc : 0 ≤ informationCap q := by unfold informationCap;positivity
  have hn' : (∑ e : E,w e.val)=1 := by rw [sum_coe_sort];exact hn
  have h := solve_error H hH f (informationCap q) hc hf (fun e : E => w e.val)
    (fun e => hw e.val e.property) hn'
  have he : allocationValue A j mu E (liftWeight E (fun e : E => w e.val))=
      allocationValue A j mu E w := by
    unfold allocationValue valueSet
    congr 1
    ext z
    simp only [Set.mem_setOf_eq]
    have hs (A' : Finset (I n)) (nu : ℝ) :
        (∑ e ∈ E,liftWeight E (fun e : E => w e.val) e*information A A' j mu nu e)=
          ∑ e ∈ E,w e*information A A' j mu nu e := by
      exact sum_congr rfl (fun e he => by simp [liftWeight,he])
    simp only [hs]
  dsimp only [f] at h
  rw [he] at h
  simpa only [Fintype.card_coe,solverWeight] using h

/-- Padding a finite library with zero weights preserves its exact value. -/
lemma zero_extension (A : Finset (I n)) (j : I n) (mu : ℝ)
    (F E : Finset (Measurement n)) (hFE : F ⊆ E) (w : Measurement n → ℝ) :
    allocationValue A j mu E (fun e => if e ∈ F then w e else 0)=allocationValue A j mu F w := by
  have hs (A' : Finset (I n)) (nu : ℝ) :
      (∑ e ∈ E,(if e ∈ F then w e else 0)*information A A' j mu nu e)=
        ∑ e ∈ F,w e*information A A' j mu nu e := by
    rw [← sum_subset hFE (by intro e he hn; simp [hn])]
    exact sum_congr rfl (fun e he => by simp [he])
  unfold allocationValue valueSet
  simp only [hs]

/-- Full-library solver contract relative to the original unrestricted Gamma. -/
theorem full_solver_contract (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (halt : ∃ A' nu,Admissible A A' j nu) (q mu : ℝ)
    (hq : 0 ≤ q) (hm : 0 ≤ mu) (hm1 : mu ≤ 1) (H : ℕ) (hH : 0 < H) :
    oracleValue A j q mu ≤
      allocationValue A j mu (allQueries j q)
        (solverWeight A j mu (allQueries j q) (allQueries_nonempty j q) H)+
      informationCap q*((allQueries j q).card:ℝ)^2/(H:ℝ) := by
  apply csSup_le (game_values_nonempty A j q mu)
  rintro v ⟨F,w,hf,rfl⟩
  have hFE : F ⊆ allQueries j q := fun e he => (allQueries_mem j q e).mpr (hf.1 e he)
  let w' : Measurement n → ℝ := fun e => if e ∈ F then w e else 0
  have hn : (∑ e ∈ allQueries j q,w' e)=1 := by
    rw [← sum_subset hFE (by intro e he hn; simp [w',hn])]
    simp only [w']
    rw [sum_congr rfl (fun e he => if_pos he)]
    exact hf.2.2
  have hw : ∀ e ∈ allQueries j q,0 ≤ w' e := by
    intro e he
    by_cases h : e ∈ F <;> simp [w',h,hf.2.1 e]
  have h := finite_solver_comparison A j hj halt q mu hq hm hm1 (allQueries j q)
    (allQueries_nonempty j q) (fun e he => (allQueries_mem j q e).mp he) H hH w' hw hn
  rw [zero_extension A j mu F (allQueries j q) hFE w] at h
  exact h

/-- A07 now receives a proved finite-solver tolerance, with zero library loss. -/
theorem estimated_full_solver_regret (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (halt : ∃ A' nu,Admissible A A' j nu) (q mu mhat : ℝ)
    (hq : 1 ≤ q) (hm : 0 ≤ mu) (hm1 : mu ≤ 1) (hh : 0 ≤ mhat) (hh1 : mhat ≤ 1)
    (H : ℕ) (hH : 0 < H) :
    oracleRegret A j q mu (allQueries j q)
      (solverWeight A j mhat (allQueries j q) (allQueries_nonempty j q) H) ≤
      2*marginModulus q*|mu-mhat|+informationCap q*((allQueries j q).card:ℝ)^2/(H:ℝ) := by
  apply estimated_optimizer_regret A j hj halt q mu mhat _ hq hm hm1 hh hh1
    (by unfold informationCap;positivity) _ _
  · exact solver_feasible A j q mhat _ (allQueries_nonempty j q)
      (fun e he => (allQueries_mem j q e).mp he) H hH
  · exact full_solver_contract A j hj halt q mhat (by linarith) hh hh1 H hH

#print axioms solver_feasible
#print axioms finite_solver_comparison
#print axioms zero_extension
#print axioms full_solver_contract
#print axioms estimated_full_solver_regret
end
end CIGAMF.P13.D6FiniteGridAllocation
