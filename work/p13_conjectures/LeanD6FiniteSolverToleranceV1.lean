import «LeanD6FiniteNuisanceEvaluationV1»

/-! A prescribed positive tolerance determines a finite grid. The selected
weights can be evaluated using finitely many quadratic minima and comparisons.
This is an exact-real construction, not a bit-complexity or floating-point claim. -/
namespace CIGAMF.P13.D6FiniteSolverTolerance
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6LocalOracleRegret
open CIGAMF.P13.D6AllocationRiskBridge CIGAMF.P13.D6AllocationTrackingStability
open CIGAMF.P13.D6FiniteGridAllocation CIGAMF.P13.D6FiniteNuisanceEvaluation
open CIGAMF.P13.FiniteGridSolver
noncomputable section
variable {n : ℕ}

def resolution (q : ℝ) (d : ℕ) (eps : ℝ) : ℕ :=
  ⌈informationCap q*(d:ℝ)^2/eps⌉₊+1

theorem resolution_pos (q : ℝ) (d : ℕ) (eps : ℝ) : 0 < resolution q d eps := by
  unfold resolution
  omega

theorem resolution_error (q : ℝ) (d : ℕ) (eps : ℝ) (heps : 0 < eps) :
    informationCap q*(d:ℝ)^2/(resolution q d eps:ℝ) ≤ eps := by
  have h := Nat.le_ceil (informationCap q*(d:ℝ)^2/eps)
  have hr : informationCap q*(d:ℝ)^2/eps ≤ (resolution q d eps:ℝ) := by
    unfold resolution
    push_cast
    linarith
  apply (div_le_iff₀ (by exact_mod_cast resolution_pos q d eps)).mpr
  have := (div_le_iff₀ heps).mp hr
  nlinarith

/-- Tolerance is achieved by the supplied solver, not assumed as an input. -/
theorem prescribed_tolerance (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (halt : ∃ B nu,Admissible A B j nu) (q mu eps : ℝ)
    (hq : 0 ≤ q) (hm : 0 ≤ mu) (hm1 : mu ≤ 1) (heps : 0 < eps) :
    oracleValue A j q mu ≤ allocationValue A j mu (allQueries j q)
      (solverWeight A j mu (allQueries j q) (allQueries_nonempty j q)
        (resolution q (allQueries j q).card eps))+eps := by
  have h := full_solver_contract A j hj halt q mu hq hm hm1
    (resolution q (allQueries j q).card eps) (resolution_pos _ _ _)
  linarith [resolution_error q (allQueries j q).card eps heps]

def finiteSolverWeight (A : Finset (I n)) (j : I n)
    (halt : ∃ B nu,Admissible A B j nu) (mu : ℝ)
    (E : Finset (Measurement n)) (hE : E.Nonempty) (H : ℕ) : Measurement n → ℝ :=
  letI : Nonempty E := hE.to_subtype
  liftWeight E (weight (solve H (fun v => finiteValue A j halt mu E (liftWeight E v))))

/-- Replacing every grid score by its finite evaluator returns exactly the same
weights, including ties, because the selection rule is fixed. -/
theorem finiteSolverWeight_eq (A : Finset (I n)) (j : I n)
    (halt : ∃ B nu,Admissible A B j nu) (q mu : ℝ)
    (E : Finset (Measurement n)) (hE : E.Nonempty) (hl : ∀ e ∈ E,Legal j q e)
    (H : ℕ) : finiteSolverWeight A j halt mu E hE H=solverWeight A j mu E hE H := by
  letI : Nonempty E := hE.to_subtype
  have hs : (fun g : Grid E H => finiteValue A j halt mu E (liftWeight E (weight g)))=
      (fun g : Grid E H => allocationValue A j mu E (liftWeight E (weight g))) := by
    funext g
    exact (allocationValue_eq_finite A j halt q mu E (liftWeight E (weight g)) hl
      (fun e he => by simpa [liftWeight,he] using weight_nonneg g (⟨e,he⟩ : E))).symm
  unfold finiteSolverWeight solverWeight solve
  rw [hs]

#print axioms resolution_pos
#print axioms resolution_error
#print axioms prescribed_tolerance
#print axioms finiteSolverWeight_eq
end
end CIGAMF.P13.D6FiniteSolverTolerance
