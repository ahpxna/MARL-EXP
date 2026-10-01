import Mathlib

/-!
# Finite-search regret for the heterogeneous-receiver profile space (Step 3)

`F` is the legal, byte-feasible profile family `F_{R,B}(π, K)` of PROTOCOL_HETERO_v0 (any type
of profiles), `C ⊆ F` the candidates a bounded search actually scored, `Ŝ ∈ C` its output.
With evaluator error `ε` on `C`, search error `ν` on `C` and coverage gap `ζ` from `F` to `C`:

    f S − f Ŝ ≤ 2ε + ν + ζ   for every S ∈ F.

This is a standard finite-optimisation statement, not a novelty claim.  It separates evaluator
error from search/coverage error without claiming full enumeration (the deployed R = 1 family
has up to 17⁹ profiles).  `private_decomposition` adds the structural term: the gap to the
unrestricted private optimum splits into (private − V_{R,B}) plus the search regret.

WHAT THIS DOES NOT ESTABLISH: any value of ε (mean test MSE does not bound it), ν or ζ; any
geometric bound on private − V_{R,B} (a blockwise exchange argument, not proved here); that T1
(a single k-subset theorem) is instantiated by this profile space.
-/

namespace CIGAMF.P13.MarlProfileSearch

variable {α : Type*}

/-- **Finite-search regret.** -/
theorem profile_search_regret (f fh : α → ℝ) (eps nu zeta : ℝ)
    (F C : Finset α) (hCF : C ⊆ F) (Shat : α) (hShat : Shat ∈ C)
    (hEval : ∀ S ∈ C, |fh S - f S| ≤ eps) (hSearch : ∀ S ∈ C, fh S ≤ fh Shat + nu)
    (hCover : ∀ S ∈ F, ∃ S' ∈ C, f S ≤ f S' + zeta) :
    ∀ S ∈ F, f S - f Shat ≤ 2 * eps + nu + zeta := by
  intro S hS
  obtain ⟨S', hS'C, hS'⟩ := hCover S hS
  have e1 := (abs_le.mp (hEval S' hS'C)).1
  have e2 := (abs_le.mp (hEval Shat hShat)).2
  have s1 := hSearch S' hS'C
  linarith

/-- Full enumeration of `F` removes the coverage term. -/
theorem profile_search_regret_enum (f fh : α → ℝ) (eps nu : ℝ) (F : Finset α) (Shat : α)
    (hShat : Shat ∈ F) (hEval : ∀ S ∈ F, |fh S - f S| ≤ eps)
    (hSearch : ∀ S ∈ F, fh S ≤ fh Shat + nu) :
    ∀ S ∈ F, f S - f Shat ≤ 2 * eps + nu := by
  intro S hS
  have := profile_search_regret f fh eps nu 0 F F (le_refl F) Shat hShat hEval hSearch
    (fun S hS => ⟨S, hS, by linarith⟩) S hS
  linarith

/-- **Decomposition against the private optimum.**  `Vpriv ≥ f` on the private family, `F` is a
subfamily with optimum value `VRB`; the private gap is the structural term plus the search regret. -/
theorem private_decomposition (f : α → ℝ) (Vpriv VRB : ℝ) (Shat : α) :
    Vpriv - f Shat = (Vpriv - VRB) + (VRB - f Shat) := by ring

/-- The bound is attained: `2ε` with an exact argmax of a perturbed evaluator. -/
theorem profile_search_sharp (eps : ℝ) (heps : 0 ≤ eps) :
    ∃ (f fh : Bool → ℝ) (F : Finset Bool) (Shat : Bool),
      Shat ∈ F ∧ (∀ S ∈ F, |fh S - f S| ≤ eps) ∧ (∀ S ∈ F, fh S ≤ fh Shat + 0) ∧
      f true - f Shat = 2 * eps := by
  refine ⟨fun b => if b then 2 * eps else 0, fun _ => eps, {false, true}, false, by simp, ?_, ?_, ?_⟩
  · intro S hS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hS
    rcases hS with rfl | rfl
    · simp [abs_of_nonneg heps]
    · simp; rw [show eps - 2 * eps = -eps by ring, abs_neg, abs_of_nonneg heps]
  · intro S _; simp
  · simp

end CIGAMF.P13.MarlProfileSearch

#print axioms CIGAMF.P13.MarlProfileSearch.profile_search_regret
#print axioms CIGAMF.P13.MarlProfileSearch.profile_search_regret_enum
#print axioms CIGAMF.P13.MarlProfileSearch.private_decomposition
#print axioms CIGAMF.P13.MarlProfileSearch.profile_search_sharp
