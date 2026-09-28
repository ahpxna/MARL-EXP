import Mathlib

/-!
# Two closing steps: the stopping assembly (A7) and the breakpoint window (C5).

## WHY THIS MODULE EXISTS

Two loose ends were left explicitly open, and each has a piece that can be closed cleanly
even though the surrounding programme cannot.

**A7.**  The termination analysis ends by converting a tail bound on the stopping time into
a bound on its expectation.  That conversion is the layer-cake identity plus a split at the
horizon, and it is the step at which an argument usually becomes sloppy -- it is tempting to
write `E[tau] <= t_alpha` and call the tail negligible.  `expectation_le_split` does the
conversion honestly: the expectation is at most the split point plus the SUM of the tail
probabilities above it, with no term discarded.

**C5.**  The breakpoint conjecture owes two proofs.  One of them, that `V_m(eta)` strictly
exceeds the free value below the breakpoint, is not open everywhere: the odd-`m` bound proved
in `LeanUnifiedStructuralRelaxedV1` already forces it on an explicit range.
`proved_bound_beats_free` identifies that range exactly as `eta < (m^2-3)/(m^2-1)`, which
turns part of a conjecture into a theorem and names precisely the window that is left.

## WHAT IS PROVED

* `expectation_le_split` -- `E[tau] <= t0 + sum over t in [t0, T) of P(tau > t)`, for a
  bounded integer stopping time on a finite probability space.
* `tail_probability_le_one` -- the supporting fact that each tail probability is at most one,
  which is what makes the first `t0` terms cost at most `t0`.
* `proved_bound_beats_free` -- the relaxed lower bound strictly exceeds the free value
  exactly when `eta < (m^2-3)/(m^2-1)`, so obligation (O2) of the breakpoint conjecture holds
  on that range as a consequence of an already-proved theorem.
* `breakpoint_window_shrinks` -- and the unproved window `[(m^2-3)/(m^2-1), 1)` has width
  `2/(m^2-1)`, so it narrows but never closes.

## WHAT THIS DOES NOT ESTABLISH

- **`expectation_le_split` supplies no tail bound.**  Producing `P(tau > t) <= C t e^{-c sqrt t}`
  for a particular algorithm is the analysis this module does not do; without it the bound is
  a true statement about an unknown quantity.
- Finite sample space and a bounded stopping time.  The unbounded case needs the same
  identity in `ENNReal`, which is standard and not formalised here.
- **`proved_bound_beats_free` does not prove the breakpoint.**  It closes (O2) strictly
  below `(m^2-3)/(m^2-1)` and says nothing at or above it, and obligation (O1) is untouched.
  The conjecture remains a conjecture.
-/

set_option maxHeartbeats 1000000

namespace CIGAMF.P13.PaperClosures

open Finset

/-! ### A7: from a tail to an expectation, without discarding the tail -/

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The probability that the stopping time exceeds `t`. -/
noncomputable def tailProb (p : Ω → ℝ) (tau : Ω → ℕ) (t : ℕ) : ℝ :=
  ∑ ω ∈ univ.filter (fun ω => t < tau ω), p ω

theorem tail_probability_le_one (p : Ω → ℝ) (tau : Ω → ℕ)
    (hp : ∀ ω, 0 ≤ p ω) (hs : ∑ ω, p ω = 1) (t : ℕ) :
    tailProb p tau t ≤ 1 := by
  classical
  unfold tailProb
  rw [← hs]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun ω _ _ => hp ω)

theorem tail_probability_nonneg (p : Ω → ℝ) (tau : Ω → ℕ)
    (hp : ∀ ω, 0 ≤ p ω) (t : ℕ) : 0 ≤ tailProb p tau t := by
  classical
  unfold tailProb
  exact Finset.sum_nonneg fun ω _ => hp ω

/-- The layer-cake identity on a finite space: the expectation of a bounded integer
variable is the sum of its tail probabilities. -/
theorem expectation_eq_sum_tail (p : Ω → ℝ) (tau : Ω → ℕ) (T : ℕ)
    (hT : ∀ ω, tau ω ≤ T) :
    ∑ ω, p ω * (tau ω : ℝ) = ∑ t ∈ range T, tailProb p tau t := by
  classical
  have hcount : ∀ ω : Ω,
      (∑ t ∈ range T, (if t < tau ω then (1 : ℝ) else 0)) = (tau ω : ℝ) := by
    intro ω
    have hfil : (range T).filter (fun t => t < tau ω) = range (tau ω) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨fun h => h.2, fun h => ⟨lt_of_lt_of_le h (hT ω), h⟩⟩
    rw [← Finset.sum_filter, hfil, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
  have hexp : ∀ ω : Ω, p ω * (tau ω : ℝ)
      = ∑ t ∈ range T, p ω * (if t < tau ω then (1 : ℝ) else 0) := by
    intro ω
    rw [← Finset.mul_sum, hcount ω]
  rw [Finset.sum_congr rfl fun ω _ => hexp ω, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold tailProb
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : t < tau ω <;> simp [h]

/-- **The assembly step.**  The expectation is at most the split point plus the whole tail
above it; nothing is discarded. -/
theorem expectation_le_split (p : Ω → ℝ) (tau : Ω → ℕ) (T t0 : ℕ)
    (hp : ∀ ω, 0 ≤ p ω) (hs : ∑ ω, p ω = 1)
    (hT : ∀ ω, tau ω ≤ T) (ht0 : t0 ≤ T) :
    ∑ ω, p ω * (tau ω : ℝ) ≤ (t0 : ℝ) + ∑ t ∈ Ico t0 T, tailProb p tau t := by
  classical
  rw [expectation_eq_sum_tail p tau T hT]
  have hsplit : ∑ t ∈ range T, tailProb p tau t
      = (∑ t ∈ range t0, tailProb p tau t) + ∑ t ∈ Ico t0 T, tailProb p tau t := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact (Finset.sum_Ico_consecutive _ (Nat.zero_le t0) ht0).symm
  rw [hsplit]
  have hhead : ∑ t ∈ range t0, tailProb p tau t ≤ (t0 : ℝ) := by
    have := Finset.sum_le_sum (fun t (_ : t ∈ range t0) =>
      tail_probability_le_one p tau hp hs t)
    simpa using this
  linarith

/-! ### C5: the range on which obligation (O2) is already a theorem -/

/-- **The relaxed lower bound strictly exceeds the free value exactly below
`(m^2-3)/(m^2-1)`.**  Together with `LeanUnifiedStructuralRelaxedV1`, this proves obligation
(O2) of the breakpoint conjecture on that whole range, with no solver involved. -/
theorem proved_bound_beats_free (m eta : ℝ) (hm : 5 ≤ m)
    (hlt : eta < (m ^ 2 - 3) / (m ^ 2 - 1)) :
    2 / ((m + 4) * (m - 1)) < (m + 3 - (m + 1) * eta) / (m * (m + 4)) := by
  have hm0 : (0 : ℝ) < m := by linarith
  have hm1 : (0 : ℝ) < m - 1 := by linarith
  have hm4 : (0 : ℝ) < m + 4 := by linarith
  have hsq : (0 : ℝ) < m ^ 2 - 1 := by nlinarith
  have hden1 : (0 : ℝ) < (m + 4) * (m - 1) := by positivity
  have hden2 : (0 : ℝ) < m * (m + 4) := by positivity
  have hcross : eta * (m ^ 2 - 1) < m ^ 2 - 3 := by
    rw [lt_div_iff₀ hsq] at hlt
    linarith
  rw [div_lt_div_iff₀ hden1 hden2]
  nlinarith [hcross, hm0, hm1, hm4]

/-- The window left unproved has width `2/(m^2-1)`: it narrows without ever closing. -/
theorem breakpoint_window_shrinks (m : ℝ) (hm : 5 ≤ m) :
    1 - (m ^ 2 - 3) / (m ^ 2 - 1) = 2 / (m ^ 2 - 1) := by
  have hsq : (0 : ℝ) < m ^ 2 - 1 := by nlinarith
  field_simp
  ring

#print axioms tail_probability_le_one
#print axioms expectation_eq_sum_tail
#print axioms expectation_le_split
#print axioms proved_bound_beats_free
#print axioms breakpoint_window_shrinks

end CIGAMF.P13.PaperClosures
