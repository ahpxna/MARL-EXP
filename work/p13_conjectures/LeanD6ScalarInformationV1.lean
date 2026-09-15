import «LeanD6ThreeClassPhaseV1»

/-! # D6: the B-scalar information, corrected -- and the primal/dual shape the full
game needs.

`LeanD6ThreeClassPhaseV1` says in prose that the phase transition comes from "two
disjoint blind directions".  That is FALSE for the formula actually in use.  The
B-scalar's per-sample information against the alternative `(d, x)` is

    I_B(d, x) = ( d μ²/q + (q - d) x²/q ) / 2,

which at `q = 3, μ = 1/4, d = 1, x = 0` equals `1/96 > 0`.  The B-scalar has NO blind
direction at all once `μ > 0` and `d ≥ 1`.  The A-pair does have one (`x = g`, by
`IA_eq_zero_iff`).  So the correct statement is an ASYMMETRY, not disjointness, and the
phase boundary has to be explained by a certified value gap, not by blindness.

This file also supplies the two certificate shapes the full-game claim needs, each
quantified over EVERY legal query and EVERY alternative -- not only over scalars and
pairs -- and the clipped-nuisance lemma the boundary `ν ∈ {0,1}` requires.

## WHAT IS PROVED

* `IB_at_zero` — `I_B(1, 0) = 1/96` at `q = 3, μ = 1/4`: the B-scalar is NOT blind at
  `x = 0`, so the old explanation is retracted.
* `IB_pos`, `IB_never_blind` — it is positive for every `x`, whenever `μ > 0`, `1 ≤ d`,
  `d ≤ q`.
* `blindness_asymmetry` — the A-pair has a blind direction and the B-scalar has none.
* `clipped_min` — the nuisance minimiser CLAMPED to `[0,1]`: the minimum of
  `Aν²/2 - Bν` over the interval is at `clamp(B/A)`, including both boundary cases.
  This is the step the uncapped profile silently skipped.
* `primal_lower` — a design's value is at least `V` iff every alternative costs `≥ V`.
* `dual_over_all_queries` — **the dual certificate: a mixture `ρ` of alternatives with
  `∑_λ ρ_λ I_λ(e) ≤ V κ_e` for EVERY legal query `e` caps EVERY legal design at `V`.**
  The hypothesis is universally quantified over `e`, so it is not a scalar/pair-only
  check.

## WHAT THIS DOES NOT ESTABLISH

- No specific `ρ`, `V` or design is exhibited here: the certificates are the SHAPES the
  full-game claim must be filled with, and filling them for the D6 orbit family is a
  computation, not a theorem in this file.
- `t_end` is not a phase boundary, and no phase boundary is proved here.
- The information formulas are the ones the corpus uses; they are not re-derived from
  the sampling model in this file.
-/

namespace CIGAMF.P13.D6ScalarInformation

open Finset CIGAMF.P13.D6ThreeClassPhase

/-- The B-scalar's per-sample information against `(d, x)`. -/
def IB (Q dd mu x : ℚ) : ℚ := (dd * mu ^ 2 / Q + (Q - dd) * x ^ 2 / Q) / 2

/-- **The retraction**: at `q = 3, μ = 1/4, d = 1` the B-scalar has information `1/96`
at `x = 0`.  It is not blind there. -/
theorem IB_at_zero : IB 3 1 (1/4) 0 = 1/96 := by
  unfold IB
  norm_num

theorem IB_pos (Q dd mu x : ℚ) (hQ : 3 ≤ Q) (hd : 1 ≤ dd) (hdQ : dd ≤ Q)
    (hmu : 0 < mu) : 0 < IB Q dd mu x := by
  unfold IB
  have hQ0 : (0:ℚ) < Q := by linarith
  have h1 : 0 < dd * mu ^ 2 / Q := by positivity
  have h2 : 0 ≤ (Q - dd) * x ^ 2 / Q := by
    apply div_nonneg _ (le_of_lt hQ0)
    exact mul_nonneg (by linarith) (sq_nonneg x)
  linarith

theorem IB_never_blind (Q dd mu : ℚ) (hQ : 3 ≤ Q) (hd : 1 ≤ dd) (hdQ : dd ≤ Q)
    (hmu : 0 < mu) : ∀ x : ℚ, IB Q dd mu x ≠ 0 :=
  fun x => ne_of_gt (IB_pos Q dd mu x hQ hd hdQ hmu)

/-- **The asymmetry.**  The A-pair is blind in one direction; the B-scalar is blind in
none.  "Two disjoint blind directions" is therefore not the mechanism. -/
theorem blindness_asymmetry (Q dd g : ℚ) (hQ : 3 ≤ Q) (hd : 1 ≤ dd) (hdQ : dd ≤ Q)
    (hmu : (0:ℚ) < 1/4) :
    (IA Q dd g g = 0) ∧ (∀ x : ℚ, IB Q dd (1/4) x ≠ 0) := by
  refine ⟨?_, IB_never_blind Q dd (1/4) hQ hd hdQ hmu⟩
  exact (IA_eq_zero_iff Q dd g g hQ hd).2 rfl

/-- **The clipped nuisance.**  Minimising `Aν²/2 - Bν` over `ν ∈ [0,1]` -- the minimum
sits at the clamp, and both boundary cases are covered. -/
theorem clipped_min (A B nu : ℝ) (hA : 0 < A) (h0 : 0 ≤ nu) (h1 : nu ≤ 1) :
    A / 2 * (max 0 (min 1 (B / A))) ^ 2 - B * (max 0 (min 1 (B / A)))
      ≤ A / 2 * nu ^ 2 - B * nu := by
  rcases le_or_gt (B / A) 0 with hlo | hlo
  · have hB : B ≤ 0 := by
      by_contra hposB
      push_neg at hposB
      have hdp : 0 < B / A := div_pos hposB hA
      linarith
    have hclamp : max 0 (min 1 (B / A)) = 0 := by
      have : min 1 (B / A) ≤ 0 := le_trans (min_le_right _ _) hlo
      simp [max_eq_left this]
    rw [hclamp]
    nlinarith [sq_nonneg nu, hB, h0]
  · rcases le_or_gt 1 (B / A) with hhi | hhi
    · have hclamp : max 0 (min 1 (B / A)) = 1 := by
        rw [min_eq_left hhi]
        simp
      have hBA : A ≤ B := by
        rw [le_div_iff₀ hA] at hhi
        linarith
      rw [hclamp]
      have hnu : 0 ≤ 1 - nu := by linarith
      have hstep1 : A / 2 * (1 - nu) * (1 + nu) ≤ A * (1 - nu) := by
        nlinarith [mul_nonneg hA.le (sq_nonneg (1 - nu))]
      have hstep2 : A * (1 - nu) ≤ B * (1 - nu) := mul_le_mul_of_nonneg_right hBA hnu
      nlinarith [hstep1, hstep2]
    · have hclamp : max 0 (min 1 (B / A)) = B / A := by
        rw [min_eq_right (le_of_lt hhi)]
        exact max_eq_right (le_of_lt hlo)
      rw [hclamp]
      have hkey : A / 2 * (nu - B / A) ^ 2 ≥ 0 := by positivity
      have hexp : A / 2 * nu ^ 2 - B * nu - (A / 2 * (B / A) ^ 2 - B * (B / A))
          = A / 2 * (nu - B / A) ^ 2 := by
        field_simp
        ring
      linarith [hexp ▸ hkey]

section Certificates

variable {E L : Type*} [Fintype E] [Fintype L] [Nonempty L]

/-- The primal side: a design's value is at least `V` exactly when every alternative
costs at least `V`. -/
theorem primal_lower (w : E → ℝ) (I : L → E → ℝ) (V : ℝ)
    (h : ∀ l, V ≤ ∑ e, w e * I l e) :
    V ≤ (univ : Finset L).inf' univ_nonempty (fun l => ∑ e, w e * I l e) :=
  Finset.le_inf' _ _ fun l _ => h l

/-- **The dual certificate, over EVERY legal query.**  A mixture `ρ` of alternatives
whose average information at every query `e` is at most `V κ_e` caps every legal design
at `V`. -/
theorem dual_over_all_queries (I : L → E → ℝ) (kap w : E → ℝ) (rho : L → ℝ) (V : ℝ)
    (hw : ∀ e, 0 ≤ w e) (hrho : ∀ l, 0 ≤ rho l) (hrsum : ∑ l, rho l = 1)
    (hbudget : ∑ e, kap e * w e = 1)
    (hcut : ∀ e, ∑ l, rho l * I l e ≤ V * kap e)
    (Jval : ℝ) (hJ : ∀ l, Jval ≤ ∑ e, w e * I l e) :
    Jval ≤ V := by
  classical
  have h1 : Jval ≤ ∑ l, rho l * (∑ e, w e * I l e) := by
    have hstep : ∑ l, rho l * Jval ≤ ∑ l, rho l * (∑ e, w e * I l e) :=
      Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hJ l) (hrho l)
    have hc : ∑ l, rho l * Jval = Jval := by rw [← Finset.sum_mul, hrsum, one_mul]
    linarith [hc ▸ hstep]
  have hswap : ∑ l, rho l * (∑ e, w e * I l e) = ∑ e, w e * (∑ l, rho l * I l e) := by
    have hl : ∀ l : L, rho l * (∑ e, w e * I l e) = ∑ e, w e * (rho l * I l e) :=
      fun l => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun e _ => by ring
    simp_rw [hl]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun e _ => by rw [Finset.mul_sum]
  have h2 : ∑ e, w e * (∑ l, rho l * I l e) ≤ ∑ e, w e * (V * kap e) :=
    Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (hcut e) (hw e)
  have h3 : ∑ e, w e * (V * kap e) = V := by
    have : ∑ e, w e * (V * kap e) = V * ∑ e, kap e * w e := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun e _ => by ring
    rw [this, hbudget, mul_one]
  linarith [h1, hswap ▸ h1, h2, h3]

end Certificates

#print axioms IB_at_zero
#print axioms IB_pos
#print axioms IB_never_blind
#print axioms blindness_asymmetry
#print axioms clipped_min
#print axioms primal_lower
#print axioms dual_over_all_queries

end CIGAMF.P13.D6ScalarInformation
