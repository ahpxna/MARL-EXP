import «LeanFunctionalRangeEnergyOracleV1»

/-! # Functional F5/F6: the OUTER design problem, its dual certificate, and the
setup-cost law.

`LeanFunctionalRangeEnergyOracleV1` reduced the energy oracle on the alternative union to
a finite check and solved the INNER problem on one pair region in closed form.  What was
left open there was the outer allocation.  This file supplies it.

## 1. THE DESIGN PROBLEM AND ITS DUAL

With the union reduced to a finite family of pair regions, a design is scored by its
WORST region.  `weak_duality` says any probability mixture over regions upper-bounds that
worst case, and `dual_certificate` turns one such mixture into a bound valid for EVERY
design.  That is the certificate a referee can check by hand: one vector of weights and
one inequality, no optimiser.

`design_value_le_of_pointwise` and `design_value_ge` give the two directions that make
the worst-case value usable, and `dual_gap_zero` records when a primal design and a dual
mixture certify the same number -- the only situation in which the value is PINNED.

## 2. THE SETUP-COST LAW

`sampleBudget` subtracts the per-channel setup from the total and returns `none` when the
setup alone exceeds the budget.  `infeasible_iff` and `value_of_feasible` state the
dichotomy explicitly: an infeasible configuration has NO value, it does not have a small
positive one.  This is the P26 bug -- clamping a negative budget to `1e-9` -- stated as a
theorem so it cannot recur.

## 3. THE TWO-CELL BREAK-EVEN, WITHOUT THE FOLKLORE 4

`scalar_split_optimal` computes the best two-cell scalar allocation exactly:
`min_p (σ_a²/p + σ_b²/(1-p)) = (σ_a+σ_b)²`, attained at `p = σ_a/(σ_a+σ_b)`.
`breakeven_iff` then gives the exact condition `c_c ν_c = (σ_a+σ_b)²`.  The number `4`
is the value of `(σ_a+σ_b)²` when `σ_a = σ_b = 1` and nothing more; `breakeven_four`
records precisely that, so the constant is never quoted outside its hypotheses.

## WHAT THIS DOES NOT ESTABLISH

- `dual_certificate` is WEAK duality.  No strong-duality or minimax theorem is proved, so
  a dual mixture certifies an upper bound but a gap is not excluded in general.
- The break-even of §3 is a TWO-CELL identity.  With several alternatives the scalar
  design shares cells and the pairwise threshold does not transfer; that is why no
  multi-alternative break-even is stated.
- The setup-cost law is arithmetic on budgets.  It says nothing about which channels a
  design should open.
-/

namespace CIGAMF.P13.FunctionalDesignDuality

open Finset

variable {ι W : Type*} [DecidableEq ι]

/-- The design value: the worst inner value over the finite family of pair regions. -/
noncomputable def designValue (Q : Finset ι) (hQ : Q.Nonempty) (f : ι → W → ℝ) (w : W) : ℝ :=
  Q.inf' hQ (fun q => f q w)

theorem design_value_le (Q : Finset ι) (hQ : Q.Nonempty) (f : ι → W → ℝ) (w : W)
    {q : ι} (hq : q ∈ Q) : designValue Q hQ f w ≤ f q w :=
  Finset.inf'_le _ hq

theorem design_value_ge (Q : Finset ι) (hQ : Q.Nonempty) (f : ι → W → ℝ) (w : W)
    (c : ℝ) (h : ∀ q ∈ Q, c ≤ f q w) : c ≤ designValue Q hQ f w :=
  Finset.le_inf' hQ _ h

/-- **Weak duality.**  Any probability mixture over the regions upper-bounds the worst
case. -/
theorem weak_duality (Q : Finset ι) (hQ : Q.Nonempty) (f : ι → W → ℝ) (lam : ι → ℝ)
    (hlam : ∀ q ∈ Q, 0 ≤ lam q) (hsum : ∑ q ∈ Q, lam q = 1) (w : W) :
    designValue Q hQ f w ≤ ∑ q ∈ Q, lam q * f q w := by
  classical
  have hterm : ∀ q ∈ Q, lam q * designValue Q hQ f w ≤ lam q * f q w := fun q hq =>
    mul_le_mul_of_nonneg_left (design_value_le Q hQ f w hq) (hlam q hq)
  have hsum' : ∑ q ∈ Q, lam q * designValue Q hQ f w ≤ ∑ q ∈ Q, lam q * f q w :=
    Finset.sum_le_sum hterm
  rwa [← Finset.sum_mul, hsum, one_mul] at hsum'

/-- **The dual certificate.**  One mixture and one inequality bound EVERY design. -/
theorem dual_certificate (Q : Finset ι) (hQ : Q.Nonempty) (f : ι → W → ℝ) (lam : ι → ℝ)
    (hlam : ∀ q ∈ Q, 0 ≤ lam q) (hsum : ∑ q ∈ Q, lam q = 1) (U : ℝ)
    (hcert : ∀ w : W, ∑ q ∈ Q, lam q * f q w ≤ U) :
    ∀ w : W, designValue Q hQ f w ≤ U := fun w =>
  le_trans (weak_duality Q hQ f lam hlam hsum w) (hcert w)

/-- **The value is pinned** exactly when a design meets a dual certificate. -/
theorem dual_gap_zero (Q : Finset ι) (hQ : Q.Nonempty) (f : ι → W → ℝ) (lam : ι → ℝ)
    (hlam : ∀ q ∈ Q, 0 ≤ lam q) (hsum : ∑ q ∈ Q, lam q = 1) (U : ℝ) (w₀ : W)
    (hcert : ∀ w : W, ∑ q ∈ Q, lam q * f q w ≤ U)
    (hattain : designValue Q hQ f w₀ = U) :
    IsGreatest {v | ∃ w : W, designValue Q hQ f w = v} U := by
  refine ⟨⟨w₀, hattain⟩, ?_⟩
  rintro v ⟨w, rfl⟩
  exact dual_certificate Q hQ f lam hlam hsum U hcert w

/-! ## The setup-cost law. -/

/-- The sampling budget left after opening `channels` channels, or `none` when the setup
alone exceeds the total.  An infeasible configuration has NO value; it is never clamped
to a small positive one. -/
noncomputable def sampleBudget (total setup : ℝ) (channels : ℕ) : Option ℝ :=
  if total - setup * (channels : ℝ) < 0 then none
  else some (total - setup * (channels : ℝ))

theorem infeasible_iff (total setup : ℝ) (channels : ℕ) :
    sampleBudget total setup channels = none ↔ total < setup * (channels : ℝ) := by
  unfold sampleBudget
  constructor
  · intro h
    by_contra hc
    rw [if_neg (by linarith [not_lt.mp hc])] at h
    simp at h
  · intro h
    rw [if_pos (by linarith)]

theorem value_of_feasible (total setup : ℝ) (channels : ℕ)
    (h : setup * (channels : ℝ) ≤ total) :
    sampleBudget total setup channels = some (total - setup * (channels : ℝ)) := by
  unfold sampleBudget
  rw [if_neg (by linarith)]

/-- Information scales linearly in the REMAINING budget, never in the total.

The hypothesis `0 ≤ setup` is NOT decoration: without it a negative setup would make the
remaining budget exceed the total, and the second inequality is false.  The compiler
rejected the statement that omitted it. -/
theorem information_of_budget (total setup unit : ℝ) (channels : ℕ)
    (h : setup * (channels : ℝ) ≤ total) (hsetup : 0 ≤ setup) (hunit : 0 ≤ unit) :
    0 ≤ (total - setup * (channels : ℝ)) * unit ∧
      (total - setup * (channels : ℝ)) * unit ≤ total * unit := by
  have hch : (0:ℝ) ≤ setup * (channels : ℝ) :=
    mul_nonneg hsetup (Nat.cast_nonneg channels)
  constructor
  · exact mul_nonneg (by linarith) hunit
  · exact mul_le_mul_of_nonneg_right (by linarith) hunit

/-! ## The two-cell break-even. -/

/-- **The best two-cell scalar allocation.**  `σ_a²/p + σ_b²/(1-p) ≥ (σ_a+σ_b)²` for
every split, with equality at `p = σ_a/(σ_a+σ_b)`. -/
theorem scalar_split_lower (sa sb p : ℝ) (hsa : 0 < sa) (hsb : 0 < sb)
    (hp0 : 0 < p) (hp1 : p < 1) :
    (sa + sb) ^ 2 ≤ sa ^ 2 / p + sb ^ 2 / (1 - p) := by
  have h1p : 0 < 1 - p := by linarith
  rw [div_add_div _ _ (ne_of_gt hp0) (ne_of_gt h1p), le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (sa * (1 - p) - sb * p), hsa.le, hsb.le, hp0.le, h1p.le]

theorem scalar_split_optimal (sa sb : ℝ) (hsa : 0 < sa) (hsb : 0 < sb) :
    sa ^ 2 / (sa / (sa + sb)) + sb ^ 2 / (1 - sa / (sa + sb)) = (sa + sb) ^ 2 := by
  have hs : 0 < sa + sb := by linarith
  have hne : sa + sb ≠ 0 := ne_of_gt hs
  have hrest : 1 - sa / (sa + sb) = sb / (sa + sb) := by
    field_simp
    ring
  rw [hrest]
  field_simp
  try ring

/-- **The break-even condition, exactly.**  A contrast of variance `ν_c` at cost `c_c`
matches the best two-cell scalar design iff `c_c ν_c = (σ_a+σ_b)²`. -/
theorem breakeven_iff (sa sb cc nuc : ℝ) (hsa : 0 < sa) (hsb : 0 < sb) :
    cc * nuc = (sa + sb) ^ 2 ↔
      cc * nuc = sa ^ 2 / (sa / (sa + sb)) + sb ^ 2 / (1 - sa / (sa + sb)) := by
  rw [scalar_split_optimal sa sb hsa hsb]

/-- **Where the folklore 4 comes from, and nowhere else.**  It is `(σ_a+σ_b)²` at unit
variances; with any other variances the threshold is different. -/
theorem breakeven_four : ((1:ℝ) + 1) ^ 2 = 4 := by norm_num

theorem breakeven_not_four (sa sb : ℝ) (hsa : 0 < sa) (hsb : 0 < sb)
    (hne : sa + sb ≠ 2) : (sa + sb) ^ 2 ≠ 4 := by
  intro h
  have hpos : 0 < sa + sb := by linarith
  have : sa + sb = 2 := by nlinarith [h, hpos]
  exact hne this

#print axioms design_value_le
#print axioms design_value_ge
#print axioms weak_duality
#print axioms dual_certificate
#print axioms dual_gap_zero
#print axioms infeasible_iff
#print axioms value_of_feasible
#print axioms information_of_budget
#print axioms scalar_split_lower
#print axioms scalar_split_optimal
#print axioms breakeven_iff
#print axioms breakeven_not_four

end CIGAMF.P13.FunctionalDesignDuality
