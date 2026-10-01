import «LeanPaperBWorldsV1»
import «LeanPaperBHoeffdingV1»

/-!
# Paper B: the scope of the `hdiff` retraction, and the union bound over tests

Two corrections, both of them narrowings of something this corpus claimed too broadly.

## 1. `self_difference_not_a_density` is about ONE first difference, not about all orders

`LeanPaperBWorldsV1.self_difference_not_a_density` proves that `q + D_s q` is negative
somewhere, for `q` a single Gaussian kernel and `s > 0`.  That is a genuine refutation of
the composition that was in use, and it stands.  What does NOT follow -- and what the
surrounding prose said -- is that `q + D_{b_1} ... D_{b_r} q` fails to be a density at every
order.  At order two it is a density whenever `q` is:

    q + D_s D_s q = q/2 + q(. - 2s)/4 + q(. + 2s)/4,

a convex combination of translates.  `second_difference_shape` is that identity and
`second_difference_nonneg` is the consequence.  So the retraction is of a specific
composition at first order, and the scope is corrected here rather than left overstated.

## 2. The budget for `J` tests carries `log(J/delta)`

`log_budget_suffices` bounds one test.  A decoder that runs `J` of them and needs all of
them right pays a union bound, so each test runs at level `delta/J` and the budget becomes
`8 log(J/delta)/g^2`.  `union_budget_suffices` is that statement, with the union taken over
a finite index set.
-/

namespace CIGAMF.P13.PaperBScope

open MeasureTheory
open CIGAMF.P13.PaperBRates
open CIGAMF.P13.PaperBHoeffding

/-! ## The second difference of a density is a density -/

/-- **The second symmetric difference, expanded.**  The result is a convex combination of
three translates, with weights `1/2, 1/4, 1/4`. -/
theorem second_difference_shape (q : ℝ → ℝ) (s y : ℝ) :
    q y + iterDiff q [s, s] y
      = q y / 2 + q (y - 2 * s) / 4 + q (y + 2 * s) / 4 := by
  simp only [iterDiff_cons, iterDiff_nil, symDiff]
  rw [show y - s - s = y - 2 * s from by ring, show y - s + s = y from by ring,
    show y + s - s = y from by ring, show y + s + s = y + 2 * s from by ring]
  ring

/-- **So at order two the object IS a density.**  This is the counterexample that fixes the
scope of the first-order retraction: nonnegativity survives, because the second difference
adds translates rather than subtracting one. -/
theorem second_difference_nonneg (q : ℝ → ℝ) (hq : ∀ y, 0 ≤ q y) (s y : ℝ) :
    0 ≤ q y + iterDiff q [s, s] y := by
  rw [second_difference_shape]
  have h1 := hq y
  have h2 := hq (y - 2 * s)
  have h3 := hq (y + 2 * s)
  linarith

/-- **And its total mass is unchanged**, since the three weights sum to one.  Stated on the
weights alone, which is where the claim lives. -/
theorem second_difference_weights : (1 : ℝ) / 2 + 1 / 4 + 1 / 4 = 1 := by norm_num

/-! ## The union bound over a finite family of tests -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The budget at level `delta/J`.**  Running `J` tests and needing all of them right
costs `log(J/delta)` per test, not `log(1/delta)`. -/
theorem union_budget_value (g δ J : ℝ) (hg : 0 < g) (hδ : 0 < δ) (hJ : 0 < J) :
    hoeffdingSufficient g (δ / J) = 8 * Real.log (J / δ) / g ^ 2 := by
  unfold hoeffdingSufficient
  congr 2
  rw [one_div]
  congr 1
  rw [inv_div]

/-- **The union bound.**  If each of finitely many tests errs with probability at most
`delta / J`, the probability that any of them errs is at most `delta`. -/
theorem union_error_le {ι : Type*} [Fintype ι] (A : ι → Set Ω) (δ : ℝ)
    (hcard : (Fintype.card ι : ℝ) ≠ 0)
    (hA : ∀ j, μ.real (A j) ≤ δ / (Fintype.card ι : ℝ)) :
    μ.real (⋃ j, A j) ≤ δ := by
  classical
  have hle : μ.real (⋃ j, A j) ≤ ∑ j, μ.real (A j) := by
    have h := measureReal_biUnion_finset_le (μ := μ) (Finset.univ : Finset ι) A
    simpa using h
  have hsum : ∑ j, μ.real (A j) ≤ ∑ _j : ι, δ / (Fintype.card ι : ℝ) :=
    Finset.sum_le_sum (fun j _ => hA j)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_div_cancel₀ _ hcard] at hsum
  linarith

/-! ## Audit -/

#print axioms second_difference_shape
#print axioms second_difference_nonneg
#print axioms union_budget_value
#print axioms union_error_le

end CIGAMF.P13.PaperBScope
