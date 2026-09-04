import Mathlib

/-! QUARANTINED / PROVED. MASTER↔FUNCTIONAL budget-splitting calculus. -/
namespace CIGAMF.P13.ReferenceResponseBudget

open scoped BigOperators

noncomputable def twoSourceRadius (A B N x : ℝ) : ℝ :=
  A / Real.sqrt x + B / Real.sqrt (N - x)

noncomputable def optimalResponseBudget (A B N : ℝ) : ℝ :=
  N * (A ^ (2/3 : ℝ)) / (A ^ (2/3 : ℝ) + B ^ (2/3 : ℝ))

private lemma div_sqrt_rpow_mul_rpow
    (A x : ℝ) (hA : 0 < A) (hx : 0 < x) :
    (A / Real.sqrt x) ^ (2/3 : ℝ) * x ^ (1/3 : ℝ) =
      A ^ (2/3 : ℝ) := by
  rw [Real.div_rpow hA.le (Real.sqrt_nonneg x), Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul hx.le]
  norm_num
  field_simp

private lemma div_sqrt_rpow_cancel
    (A x : ℝ) (hA : 0 < A) (hx : 0 < x) :
    ((A / Real.sqrt x) ^ (2/3 : ℝ)) ^ (3/2 : ℝ) =
      A / Real.sqrt x := by
  rw [← Real.rpow_mul (by positivity : 0 ≤ A / Real.sqrt x)]
  norm_num

private lemma one_third_rpow_three (x : ℝ) (hx : 0 < x) :
    (x ^ (1/3 : ℝ)) ^ (3 : ℝ) = x := by
  rw [← Real.rpow_mul hx.le]
  norm_num

/-- Two-point Hölder lower bound underlying the response/reference budget
split.  This theorem is independent of the optimizer formula. -/
private theorem holder_two_source_lower
    (A B x y : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hx : 0 < x) (hy : 0 < y) :
    (A ^ (2/3 : ℝ) + B ^ (2/3 : ℝ)) ^ (3/2 : ℝ) /
        Real.sqrt (x + y) ≤
      A / Real.sqrt x + B / Real.sqrt y := by
  let f : Fin 2 → ℝ :=
    ![(A / Real.sqrt x) ^ (2/3 : ℝ),
      (B / Real.sqrt y) ^ (2/3 : ℝ)]
  let g : Fin 2 → ℝ :=
    ![x ^ (1/3 : ℝ), y ^ (1/3 : ℝ)]
  have hpq : Real.HolderConjugate (3/2 : ℝ) 3 := by
    constructor <;> norm_num
  have hh := Real.inner_le_Lp_mul_Lq_of_nonneg
    (Finset.univ : Finset (Fin 2)) hpq (f := f) (g := g)
    (by intro i hi; fin_cases i <;> dsimp [f] <;> positivity)
    (by intro i hi; fin_cases i <;> dsimp [g] <;> positivity)
  simp only [Fin.sum_univ_two] at hh
  dsimp [f, g] at hh
  rw [div_sqrt_rpow_mul_rpow A x hA hx,
    div_sqrt_rpow_mul_rpow B y hB hy,
    div_sqrt_rpow_cancel A x hA hx,
    div_sqrt_rpow_cancel B y hB hy,
    one_third_rpow_three x hx,
    one_third_rpow_three y hy] at hh
  norm_num at hh
  have hpow := Real.rpow_le_rpow
    (by positivity : 0 ≤ A ^ (2/3 : ℝ) + B ^ (2/3 : ℝ)) hh
    (by norm_num : 0 ≤ (3/2 : ℝ))
  rw [Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul (by positivity : 0 ≤ A / Real.sqrt x + B / Real.sqrt y),
    ← Real.rpow_mul (by positivity : 0 ≤ x + y)]
    at hpow
  norm_num at hpow
  rw [← Real.sqrt_eq_rpow] at hpow
  have hsqrt : 0 < Real.sqrt (x + y) := Real.sqrt_pos.2 (add_pos hx hy)
  exact (div_le_iff₀ hsqrt).2 hpow

private lemma base_eq_two_thirds_mul_sqrt
    (A : ℝ) (hA : 0 < A) :
    A = A ^ (2/3 : ℝ) * Real.sqrt (A ^ (2/3 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hA)]
  norm_num
  rw [← Real.rpow_add hA]
  norm_num

private lemma three_halves_eq_mul_sqrt
    (a : ℝ) (ha : 0 < a) :
    a ^ (3/2 : ℝ) = a * Real.sqrt a := by
  calc
    a ^ (3/2 : ℝ) = a ^ (1 + 1/2 : ℝ) := by norm_num
    _ = a ^ (1 : ℝ) * a ^ (1/2 : ℝ) := Real.rpow_add ha 1 (1/2)
    _ = a * Real.sqrt a := by rw [Real.rpow_one, Real.sqrt_eq_rpow]

private theorem optimal_budget_value
    (A B N : ℝ) (hA : 0 < A) (hB : 0 < B) (hN : 0 < N) :
    twoSourceRadius A B N (optimalResponseBudget A B N) =
      (A ^ (2/3 : ℝ) + B ^ (2/3 : ℝ)) ^ (3/2 : ℝ) /
        Real.sqrt N := by
  let a : ℝ := A ^ (2/3 : ℝ)
  let b : ℝ := B ^ (2/3 : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hab : 0 < a + b := add_pos ha hb
  have hrest : N - N * a / (a + b) = N * b / (a + b) := by
    field_simp
    ring
  have hsqrtA : Real.sqrt a ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ha)
  have hsqrtB : Real.sqrt b ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hb)
  have hsqrtN : Real.sqrt N ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hN)
  have hsqrtAB : Real.sqrt (a + b) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hab)
  have hAid : A = a * Real.sqrt a := by
    simpa [a] using base_eq_two_thirds_mul_sqrt A hA
  have hBid : B = b * Real.sqrt b := by
    simpa [b] using base_eq_two_thirds_mul_sqrt B hB
  rw [twoSourceRadius, optimalResponseBudget]
  change A / Real.sqrt (N * a / (a + b)) +
      B / Real.sqrt (N - N * a / (a + b)) = _
  rw [hrest, Real.sqrt_div (mul_nonneg hN.le ha.le),
    Real.sqrt_div (mul_nonneg hN.le hb.le),
    Real.sqrt_mul hN.le, Real.sqrt_mul hN.le]
  change A / (Real.sqrt N * Real.sqrt a / Real.sqrt (a + b)) +
      B / (Real.sqrt N * Real.sqrt b / Real.sqrt (a + b)) =
    (a + b) ^ (3/2 : ℝ) / Real.sqrt N
  rw [hAid, hBid, three_halves_eq_mul_sqrt (a + b) hab]
  field_simp

/-- Continuous relaxation target: response/reference errors with `1/sqrt(n)`
    envelopes imply a 2/3-power optimal allocation law. -/
theorem two_source_budget_split_conjecture
    (A B N x : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hN : 0 < N)
    (hx0 : 0 < x) (hxN : x < N) :
    twoSourceRadius A B N (optimalResponseBudget A B N) ≤
      twoSourceRadius A B N x := by
  rw [optimal_budget_value A B N hA hB hN]
  have hy : 0 < N - x := sub_pos.2 hxN
  simpa [twoSourceRadius, add_sub_cancel_left] using
    holder_two_source_lower A B x (N - x) hA hB hx0 hy

/-- Closed-form minimum corresponding to the same continuous relaxation. -/
theorem two_source_budget_minimum_conjecture
    (A B N : ℝ) (hA : 0 < A) (hB : 0 < B) (hN : 0 < N) :
    twoSourceRadius A B N (optimalResponseBudget A B N) =
      (A ^ (2/3 : ℝ) + B ^ (2/3 : ℝ)) ^ (3/2 : ℝ) / Real.sqrt N := by
  exact optimal_budget_value A B N hA hB hN

end CIGAMF.P13.ReferenceResponseBudget
