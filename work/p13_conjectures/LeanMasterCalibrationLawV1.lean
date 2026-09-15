import Mathlib

/-! # MASTER: the FULL-CLASS calibration law, and the witness that kills the
four-alternative reading.

`scripts/P6_master_group_calibration.py` solves a game with four alternatives, each
moving ONE item and pinning every other coordinate.  With `θ` free in `ℝ⁴` and the two
group offsets free, that is not the alternative class of the threshold problem: an
alternative may shift a whole group and pay the shift back with the offset, changing
the answer while leaving every ordinary query mean untouched.  `hidden_shift_witness`
exhibits one in exact rationals.  So a group with no calibration query has `Γ = 0`,
and the finite-game number is not the threshold rate.

This file replaces the toy by the law of the stated model.

## THE MODEL

Task: report `{i : θ_i > τ}`.  Observation `Y_i = θ_i + b_{g(i)} + noise`, variance
`v_i`; a control query on group `g` observes `b_g` with variance `ν_g` at price `κ_g`.
Everything (`θ`, `b`) is free.  For a boundary alternative at item `i` the nuisance is
the common shift `t` of the group, and profiling it out gives

    I_i(x, z) = Δ_i² / (2 (v_i/x_i + ν_g/z_g)).

With `v = ν = 1`, unit ordinary price, control price `κ`, `K` groups of `m` items and a
common gap `Δ`:

    Γ* = Δ² / (2 K (√m + √κ)²).

## WHAT IS PROVED

* `hidden_shift_witness` — four items in two groups, `θ = (1,0,0,1)` with offsets
  `(0,0)` against `λ = (1/4,-3/4,0,1)` with offsets `(3/4,0)`: **every ordinary query
  mean agrees**, yet the answer set changes from `{0,3}` to `{3}`.  Exact rationals.
* `profiled_information` — the two-quadratic profiling: the infimum over the nuisance
  is `Δ²/(2(1/a+1/b))`, and it is ATTAINED at `t = aΔ/(a+b)`.  This is the lemma that
  must come from the query means, not be posited.
* `group_cost_lower` — **a group that must deliver information `h` costs at least
  `h(√m+√κ)²`**, by Cauchy-Schwarz; no optimiser, no bisection.
* `group_cost_attained` — the allocation `x = h(√m+√κ)/√m`, `z = h(√m+√κ)/√κ` meets
  both the information requirement and the cost with equality.
* `calibration_rate_upper` — every design with unit budget has
  `V ≤ Δ²/(2K(√m+√κ)²)`.
* `calibration_rate_attained` — and the symmetric design achieves it, so the constant
  is exact.

## WHAT THIS DOES NOT ESTABLISH

- This is a DIFFERENT problem from the symmetric-family price threshold
  `c* = (m-1)²/(m+3)²` of `LeanMasterAnchorThresholdV1` and from the finite
  three-alternative certificate `U₀ < L₁` of `P12`.  None of the three may be
  substituted for another.
- Heterogeneous `v_i`, `ν_g`, `κ_g` and unequal gaps are not covered; the law above is
  the equal-parameter case.
- The witness shows a group WITHOUT calibration is uninformative for the threshold
  answer.  It does not by itself give the optimal price of calibration.
-/

namespace CIGAMF.P13.MasterCalibrationLaw

open Finset

/-! ## The witness: shifting a group and paying it back with the offset. -/

/-- Group of each item: items 0,1 in group 0; items 2,3 in group 1. -/
def grp : Fin 4 → Fin 2 := ![0, 0, 1, 1]

def theta0 : Fin 4 → ℚ := ![1, 0, 0, 1]

def off0 : Fin 2 → ℚ := ![0, 0]

def lam : Fin 4 → ℚ := ![1/4, -3/4, 0, 1]

def off1 : Fin 2 → ℚ := ![3/4, 0]

/-- **Every ordinary query mean agrees, but the answer changes.**  A group with no
calibration query therefore cannot separate these two worlds: `Γ = 0` there. -/
theorem hidden_shift_means :
    ∀ i : Fin 4, theta0 i + off0 (grp i) = lam i + off1 (grp i) := by
  intro i
  fin_cases i <;> norm_num [theta0, off0, lam, off1, grp]

theorem hidden_shift_answers_differ :
    (Finset.univ.filter (fun i : Fin 4 => (1:ℚ)/2 < theta0 i))
      ≠ (Finset.univ.filter (fun i : Fin 4 => (1:ℚ)/2 < lam i)) := by
  intro hEq
  have h0 : (0 : Fin 4) ∈ Finset.univ.filter (fun i : Fin 4 => (1:ℚ)/2 < theta0 i) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    norm_num [theta0]
  rw [hEq] at h0
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h0
  norm_num [lam] at h0

theorem hidden_shift_witness :
    (∀ i : Fin 4, theta0 i + off0 (grp i) = lam i + off1 (grp i))
    ∧ (Finset.univ.filter (fun i : Fin 4 => (1:ℚ)/2 < theta0 i))
        ≠ (Finset.univ.filter (fun i : Fin 4 => (1:ℚ)/2 < lam i)) :=
  ⟨hidden_shift_means, hidden_shift_answers_differ⟩

/-- Item 3 is above threshold in both worlds; item 0 only in the first. -/
theorem hidden_shift_answers :
    ((1:ℚ)/2 < theta0 0 ∧ ¬((1:ℚ)/2 < lam 0)) ∧ ((1:ℚ)/2 < theta0 3 ∧ (1:ℚ)/2 < lam 3) := by
  have e1 : theta0 0 = 1 := rfl
  have e2 : lam 0 = 1/4 := rfl
  have e3 : theta0 3 = 1 := rfl
  have e4 : lam 3 = 1 := rfl
  rw [e1, e2, e3, e4]
  norm_num

/-! ## Profiling the nuisance out of the energy. -/

/-- **The profiled information.**  `a = x/v` is the ordinary precision, `b = z/ν` the
control precision, `t` the common group shift.  The infimum over `t` is
`Δ²/(2(1/a+1/b))` and it is attained. -/
theorem profiled_information (a b D : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∀ t : ℝ, a * b * D ^ 2 / (2 * (a + b)) ≤ a * (D - t) ^ 2 / 2 + b * t ^ 2 / 2)
    ∧ a * (D - a * D / (a + b)) ^ 2 / 2 + b * (a * D / (a + b)) ^ 2 / 2
        = a * b * D ^ 2 / (2 * (a + b)) := by
  have hab : 0 < a + b := by linarith
  constructor
  · intro t
    rw [div_le_iff₀ (by linarith : (0:ℝ) < 2 * (a + b))]
    nlinarith [sq_nonneg ((a + b) * t - a * D), ha.le, hb.le, hab]
  · field_simp
    try ring

/-- The profiled information in the `1/a + 1/b` form the model states. -/
theorem profiled_information_form (a b D : ℝ) (ha : 0 < a) (hb : 0 < b) :
    D ^ 2 / (2 * (1 / a + 1 / b)) = a * b * D ^ 2 / (2 * (a + b)) := by
  have hab : 0 < a + b := by linarith
  field_simp
  try ring

/-! ## The cost of one group. -/

/-- **A group that must deliver profiled information `h` costs at least `h(√m+√κ)²`.**
`sm² = m`, `sk² = κ`.  Pure Cauchy-Schwarz: no optimiser is consulted. -/
theorem group_cost_lower (h x z sm sk : ℝ) (hsm : 0 < sm) (hsk : 0 < sk)
    (hh : 0 < h) (hx : 0 < x) (hz : 0 < z) (hinfo : h * (x + z) ≤ x * z) :
    h * (sm + sk) ^ 2 ≤ sm ^ 2 * x + sk ^ 2 * z := by
  have hxz : 0 < x + z := by linarith
  have hcs : (sm + sk) ^ 2 * (x * z) ≤ (sm ^ 2 * x + sk ^ 2 * z) * (x + z) := by
    nlinarith [sq_nonneg (sm * x - sk * z)]
  have hstep : h * (sm + sk) ^ 2 * (x + z) ≤ (sm ^ 2 * x + sk ^ 2 * z) * (x + z) := by
    have h1 : h * (sm + sk) ^ 2 * (x + z) ≤ (sm + sk) ^ 2 * (x * z) := by
      nlinarith [sq_nonneg (sm + sk), hinfo]
    linarith [h1, hcs]
  exact le_of_mul_le_mul_right (by linarith [hstep]) hxz

/-- …and the split `z/x = √(m/κ)` attains it, with the information requirement tight. -/
theorem group_cost_attained (h sm sk : ℝ) (hsm : 0 < sm) (hsk : 0 < sk) (hh : 0 < h) :
    (sm ^ 2 * (h * (sm + sk) / sm) + sk ^ 2 * (h * (sm + sk) / sk) = h * (sm + sk) ^ 2)
    ∧ h * ((h * (sm + sk) / sm) + (h * (sm + sk) / sk))
        = (h * (sm + sk) / sm) * (h * (sm + sk) / sk) := by
  constructor
  · field_simp; try ring
  · field_simp; try ring

/-! ## The `K`-group law. -/

variable {K : ℕ}

/-- **Upper bound: every unit-budget design is capped at `Δ²/(2K(√m+√κ)²)`.** -/
theorem calibration_rate_upper (sm sk D V : ℝ) (x z : Fin K → ℝ)
    (hsm : 0 < sm) (hsk : 0 < sk) (hD : 0 < D) (hV : 0 < V) (hK : 0 < K)
    (hx : ∀ g, 0 < x g) (hz : ∀ g, 0 < z g)
    (hbudget : ∑ g, (sm ^ 2 * x g + sk ^ 2 * z g) ≤ 1)
    (hinfo : ∀ g, 2 * V / D ^ 2 * (x g + z g) ≤ x g * z g) :
    V ≤ D ^ 2 / (2 * (K : ℝ) * (sm + sk) ^ 2) := by
  set h : ℝ := 2 * V / D ^ 2 with hhdef
  have hD2 : (0:ℝ) < D ^ 2 := by positivity
  have hhpos : 0 < h := by rw [hhdef]; positivity
  have hterm : ∀ g : Fin K, h * (sm + sk) ^ 2 ≤ sm ^ 2 * x g + sk ^ 2 * z g := fun g =>
    group_cost_lower h (x g) (z g) sm sk hsm hsk hhpos (hx g) (hz g) (hinfo g)
  have hsum : (K : ℝ) * (h * (sm + sk) ^ 2) ≤ ∑ g, (sm ^ 2 * x g + sk ^ 2 * z g) := by
    have := Finset.sum_le_sum (fun g (_ : g ∈ (univ : Finset (Fin K))) => hterm g)
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using this
  have hKpos : (0:ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hsq : (0:ℝ) < (sm + sk) ^ 2 := by positivity
  have hcap : (K : ℝ) * (h * (sm + sk) ^ 2) ≤ 1 := le_trans hsum hbudget
  rw [hhdef] at hcap
  have hmul : ((K : ℝ) * (2 * V / D ^ 2 * (sm + sk) ^ 2)) * D ^ 2 ≤ 1 * D ^ 2 :=
    mul_le_mul_of_nonneg_right hcap hD2.le
  have hsimp : ((K : ℝ) * (2 * V / D ^ 2 * (sm + sk) ^ 2)) * D ^ 2
      = 2 * V * ((K : ℝ) * (sm + sk) ^ 2) := by
    field_simp
    try ring
  rw [hsimp, one_mul] at hmul
  rw [le_div_iff₀ (by positivity)]
  have hgoal : V * (2 * (K : ℝ) * (sm + sk) ^ 2) = 2 * V * ((K : ℝ) * (sm + sk) ^ 2) := by
    ring
  rw [hgoal]
  exact hmul

/-- **The symmetric design attains it**, so the constant `1/(2K(√m+√κ)²)` is exact. -/
theorem calibration_rate_attained (sm sk D : ℝ) (hsm : 0 < sm) (hsk : 0 < sk)
    (hD : 0 < D) (hK : 0 < K) :
    let h : ℝ := 1 / ((K : ℝ) * (sm + sk) ^ 2)
    let xg : ℝ := h * (sm + sk) / sm
    let zg : ℝ := h * (sm + sk) / sk
    (∑ _g : Fin K, (sm ^ 2 * xg + sk ^ 2 * zg) = 1)
      ∧ h * (xg + zg) = xg * zg
      ∧ D ^ 2 / (2 * (1 / xg + 1 / zg)) = D ^ 2 / (2 * (K : ℝ) * (sm + sk) ^ 2) := by
  intro h xg zg
  have hKpos : (0:ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hsq : (0:ℝ) < (sm + sk) ^ 2 := by positivity
  have hhpos : 0 < h := by simp only [h]; positivity
  have hxp : 0 < xg := by simp only [xg]; positivity
  have hzp : 0 < zg := by simp only [zg]; positivity
  refine ⟨?_, ?_, ?_⟩
  · have hone : sm ^ 2 * xg + sk ^ 2 * zg = h * (sm + sk) ^ 2 := by
      simp only [xg, zg]
      field_simp
      try ring
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hone]
    simp only [h]
    field_simp
  · simp only [xg, zg]
    field_simp
    try ring
  · have hinv : 1 / xg + 1 / zg = 1 / h := by
      simp only [xg, zg, h]
      field_simp
      try ring
    rw [hinv]
    simp only [h]
    field_simp
    try ring

#print axioms hidden_shift_means
#print axioms hidden_shift_answers_differ
#print axioms hidden_shift_witness
#print axioms hidden_shift_answers
#print axioms profiled_information
#print axioms profiled_information_form
#print axioms group_cost_lower
#print axioms group_cost_attained
#print axioms calibration_rate_upper
#print axioms calibration_rate_attained

end CIGAMF.P13.MasterCalibrationLaw
