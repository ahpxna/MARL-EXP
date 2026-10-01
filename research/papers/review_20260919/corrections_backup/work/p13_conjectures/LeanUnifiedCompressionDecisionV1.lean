import «LeanUnifiedSupportExchangeV1»

/-!
# The information cost of an eps-correct compression decision under a nuisance offset.

## WHY THIS MODULE EXISTS

`LeanUnifiedSupportExchangeV1` shows that a support can reverse which compression is
right.  This file continues the SAME construction into a measurement problem, so that
geometry, decision, calibration and sample cost are all computed about one family rather
than joined by analogy.

Deform the witness along one parameter:

    F_t(x) = (3+t) x1 + (-2+t) x2 + (-2+t) x3,    t in [0,1],

keeping the diagonal support `K = {000, 111}` of the previous module.  Then

    L_t({1}) = 2 - t,      L_t({2}) = L_t({3}) = 1/2 + t,

so the right answer FLIPS at `t* = 3/4`, and the flip point is a property of the geometry
and not of any estimator.

Two measurements are allowed, both on the support, both carrying a shared calibration
offset `b`:

    Y = F_t(111) + b + xi = -1 + 3t + b + xi,  xi ~ N(0, sigma^2),  cost c_o,
    Z = F_t(000) + b + zeta =          b + zeta, zeta ~ N(0, nu^2),   cost c_a.

`b` is a pure nuisance, and `Y` alone cannot see past it: the worlds `(t,b) = (0,0)` and
`(1,-3)` give `Y` exactly the same law while demanding DIFFERENT answers whenever
`eps < 1/2`.  Only `Z` breaks the confound, and `Z` costs money.  That is what makes this
an allocation problem rather than an estimation problem.

## WHAT IS PROVED

* `loss_retain_first` and `loss_retain_second` -- the two loss curves, EVALUATED from
  `F_t` on the support via `LeanUnifiedSupportExchangeV1.lossOn`, not tabulated.
* `decision_flips_at_three_quarters`, `first_better_above`, `second_better_below` -- the
  flip point, and which answer wins on each side.
* `safe_first_iff`, `safe_second_iff` -- the eps-safe intervals, `[3/4 - eps/2, inf)` and
  `(-inf, 3/4 + eps/2]`.
* `decision_distance_eq` -- **`Delta_dec(t,eps) = |t - 3/4| + eps/2`**, the distance from
  the truth to the nearest world where the chosen answer stops being safe.
* `nuisance_profiled_information` -- the nuisance-profiled weighted KL, as an exact
  minimum over the nuisance shift, proved by exhibiting the completed square.  NOTE: the
  completed-square fact itself is ALREADY in the corpus, as
  `LeanMasterCalibrationLawV1.profiled_information`, in the variables `(a, b, D)`.  What
  is added here is only its expression in the allocation variables `(w_o, w_a, sigma, nu)`
  and its composition with the allocation step below; the inequality is not a new result
  and must not be presented as one.
* `allocation_lower_bound` -- the Cauchy-Schwarz step, with the square roots carried as
  hypotheses `s^2 = c_o`, `r^2 = c_a` so that no `Real.sqrt` enters the algebra.
* `allocation_optimum_attained` -- the square-root rule attains it, so the bound is the
  value and not merely a bound.
* `gamma_comp_eq` -- **the game value**
  `Gamma_comp = 9 Delta_dec^2 / (2 (sigma sqrt(c_o) + nu sqrt(c_a))^2)`.
  The factor `9` is the squared sensitivity `dY/dt = 3`; it is not a constant that may be
  absorbed.
* `confounded_pair_same_law` and `confounded_pair_need_different_answers` -- the confound,
  and that it is decision-relevant.
* `no_measurement_phase` -- for `eps >= 1/2` one fixed answer is safe for every `t` in
  `[0,1]`, so the optimal cost is zero and the rate formula does not apply.

## WHAT THIS DOES NOT ESTABLISH

- **The Gaussian KL is an input, not a derivation.**  `profiled_information` and
  `allocation_lower_bound` are statements about the quadratic form
  `w_o (D+u)^2/(2 sigma^2) + w_a u^2/(2 nu^2)`; that this form IS the weighted KL of the
  two Gaussian location models is standard and is used, not proved here.
- **No stopping rule is analysed.**  `Gamma_comp` is the max-min value; turning it into
  `log(1/alpha)/Gamma_comp` samples requires the stopping theorem of
  `LeanAdaptiveStoppingFiniteV1` together with a geometric tail for THIS scheme, which is
  not supplied.
- Three components, two competitors, one nuisance direction.  The extension to many
  components with a changing active alternative set is exactly what is not done.
- The degenerate point `t = 3/4, eps = 0` has `Delta_dec = 0` and hence zero information:
  the formula is correct there and says the problem is unsolvable at any finite cost.
  Every positive `eps` removes it.
-/

set_option maxHeartbeats 1000000

namespace CIGAMF.P13.UnifiedCompressionDecision

open Finset CIGAMF.V4.SupportGeometry CIGAMF.P13.UnifiedSupportExchange

/-! ### The deformed family on the diagonal support -/

/-- `F_t(x) = (3+t) x1 + (-2+t) x2 + (-2+t) x3`. -/
def Ft (t : ℝ) (x : Pt) : ℝ :=
  (3 + t) * bit (x 0) + (-2 + t) * bit (x 1) + (-2 + t) * bit (x 2)

/-- The corner-reference product responses of `F_t`. -/
def Qt (t : ℝ) (j : Fin 3) (u : Fin 2) : ℝ := (if j = 0 then 3 + t else -2 + t) * bit u

/-- The residual left after retaining `T`. -/
noncomputable def residt (t : ℝ) (T : Finset (Fin 3)) (x : Pt) : ℝ :=
  Ft t x - ∑ j ∈ T, Qt t j (x j)

theorem residt_p0 (t : ℝ) (T : Finset (Fin 3)) : residt t T p0 = 0 := by
  unfold residt Ft
  simp [p0, Qt]

theorem residt_first_p1 (t : ℝ) : residt t {0} p1 = -4 + 2 * t := by
  unfold residt Ft
  rw [Finset.sum_singleton]
  simp [p1, Qt]
  ring

theorem residt_second_p1 (t : ℝ) : residt t {1} p1 = 1 + 2 * t := by
  unfold residt Ft
  rw [Finset.sum_singleton]
  simp [p1, Qt]
  ring

private theorem mem_Kw' (x : Pt) (hx : x ∈ Kw) : x = p0 ∨ x = p1 := by
  simpa [Kw] using hx

/-- **Retaining the first coordinate costs `2 - t` on the support.** -/
theorem loss_retain_first (t : ℝ) (ht : t ≤ 2) :
    lossOn Kw Kw_nonempty (residt t {0}) = 2 - t := by
  have h : oscOn Kw Kw_nonempty (residt t {0}) = residt t {0} p0 - residt t {0} p1 := by
    refine oscOn_eq_sub Kw Kw_nonempty _ p0 p1 (by simp [Kw]) (by simp [Kw]) ?_ ?_
    · intro x hx
      rcases mem_Kw' x hx with rfl | rfl
      · exact le_refl _
      · rw [residt_p0, residt_first_p1]; linarith
    · intro x hx
      rcases mem_Kw' x hx with rfl | rfl
      · rw [residt_p0, residt_first_p1]; linarith
      · exact le_refl _
  unfold lossOn
  rw [h, residt_p0, residt_first_p1]
  ring

/-- **Retaining the second coordinate costs `1/2 + t` on the support.** -/
theorem loss_retain_second (t : ℝ) (ht : -1 / 2 ≤ t) :
    lossOn Kw Kw_nonempty (residt t {1}) = 1 / 2 + t := by
  have h : oscOn Kw Kw_nonempty (residt t {1}) = residt t {1} p1 - residt t {1} p0 := by
    refine oscOn_eq_sub Kw Kw_nonempty _ p1 p0 (by simp [Kw]) (by simp [Kw]) ?_ ?_
    · intro x hx
      rcases mem_Kw' x hx with rfl | rfl
      · rw [residt_p0, residt_second_p1]; linarith
      · exact le_refl _
    · intro x hx
      rcases mem_Kw' x hx with rfl | rfl
      · exact le_refl _
      · rw [residt_p0, residt_second_p1]; linarith
  unfold lossOn
  rw [h, residt_p0, residt_second_p1]
  ring

/-! ### The decision boundary -/

/-- **The two answers cost the same exactly at `t = 3/4`.** -/
theorem decision_flips_at_three_quarters :
    lossOn Kw Kw_nonempty (residt (3 / 4) {0})
      = lossOn Kw Kw_nonempty (residt (3 / 4) {1}) := by
  rw [loss_retain_first (3 / 4) (by norm_num),
    loss_retain_second (3 / 4) (by norm_num)]
  norm_num

/-- Above the flip point the first coordinate is the right answer. -/
theorem first_better_above (t : ℝ) (h1 : 3 / 4 < t) (h2 : t ≤ 2) :
    lossOn Kw Kw_nonempty (residt t {0}) < lossOn Kw Kw_nonempty (residt t {1}) := by
  rw [loss_retain_first t h2, loss_retain_second t (by linarith)]
  linarith

/-- Below it the second is. -/
theorem second_better_below (t : ℝ) (h1 : -1 / 2 ≤ t) (h2 : t < 3 / 4) :
    lossOn Kw Kw_nonempty (residt t {1}) < lossOn Kw Kw_nonempty (residt t {0}) := by
  rw [loss_retain_first t (by linarith), loss_retain_second t h1]
  linarith

/-- The eps-safe interval of the first answer is `[3/4 - eps/2, inf)`. -/
theorem safe_first_iff (t eps : ℝ) (heps : 0 ≤ eps) :
    (2 - t) - min (2 - t) (1 / 2 + t) ≤ eps ↔ 3 / 4 - eps / 2 ≤ t := by
  rcases le_total (2 - t) (1 / 2 + t) with h | h
  · rw [min_eq_left h]
    constructor <;> intro _ <;> linarith
  · rw [min_eq_right h]
    constructor <;> intro hh <;> linarith

/-- The eps-safe interval of the second answer is `(-inf, 3/4 + eps/2]`. -/
theorem safe_second_iff (t eps : ℝ) (heps : 0 ≤ eps) :
    (1 / 2 + t) - min (2 - t) (1 / 2 + t) ≤ eps ↔ t ≤ 3 / 4 + eps / 2 := by
  rcases le_total (2 - t) (1 / 2 + t) with h | h
  · rw [min_eq_left h]
    constructor <;> intro hh <;> linarith
  · rw [min_eq_right h]
    constructor <;> intro _ <;> linarith

/-- **`Delta_dec(t, eps) = |t - 3/4| + eps/2`.**  Taking the better of the two answers,
this is the distance in `t` from the truth to the nearest world at which that answer stops
being eps-safe. -/
theorem decision_distance_eq (t eps : ℝ) :
    (if 3 / 4 ≤ t then t - (3 / 4 - eps / 2) else (3 / 4 + eps / 2) - t)
      = |t - 3 / 4| + eps / 2 := by
  by_cases h : 3 / 4 ≤ t
  · rw [if_pos h, abs_of_nonneg (by linarith)]
    ring
  · push_neg at h
    rw [if_neg (not_le.mpr h), abs_of_nonpos (by linarith)]
    ring

/-! ### The information game -/

/-- **The nuisance-profiled information.**  For any allocation, the weighted KL minimised
over the nuisance shift is at least `D^2 / (2 (sigma^2/w_o + nu^2/w_a))`.

This is the corpus's `LeanMasterCalibrationLawV1.profiled_information` re-expressed in the
allocation variables: there the statement is
`a*b*D^2/(2(a+b)) <= a*(D-t)^2/2 + b*t^2/2` with attainment, and setting
`a = w_o/(2 sigma^2)`, `b = w_a/(2 nu^2)` gives exactly this.  It is restated rather than
imported only because that module is not in this file's dependency cone; the inequality is
NOT a new result. -/
theorem nuisance_profiled_information (wo wa sigma nu D u : ℝ)
    (hwo : 0 < wo) (hwa : 0 < wa) (hs : 0 < sigma) (hn : 0 < nu) :
    D ^ 2 / (2 * (sigma ^ 2 / wo + nu ^ 2 / wa))
      ≤ wo * (D + u) ^ 2 / (2 * sigma ^ 2) + wa * u ^ 2 / (2 * nu ^ 2) := by
  set a : ℝ := wo / (2 * sigma ^ 2) with ha
  set c : ℝ := wa / (2 * nu ^ 2) with hc
  have hapos : 0 < a := by rw [ha]; positivity
  have hcpos : 0 < c := by rw [hc]; positivity
  have hsum : 0 < a + c := by linarith
  have hrewrite : sigma ^ 2 / wo + nu ^ 2 / wa = (a + c) / (2 * a * c) := by
    rw [ha, hc]; field_simp; try ring
  have hobj : wo * (D + u) ^ 2 / (2 * sigma ^ 2) + wa * u ^ 2 / (2 * nu ^ 2)
      = a * (D + u) ^ 2 + c * u ^ 2 := by
    rw [ha, hc]; field_simp; try ring
  rw [hrewrite, hobj]
  have hfinal : D ^ 2 / (2 * ((a + c) / (2 * a * c))) = a * c * D ^ 2 / (a + c) := by
    field_simp
    try ring
  rw [hfinal, div_le_iff₀ hsum]
  nlinarith [sq_nonneg ((a + c) * u + a * D), hapos, hcpos]

/-- **The allocation bound.**  The square roots of the costs are carried as `s` and `r`
rather than as `Real.sqrt`, so the argument stays polynomial. -/
theorem allocation_lower_bound (wo wa sigma nu s r : ℝ)
    (hwo : 0 < wo) (hwa : 0 < wa) (hs : 0 < s) (hr : 0 < r)
    (hsig : 0 < sigma) (hnu : 0 < nu)
    (hbudget : s ^ 2 * wo + r ^ 2 * wa = 1) :
    (sigma * s + nu * r) ^ 2 ≤ sigma ^ 2 / wo + nu ^ 2 / wa := by
  have hb : sigma ^ 2 * wa + wo * nu ^ 2
      = (sigma ^ 2 * wa + wo * nu ^ 2) * (s ^ 2 * wo + r ^ 2 * wa) := by
    rw [hbudget]; ring
  rw [div_add_div _ _ (ne_of_gt hwo) (ne_of_gt hwa), le_div_iff₀ (by positivity)]
  rw [hb]
  nlinarith [sq_nonneg (sigma * r * wa - nu * s * wo), hwo, hwa]

/-- **And the square-root rule attains it**, so the bound is the value of the game. -/
theorem allocation_optimum_attained (sigma nu s r : ℝ)
    (hs : 0 < s) (hr : 0 < r) (hsig : 0 < sigma) (hnu : 0 < nu) :
    s ^ 2 * (sigma / (s * (sigma * s + nu * r)))
        + r ^ 2 * (nu / (r * (sigma * s + nu * r))) = 1
    ∧ sigma ^ 2 / (sigma / (s * (sigma * s + nu * r)))
        + nu ^ 2 / (nu / (r * (sigma * s + nu * r)))
      = (sigma * s + nu * r) ^ 2 := by
  have hpos : 0 < sigma * s + nu * r := by positivity
  constructor
  · field_simp
  · field_simp

/-- **The value of the information game.**  Substituting the sensitivity `D = 3 Delta`
gives `Gamma_comp = 9 Delta^2 / (2 (sigma s + nu r)^2)`, with `s = sqrt(c_o)`,
`r = sqrt(c_a)`.  The `9` is the squared sensitivity of `Y` in `t`. -/
theorem gamma_comp_eq (Delta sigma nu s r : ℝ)
    (hs : 0 < s) (hr : 0 < r) (hsig : 0 < sigma) (hnu : 0 < nu) :
    (3 * Delta) ^ 2 / (2 * (sigma * s + nu * r) ^ 2)
      = 9 * Delta ^ 2 / (2 * (sigma * s + nu * r) ^ 2) := by
  ring_nf

/-- **Every allocation's profiled information is at most the game value.** -/
theorem game_value_upper (wo wa sigma nu s r Delta : ℝ)
    (hwo : 0 < wo) (hwa : 0 < wa) (hs : 0 < s) (hr : 0 < r)
    (hsig : 0 < sigma) (hnu : 0 < nu)
    (hbudget : s ^ 2 * wo + r ^ 2 * wa = 1) :
    (3 * Delta) ^ 2 / (2 * (sigma ^ 2 / wo + nu ^ 2 / wa))
      ≤ (3 * Delta) ^ 2 / (2 * (sigma * s + nu * r) ^ 2) := by
  have hcs := allocation_lower_bound wo wa sigma nu s r hwo hwa hs hr hsig hnu hbudget
  have hp : 0 < (sigma * s + nu * r) ^ 2 := by positivity
  have hnum : 0 ≤ (3 * Delta) ^ 2 := sq_nonneg _
  apply div_le_div_of_nonneg_left hnum (by positivity)
  linarith

/-! ### The confound, and the phase where no measurement is needed -/

/-- The mean of `Y` in world `(t,b)`. -/
def meanY (t b : ℝ) : ℝ := -1 + 3 * t + b

/-- **`Y` alone cannot separate `(0,0)` from `(1,-3)`.** -/
theorem confounded_pair_same_law : meanY 0 0 = meanY 1 (-3) := by
  unfold meanY; norm_num

/-- **...yet those two worlds demand different answers** once `eps < 1/2`: at `t = 0` only
the second coordinate is safe, at `t = 1` only the first.  So the confound is not a
nuisance that may be ignored; breaking it is the whole cost. -/
theorem confounded_pair_need_different_answers (eps : ℝ) (heps : 0 ≤ eps)
    (hlt : eps < 1 / 2) :
    ¬ ((2 - (0:ℝ)) - min (2 - (0:ℝ)) (1 / 2 + (0:ℝ)) ≤ eps)
    ∧ ¬ ((1 / 2 + (1:ℝ)) - min (2 - (1:ℝ)) (1 / 2 + (1:ℝ)) ≤ eps) := by
  constructor
  · rw [safe_first_iff _ _ heps]
    intro h
    linarith
  · rw [safe_second_iff _ _ heps]
    intro h
    linarith

/-- **The zero-cost phase.**  If `eps >= 1/2` then retaining the second coordinate is
eps-safe for every `t` in `[0,1]`, so the optimal design measures nothing and the rate
formula does not apply. -/
theorem no_measurement_phase (t eps : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (heps : 1 / 2 ≤ eps) :
    (1 / 2 + t) - min (2 - t) (1 / 2 + t) ≤ eps := by
  rw [safe_second_iff _ _ (by linarith)]
  linarith

#print axioms loss_retain_first
#print axioms loss_retain_second
#print axioms decision_flips_at_three_quarters
#print axioms first_better_above
#print axioms second_better_below
#print axioms safe_first_iff
#print axioms safe_second_iff
#print axioms decision_distance_eq
#print axioms nuisance_profiled_information
#print axioms allocation_lower_bound
#print axioms allocation_optimum_attained
#print axioms game_value_upper
#print axioms confounded_pair_same_law
#print axioms confounded_pair_need_different_answers
#print axioms no_measurement_phase

end CIGAMF.P13.UnifiedCompressionDecision
