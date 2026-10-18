import Mathlib

/-!
# Same-day two-share designs: day effects, window effects and the unpaired amplification (city track, W22-F, 18/10/2026)

Companion of PROTOCOL_CITY_WAVE22_20261017 Amendment W22-F (F1) and ledger C-262; extends `LeanCityOwnerTestV2` (same extrapolation).

Model: the treated / control fleet means at share `p` are affine, `T p = t0 + t1 p`, `C p = c0 + c1 p`, plus additive nuisance terms: a day
effect `δ` (common to both groups and both shares measured that day) or a window effect `θ` (first / second half of the day, possibly
different for the two groups: `θ1, θ2` treated, `φ1, φ2` control).  `ts` is the two-share extrapolation from shares `p1 < p2`.

## WHAT IS PROVED
* `unpaired_error` — shares measured on two different days with day effects `δA` (share p1) and `δB` (share p2): the extrapolation's error is
  exactly `(δB - δA) / (p2 - p1)`; at (0.3, 0.7) the factor is 2.5 (`unpaired_factor_37`), matching C-262's measured amplification.
* `same_day_cancels` — both shares on the same day (`δA = δB`): the day effect cancels exactly.
* `alternating_pair_exact` — both shares on the same day, one in each half, with the order alternated on a pair of days: the mean of the two
  days' estimates equals the equal-weight mean over the two halves of the global effect, for any window effects; a single order is off
  by the window terms given exactly in `single_order_error`.
* `hyps_satisfiable` — shares (0.3, 0.7) and arbitrary effects.

## WHAT THIS DOES NOT ESTABLISH
That simulated or real days and halves act additively, or that the share's effect does not carry across the switch (the design's 900-s
burn-in is an empirical choice; F1 tests the result).
-/

namespace CIGAMF.P13.CityOwnerTestV3

/-- The two-share extrapolation from the four measured means. -/
noncomputable def ts (p1 p2 T1 C1 T2 C2 : ℝ) : ℝ :=
  (T2 + (1 - p2) * (T2 - T1) / (p2 - p1)) - (C1 - p1 * (C2 - C1) / (p2 - p1))

theorem unpaired_error (t0 t1 c0 c1 δA δB : ℝ) {p1 p2 : ℝ} (h : p1 < p2) :
    ts p1 p2 (t0 + t1 * p1 + δA) (c0 + c1 * p1 + δA) (t0 + t1 * p2 + δB) (c0 + c1 * p2 + δB)
      - ((t0 + t1 * 1) - (c0 + c1 * 0)) = (δB - δA) / (p2 - p1) := by
  have hne : p2 - p1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt h)
  unfold ts; field_simp; ring

theorem unpaired_factor_37 (δA δB : ℝ) : (δB - δA) / ((7 / 10 : ℝ) - 3 / 10) = (5 / 2) * (δB - δA) := by ring

theorem same_day_cancels (t0 t1 c0 c1 δ : ℝ) {p1 p2 : ℝ} (h : p1 < p2) :
    ts p1 p2 (t0 + t1 * p1 + δ) (c0 + c1 * p1 + δ) (t0 + t1 * p2 + δ) (c0 + c1 * p2 + δ) = (t0 + t1 * 1) - (c0 + c1 * 0) := by
  have key := unpaired_error t0 t1 c0 c1 δ δ h
  simp only [sub_self, zero_div] at key; linarith

theorem single_order_error (t0 t1 c0 c1 θ1 θ2 φ1 φ2 : ℝ) {p1 p2 : ℝ} (h : p1 < p2) :
    ts p1 p2 (t0 + t1 * p1 + θ1) (c0 + c1 * p1 + φ1) (t0 + t1 * p2 + θ2) (c0 + c1 * p2 + φ2)
      - ((t0 + t1 * 1) - (c0 + c1 * 0))
      = θ2 + (1 - p2) * (θ2 - θ1) / (p2 - p1) - φ1 + p1 * (φ2 - φ1) / (p2 - p1) := by
  have hne : p2 - p1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt h)
  unfold ts; field_simp; ring

theorem alternating_pair_exact (t0 t1 c0 c1 θ1 θ2 φ1 φ2 : ℝ) {p1 p2 : ℝ} (h : p1 < p2) :
    (ts p1 p2 (t0 + t1 * p1 + θ1) (c0 + c1 * p1 + φ1) (t0 + t1 * p2 + θ2) (c0 + c1 * p2 + φ2)
      + ts p1 p2 (t0 + t1 * p1 + θ2) (c0 + c1 * p1 + φ2) (t0 + t1 * p2 + θ1) (c0 + c1 * p2 + φ1)) / 2
      = (((t0 + t1 * 1 + θ1) - (c0 + c1 * 0 + φ1)) + ((t0 + t1 * 1 + θ2) - (c0 + c1 * 0 + φ2))) / 2 := by
  have hne : p2 - p1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt h)
  unfold ts; field_simp; ring

theorem hyps_satisfiable : (3 / 10 : ℝ) < 7 / 10 ∧
    ts (3 / 10) (7 / 10) (1 + 2 * (3 / 10) + 1) (3 + 4 * (3 / 10) + 1) (1 + 2 * (7 / 10) + 4) (3 + 4 * (7 / 10) + 4) - ((1 + 2 * 1) - (3 + 4 * 0))
      = (4 - 1) / ((7 / 10 : ℝ) - 3 / 10) := by
  refine ⟨by norm_num, unpaired_error 1 2 3 4 1 4 (by norm_num)⟩

end CIGAMF.P13.CityOwnerTestV3

#print axioms CIGAMF.P13.CityOwnerTestV3.unpaired_error
#print axioms CIGAMF.P13.CityOwnerTestV3.unpaired_factor_37
#print axioms CIGAMF.P13.CityOwnerTestV3.same_day_cancels
#print axioms CIGAMF.P13.CityOwnerTestV3.single_order_error
#print axioms CIGAMF.P13.CityOwnerTestV3.alternating_pair_exact
#print axioms CIGAMF.P13.CityOwnerTestV3.hyps_satisfiable
