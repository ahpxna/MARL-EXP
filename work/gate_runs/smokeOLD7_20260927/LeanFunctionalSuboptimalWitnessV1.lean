import «LeanFunctionalHeterogeneousLowerV1»

/-! # Functional: an EXACT eight-cell witness that `w*` is not a maximiser.

`P23` found designs beating `w*` with Nelder-Mead.  A search certifies nothing.  To
disprove optimality one only needs ONE feasible design with a strictly larger value,
and that is a finite rational computation.  This file is that computation, with the
configuration and the witness taken from the closure guide of 2026-09-15.

## THE CONFIGURATION

Incumbent cells at `∓1/2`, six outsider cells at

    mean = (1/4, -1/4, -1/10, -1/30, 1/30, 1/10),

all variances `1`.  This is the `n = 4, c = 1` instance: `d = 1/2`, the middle gaps are
`g = (2/5, 7/15, 7/15, 2/5)`, all `≥ d/2`, so the configuration is inside the domain
where the `w*` formula is valid.

## THE TWO DESIGNS

    w*  = (1568/8397, 1568/8397, 1568/8397, 1568/8397,
           1225/16794, 450/8397, 450/8397, 1225/16794)     -- sums to 1 exactly
    w~  = (1/5, 1/5, 1/5, 1/5, 3/50, 1/25, 1/25, 3/50)     -- sums to 1 exactly

At `w*` the ENDPOINT pair alone already gives `49/8397`, so `J(w*) ≤ 49/8397`.  At `w~`
EVERY one of the thirty ordered outsider pairs is at least `1/160`, so by
`energyU_ge_pairV` every flipping alternative costs at least `1/160`; and the explicit
alternative that moves the four endpoints to `(∓3/8, ±3/8)` flips (both ranges become
`3/4`) and costs exactly `1/160`.  Since

    49/8397 < 1/160,      1/160 - 49/8397 = 557/1343520,

`w*` is NOT a maximiser, by an exact margin of 7.1046%.

## WHAT IS PROVED

* `budget_wstar`, `budget_wtilde` — both designs are feasible and positive.
* `wstar_endpoint_pair` — at `w*` the endpoint pair value is exactly `49/8397`, so
  `J(w*) ≤ 49/8397`.  Only an UPPER bound on `J(w*)` is needed and only that is claimed.
* `wtilde_pair_ge` — at `w~` all thirty ordered pairs are at least `1/160`.
* `wtilde_witness_flips`, `wtilde_witness_energy` — the flipping alternative and its
  exact cost `1/160`.
* `gap_exact` — `49/8397 < 1/160` and the difference is `557/1343520`.
* `wstar_not_optimal` — the conclusion.

## WHAT THIS DOES NOT ESTABLISH

- `w~` is NOT claimed optimal; it is only a witness that `w*` is not.
- `sup_w J(w)` is not computed and is not claimed.
- The alternative set here is the CLOSED (tie) one, matching `FlipsU`'s `≤`.  For
  strict rank inversion the same witness is approached by perturbing the outsider
  endpoints outwards, which is a limit, not an attained minimum.
-/

namespace CIGAMF.P13.FunctionalSuboptimalWitness

open Finset

/-- The pinch value in the form the pair reduction gives with unit variances:
`(1-D)^2 / (2(1/wI0 + 1/wI1 + 1/wa + 1/wb))`. -/
noncomputable def pinch (wI0 wI1 wa wb D : ℝ) : ℝ :=
  (1 - D) ^ 2 / (2 * (1 / wI0 + 1 / wI1 + 1 / wa + 1 / wb))

/-- The six outsider means. -/
noncomputable def omean : Fin 6 → ℝ := ![1/4, -1/4, -1/10, -1/30, 1/30, 1/10]

/-- The witness design's outsider weights (its incumbent weights are both `1/5`). -/
noncomputable def wt : Fin 6 → ℝ := ![1/5, 1/5, 3/50, 1/25, 1/25, 3/50]

/-- `w*`'s outsider weights (its incumbent weights are both `1568/8397`). -/
noncomputable def ws : Fin 6 → ℝ := ![1568/8397, 1568/8397, 1225/16794, 450/8397, 450/8397, 1225/16794]

theorem budget_wtilde :
    (1/5 : ℝ) + 1/5 + (1/5 + 1/5 + 3/50 + 1/25 + 1/25 + 3/50) = 1 := by norm_num

theorem budget_wstar :
    (1568/8397 : ℝ) + 1568/8397
      + (1568/8397 + 1568/8397 + 1225/16794 + 450/8397 + 450/8397 + 1225/16794) = 1 := by
  norm_num

theorem wtilde_pos : ∀ i : Fin 6, 0 < wt i := by
  intro i; fin_cases i <;> norm_num [wt]

theorem wstar_pos : ∀ i : Fin 6, 0 < ws i := by
  intro i; fin_cases i <;> norm_num [ws]

theorem mean_diff_lt_one : ∀ a b : Fin 6, omean a - omean b < 1 := by
  intro a b; fin_cases a <;> fin_cases b <;> norm_num [omean]

/-- **At `w*` the endpoint pair alone gives `49/8397`**, so `J(w*) ≤ 49/8397`.
Only an upper bound on `J(w*)` is needed here. -/
theorem wstar_endpoint_pair :
    pinch (1568/8397) (1568/8397) (ws 0) (ws 1) (omean 0 - omean 1) = 49/8397 := by
  norm_num [pinch, ws, omean]

/-- **At `w~` every one of the thirty ordered outsider pairs is at least `1/160`.** -/
theorem wtilde_pair_ge : ∀ a b : Fin 6, a ≠ b →
    (1:ℝ)/160 ≤ pinch (1/5) (1/5) (wt a) (wt b) (omean a - omean b) := by
  intro a b _
  fin_cases a <;> fin_cases b <;> norm_num [pinch, wt, omean]

/-- The flipping alternative: the four endpoints move to `∓3/8, ±3/8`.  Both ranges
become `3/4`, so the decision ties. -/
theorem wtilde_witness_flips :
    |(3:ℝ)/8 - (-(3/8))| ≤ (3/8 : ℝ) - (-(3/8)) := by norm_num

/-- …and it costs exactly `1/160`: four cells move by `1/8` at weight `1/5`, the
middle cells do not move. -/
theorem wtilde_witness_energy :
    ((1/5 : ℝ) * (-(3/8) + 1/2) ^ 2 + (1/5) * (3/8 - 1/2) ^ 2) / 2
      + ((1/5 : ℝ) * (3/8 - 1/4) ^ 2 + (1/5) * (-(3/8) - (-(1/4))) ^ 2) / 2
      = 1/160 := by norm_num

theorem gap_exact : (49:ℝ)/8397 < 1/160 ∧ (1:ℝ)/160 - 49/8397 = 557/1343520 := by
  constructor <;> norm_num

/-- **The conclusion.**  `J(w*) ≤ 49/8397 < 1/160 ≤ J(w~)`, so `w*` is not a maximiser.
No optimiser is trusted and no supremum is computed. -/
theorem wstar_not_optimal (J : (Fin 6 → ℝ) → ℝ)
    (hstar : J ws ≤ 49/8397) (htilde : (1:ℝ)/160 ≤ J wt) : J ws < J wt := by
  have h := gap_exact.1
  linarith

#print axioms budget_wtilde
#print axioms budget_wstar
#print axioms wtilde_pos
#print axioms wstar_pos
#print axioms mean_diff_lt_one
#print axioms wstar_endpoint_pair
#print axioms wtilde_pair_ge
#print axioms wtilde_witness_flips
#print axioms wtilde_witness_energy
#print axioms gap_exact
#print axioms wstar_not_optimal

end CIGAMF.P13.FunctionalSuboptimalWitness
