import «LeanPaperCStabilityFamilyV1»
import «LeanPaperCRelaxedJoinV1»

/-!
# Paper C: the price ratio of an actual perturbation

The earlier robustness floor (`price_ratio_robust`, `ratio_lower_of_perturbation`,
`ratio_collapse_lower`) is ARITHMETIC: it takes the perturbed zero-band value and the
perturbed free value as hypotheses (`hu`, `hf`, `hV`, `hVfree`).  Nothing instantiated those
hypotheses at an actual perturbed program, and the fixed-`D` envelope they came from uses a
different regret from the paper's physical one.  This module states the floor for the
physical program itself.

For an arbitrary weight vector `g'` and band `η`, `trueValue g' η` is the optimum over every
permutation law with per-item bands, with the per-budget baseline recomputed for `g'` and the
normaliser `‖g'‖₁` (`LeanPaperCStabilityEndgameV1`).  At `η = m` the band is vacuous, so
`trueValue g' m` is the unconstrained optimum of `g'`.  With `ε = ‖g_m - g'‖₁`:

* `physical_price_ratio`: for odd `m`, every admissible `d`, a positive perturbed free value
  and `3ε/d ≤ V_m(0)`,
  `trueValue g' 0 / trueValue g' m ≥ (V_m(0) - 3ε/d) / (V_free + 3ε/d)`.
  The two values come from `family_value_robust` at `η = 0` and `η = m`, the anchors from
  `odd_value_zero` and `odd_breakpoint`.
* `physical_price_linear`: at `ε ≤ 1/(2m)` the physical price ratio is at least `(m-1)/4`.
  No hypothesis about `g'` remains: the positivity of the perturbed free value, the choice
  `d = m+3` and the numerator's sign are all derived.

What this does NOT say: where the price collapses.  A lower bound on the ratio cannot locate a
collapse; only a perturbation proved to destroy the price could, and none is proved.
-/

namespace CIGAMF.P13.PaperCRatioJoin

open Finset
open CIGAMF.P13.PaperCFamily CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCFrontier
open CIGAMF.P13.PaperCStabilityEndgame CIGAMF.P13.PaperCEndgame CIGAMF.P13.PaperCEndpointLaw
open CIGAMF.P13.PaperCStabilityFamily CIGAMF.P13.PaperCRelaxedJoin

/-! ## The two anchors, in closed form -/

theorem odd_zero_value (m : ℕ) (hm : 3 ≤ m) (hmo : m % 2 = 1) :
    value m (by omega) 0 = ((m : ℝ) + 3) / ((m : ℝ) * ((m : ℝ) + 4)) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = 2 * s + 3 := ⟨(m - 3) / 2, by omega⟩
  rw [odd_value_zero s]
  rfl

theorem odd_free_value (m : ℕ) (hm : 3 ≤ m) (hmo : m % 2 = 1) (η : ℝ) (hη : 1 ≤ η) :
    value m (by omega) η = freeValue m :=
  (odd_breakpoint m hm hmo η (by linarith)).mpr hη

/-! ## Mass bookkeeping -/

theorem normMass_gFamily (m : ℕ) (hm : 3 ≤ m) : normMass (gFamily m) = (m : ℝ) + 4 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  have h := sum_fn_gFamily n (by omega) (fun w => |w|)
  beta_reduce at h
  unfold normMass
  rw [h]
  have hc : (((n + 1) / 2 : ℕ) : ℝ) + ((n - (n + 1) / 2 : ℕ) : ℝ) = (n : ℝ) := by
    rw [← Nat.cast_add, show (n + 1) / 2 + (n - (n + 1) / 2) = n from by omega]
  rw [show |(-3 : ℝ)| = 3 by norm_num, show |(3 : ℝ)| = 3 by norm_num,
    show |(-1 : ℝ)| = 1 by norm_num, abs_one]
  push_cast
  linarith

theorem normMass_ge {m : ℕ} (g g' : Fin m → ℝ) : normMass g - l1 g g' ≤ normMass g' := by
  unfold normMass l1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i _
  linarith [abs_sub_abs_le_abs_sub (g i) (g' i)]

theorem l1_nonneg {m : ℕ} (g g' : Fin m → ℝ) : 0 ≤ l1 g g' := by
  unfold l1
  exact Finset.sum_nonneg (fun i _ => abs_nonneg _)

/-! ## The ratio, for the physical program -/

/-- **The price ratio of an actual perturbation**, from the physical envelope at the two
anchors. -/
theorem physical_price_ratio (m : ℕ) (hm : 3 ≤ m) (hmo : m % 2 = 1) (g' : Fin m → ℝ)
    (d : ℝ) (hd : 0 < d) (hdg : d ≤ (m : ℝ) + 4) (hg' : d ≤ normMass g')
    (hpos : 0 < trueValue g' (m : ℝ) (interiorK m) (interiorK_nonempty m (by omega)))
    (hsmall : 3 * l1 (gFamily m) g' / d ≤ ((m : ℝ) + 3) / ((m : ℝ) * ((m : ℝ) + 4))) :
    (((m : ℝ) + 3) / ((m : ℝ) * ((m : ℝ) + 4)) - 3 * l1 (gFamily m) g' / d)
        / (freeValue m + 3 * l1 (gFamily m) g' / d)
      ≤ trueValue g' 0 (interiorK m) (interiorK_nonempty m (by omega))
        / trueValue g' (m : ℝ) (interiorK m) (interiorK_nonempty m (by omega)) := by
  have h0 := family_value_robust m hm g' 0 le_rfl d hd hdg hg'
  have hM := family_value_robust m hm g' (m : ℝ) (by positivity) d hd hdg hg'
  rw [odd_zero_value m hm hmo] at h0
  rw [odd_free_value m hm hmo (m : ℝ) (by exact_mod_cast (show 1 ≤ m by omega))] at hM
  have hlo := (abs_le.mp h0).1
  have hup := (abs_le.mp hM).2
  have hnum : 0 ≤ ((m : ℝ) + 3) / ((m : ℝ) * ((m : ℝ) + 4)) - 3 * l1 (gFamily m) g' / d := by
    linarith
  calc _ ≤ (((m : ℝ) + 3) / ((m : ℝ) * ((m : ℝ) + 4)) - 3 * l1 (gFamily m) g' / d)
          / trueValue g' (m : ℝ) (interiorK m) (interiorK_nonempty m (by omega)) :=
        div_le_div_of_nonneg_left hnum hpos (by linarith)
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hpos.le

/-- The arithmetic step of the linear corollary, on bare reals. -/
theorem ratio_arith (mR V0 F E tv0 tvM : ℝ) (hm : 3 ≤ mR)
    (hkey : 0 ≤ 4 * V0 - (mR - 1) * F - (mR + 3) * E) (hFE : E < F)
    (hlo : V0 - E ≤ tv0) (hup : tvM ≤ F + E) (hlow : F - E ≤ tvM) :
    (mR - 1) / 4 ≤ tv0 / tvM := by
  have htvM : 0 < tvM := by linarith
  rw [div_le_div_iff₀ (by norm_num) htvM]
  nlinarith [mul_le_mul_of_nonneg_left hup (by linarith : (0 : ℝ) ≤ mR - 1)]

/-- **A perturbation of size `O(1/m)` keeps a linear price.**  For odd `m ≥ 3` and every
`g'` with `‖g_m - g'‖₁ ≤ 1/(2m)`, the physical price ratio is at least `(m-1)/4`. -/
theorem physical_price_linear (m : ℕ) (hm : 3 ≤ m) (hmo : m % 2 = 1) (g' : Fin m → ℝ)
    (hε : l1 (gFamily m) g' ≤ 1 / (2 * (m : ℝ))) :
    ((m : ℝ) - 1) / 4
      ≤ trueValue g' 0 (interiorK m) (interiorK_nonempty m (by omega))
        / trueValue g' (m : ℝ) (interiorK m) (interiorK_nonempty m (by omega)) := by
  have hmR : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hε0 := l1_nonneg (gFamily m) g'
  have hε1 : l1 (gFamily m) g' ≤ 1 := by
    refine le_trans hε ?_
    rw [div_le_one (by positivity)]
    linarith
  have hd : (0 : ℝ) < (m : ℝ) + 3 := by linarith
  have hdg : (m : ℝ) + 3 ≤ (m : ℝ) + 4 := by linarith
  have hg' : (m : ℝ) + 3 ≤ normMass g' := by
    have := normMass_ge (gFamily m) g'
    rw [normMass_gFamily m hm] at this
    linarith
  have h0 := family_value_robust m hm g' 0 le_rfl ((m : ℝ) + 3) hd hdg hg'
  have hM := family_value_robust m hm g' (m : ℝ) (by positivity) ((m : ℝ) + 3) hd hdg hg'
  rw [odd_zero_value m hm hmo] at h0
  rw [odd_free_value m hm hmo (m : ℝ) (by exact_mod_cast (show 1 ≤ m by omega))] at hM
  have hEm : ((m : ℝ) + 3) * (3 * l1 (gFamily m) g' / ((m : ℝ) + 3))
      = 3 * l1 (gFamily m) g' := by
    field_simp
  have hkey0 : 4 * (((m : ℝ) + 3) / ((m : ℝ) * ((m : ℝ) + 4))) - ((m : ℝ) - 1) * freeValue m
      = (2 * (m : ℝ) + 12) / ((m : ℝ) * ((m : ℝ) + 4)) := by
    unfold freeValue denom
    have h1 : (m : ℝ) - 1 ≠ 0 := by linarith
    have h2 : (m : ℝ) ≠ 0 := by linarith
    have h3 : (m : ℝ) + 4 ≠ 0 := by linarith
    field_simp
    ring
  have h3e1 : 3 * l1 (gFamily m) g' ≤ 3 / (2 * (m : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hε (by norm_num : (0 : ℝ) ≤ 3)
    calc _ ≤ 3 * (1 / (2 * (m : ℝ))) := this
      _ = 3 / (2 * (m : ℝ)) := by ring
  have h3e2 : 3 / (2 * (m : ℝ)) ≤ (2 * (m : ℝ) + 12) / ((m : ℝ) * ((m : ℝ) + 4)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hFE : 3 * l1 (gFamily m) g' / ((m : ℝ) + 3) < freeValue m := by
    have hE' : 3 * l1 (gFamily m) g' / ((m : ℝ) + 3) ≤ 3 / (2 * (m : ℝ)) / ((m : ℝ) + 3) :=
      div_le_div_of_nonneg_right h3e1 hd.le
    have : 3 / (2 * (m : ℝ)) / ((m : ℝ) + 3) < freeValue m := by
      unfold freeValue denom
      rw [div_div, div_lt_div_iff₀ (by positivity) (by nlinarith)]
      nlinarith
    linarith
  exact ratio_arith (m : ℝ) (((m : ℝ) + 3) / ((m : ℝ) * ((m : ℝ) + 4))) (freeValue m)
    (3 * l1 (gFamily m) g' / ((m : ℝ) + 3)) _ _ hmR (by nlinarith) hFE
    (by linarith [(abs_le.mp h0).1]) (by linarith [(abs_le.mp hM).2])
    (by linarith [(abs_le.mp hM).1])

/-- **The hypothesis is satisfiable**: the unperturbed family meets it, so
`physical_price_linear` is not vacuous. -/
theorem physical_price_linear_self (m : ℕ) (hm : 3 ≤ m) (hmo : m % 2 = 1) :
    ((m : ℝ) - 1) / 4
      ≤ trueValue (gFamily m) 0 (interiorK m) (interiorK_nonempty m (by omega))
        / trueValue (gFamily m) (m : ℝ) (interiorK m) (interiorK_nonempty m (by omega)) :=
  physical_price_linear m hm hmo (gFamily m) (by
    have h0 : l1 (gFamily m) (gFamily m) = 0 := by simp [l1]
    rw [h0]
    have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    positivity)

end CIGAMF.P13.PaperCRatioJoin

#print axioms CIGAMF.P13.PaperCRatioJoin.physical_price_ratio
#print axioms CIGAMF.P13.PaperCRatioJoin.physical_price_linear
#print axioms CIGAMF.P13.PaperCRatioJoin.normMass_gFamily
#print axioms CIGAMF.P13.PaperCRatioJoin.physical_price_linear_self
