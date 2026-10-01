import «LeanPaperCCollapseScaleV1»

/-!
# Paper C: the collapse bound on the window `(1/(2m), 1/m)`

`physical_price_linear` bounds the price ratio of every perturbation with `‖g_m − g'‖₁ ≤ 1/(2m)`
by `(m−1)/4`, and `collapse_lower` bounds it by `1/(16 ε)` for `ε = ‖g_m − g'‖₁ ∈ [1/m, 1/6]`.
Between them, on `(1/(2m), 1/m)`, no per-perturbation lower bound was stated.  This module fills
the window from the same robust-value bound (`physical_price_ratio`).

* `window_arith`: for `x ≥ 3` and `0 ≤ e ≤ 1/x`, the ratio bound is at least `(x − 1)/8`.
* `collapse_window`: every perturbation with `‖g_m − g'‖₁ ≤ 1/m` and a positive perturbed free
  value keeps a price ratio of at least `(m − 1)/8`.
* `collapse_all`: on `0 < ε ≤ 1/6`, with a positive perturbed free value, the ratio is at least
  `min(m − 1, 1/ε)/16`, with no gap in `ε`.
* `collapse_window_satisfiable`: the unperturbed family meets the hypotheses.
-/

namespace CIGAMF.P13.PaperCCollapseWindow

open Finset
open CIGAMF.P13.PaperCRanking CIGAMF.P13.PaperCInstantiation CIGAMF.P13.PaperCFamily
open CIGAMF.P13.PaperCEndpoint CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCFrontier
open CIGAMF.P13.PaperCStabilityEndgame CIGAMF.P13.PaperCEndgame CIGAMF.P13.PaperCEndpointLaw
open CIGAMF.P13.PaperCStabilityFamily CIGAMF.P13.PaperCRelaxedJoin CIGAMF.P13.PaperCRatioJoin
open CIGAMF.P13.PaperCLawPush CIGAMF.P13.PaperCBaselineAttain CIGAMF.P13.PaperCCollapseScale

/-- **The window arithmetic.**  For `x >= 3` and `0 <= e <= 1/x`, the robust ratio bound is at
least `(x - 1)/8`. -/
theorem window_arith (x e : ℝ) (hx : 3 ≤ x) (he0 : 0 ≤ e) (he1 : e ≤ 1 / x) :
    (x - 1) / 8 ≤ ((x + 3) / (x * (x + 4)) - 3 * e / (x + 3))
      / (2 / ((x + 4) * (x - 1)) + 3 * e / (x + 3)) := by
  have hx0 : 0 < x := by linarith
  have hxe : x * e ≤ 1 := by rwa [le_div_iff₀ hx0, mul_comm] at he1
  have hy : 3 * e / (x + 3) ≤ 3 / (x * (x + 3)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hy0 : 0 ≤ 3 * e / (x + 3) := by positivity
  have hden : 0 < 2 / ((x + 4) * (x - 1)) + 3 * e / (x + 3) := by
    have : 0 < 2 / ((x + 4) * (x - 1)) := div_pos two_pos (mul_pos (by linarith) (by linarith))
    linarith
  rw [le_div_iff₀ hden]
  have hf : (x - 1) * (2 / ((x + 4) * (x - 1))) = 2 / (x + 4) := by
    have h1 : x - 1 ≠ 0 := by linarith
    have h2 : x + 4 ≠ 0 := by linarith
    field_simp
  have hkey : 2 / (8 * (x + 4)) + (x + 7) / 8 * (3 / (x * (x + 3))) ≤ (x + 3) / (x * (x + 4)) := by
    rw [show 2 / (8 * (x + 4)) + (x + 7) / 8 * (3 / (x * (x + 3)))
        = (2 * x * (x + 3) + 3 * (x + 7) * (x + 4)) / (8 * x * (x + 3) * (x + 4)) by
          field_simp]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hdiff : (x + 3) * (8 * x * (x + 3) * (x + 4))
        - (2 * x * (x + 3) + 3 * (x + 7) * (x + 4)) * (x * (x + 4))
        = x * (x + 4) * (3 * x ^ 2 + 9 * x - 12) := by ring
    have hq : 0 ≤ 3 * x ^ 2 + 9 * x - 12 := by nlinarith
    have hp : 0 ≤ x * (x + 4) * (3 * x ^ 2 + 9 * x - 12) :=
      mul_nonneg (mul_nonneg hx0.le (by linarith)) hq
    linarith
  have hmono : (x + 7) / 8 * (3 * e / (x + 3)) ≤ (x + 7) / 8 * (3 / (x * (x + 3))) :=
    mul_le_mul_of_nonneg_left hy (by linarith)
  have hexp : (x - 1) / 8 * (2 / ((x + 4) * (x - 1)) + 3 * e / (x + 3))
      = 2 / (8 * (x + 4)) + ((x - 1) / 8) * (3 * e / (x + 3)) := by
    rw [mul_add, show (x - 1) / 8 * (2 / ((x + 4) * (x - 1))) = (x - 1) * (2 / ((x + 4) * (x - 1))) / 8
      by ring, hf]
    field_simp
  rw [hexp]
  nlinarith

/-- **The window.**  Every perturbation within `1/m` of an odd family, with a positive perturbed
free value, keeps a price ratio of at least `(m - 1)/8`. -/
theorem collapse_window (s : ℕ) (g' : Fin (2 * s + 3) → ℝ)
    (hε : l1 (gFamily (2 * s + 3)) g' ≤ 1 / ((2 * s + 3 : ℕ) : ℝ))
    (hpos : 0 < trueValue g' ((2 * s + 3 : ℕ) : ℝ) (interiorK (2 * s + 3))
      (interiorK_nonempty _ (by omega))) :
    (((2 * s + 3 : ℕ) : ℝ) - 1) / 8
      ≤ trueValue g' 0 (interiorK (2 * s + 3)) (interiorK_nonempty _ (by omega))
        / trueValue g' ((2 * s + 3 : ℕ) : ℝ) (interiorK (2 * s + 3))
            (interiorK_nonempty _ (by omega)) := by
  have hm : 3 ≤ 2 * s + 3 := by omega
  have hmo : (2 * s + 3) % 2 = 1 := by omega
  set M : ℝ := ((2 * s + 3 : ℕ) : ℝ) with hMdef
  have hM3 : (3 : ℝ) ≤ M := by rw [hMdef]; push_cast; linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)]
  set ε := l1 (gFamily (2 * s + 3)) g'
  have hε0 : 0 ≤ ε := l1_nonneg _ _
  have hε1 : ε ≤ 1 := le_trans hε (by rw [div_le_one (by linarith)]; linarith)
  have hg' : M + 3 ≤ normMass g' := by
    have := normMass_ge (gFamily (2 * s + 3)) g'
    rw [CIGAMF.P13.PaperCRatioJoin.normMass_gFamily (2 * s + 3) hm] at this
    linarith
  have hsmall : 3 * ε / (M + 3) ≤ (M + 3) / (M * (M + 4)) := by
    have hxe : M * ε ≤ 1 := by rwa [le_div_iff₀ (by linarith), mul_comm] at hε
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hr := physical_price_ratio (2 * s + 3) hm hmo g' (M + 3) (by positivity) (by linarith)
    hg' hpos hsmall
  refine le_trans ?_ hr
  have hF : freeValue (2 * s + 3) = 2 / ((M + 4) * (M - 1)) := by
    unfold freeValue denom; rw [hMdef]
  rw [hF]
  exact window_arith M ε hM3 hε0 hε

/-- **No gap in `ε`.**  On `0 < ε <= 1/6`, with a positive perturbed free value, the price ratio
is at least `min(m - 1, 1/ε)/16`. -/
theorem collapse_all (s : ℕ) (g' : Fin (2 * s + 3) → ℝ)
    (hε0 : 0 < l1 (gFamily (2 * s + 3)) g') (hε2 : l1 (gFamily (2 * s + 3)) g' ≤ 1 / 6)
    (hpos : 0 < trueValue g' ((2 * s + 3 : ℕ) : ℝ) (interiorK (2 * s + 3))
      (interiorK_nonempty _ (by omega))) :
    min ((((2 * s + 3 : ℕ) : ℝ) - 1)) (1 / l1 (gFamily (2 * s + 3)) g') / 16
      ≤ trueValue g' 0 (interiorK (2 * s + 3)) (interiorK_nonempty _ (by omega))
        / trueValue g' ((2 * s + 3 : ℕ) : ℝ) (interiorK (2 * s + 3))
            (interiorK_nonempty _ (by omega)) := by
  by_cases h : l1 (gFamily (2 * s + 3)) g' ≤ 1 / ((2 * s + 3 : ℕ) : ℝ)
  · refine le_trans ?_ (collapse_window s g' h hpos)
    have hm1 : (0 : ℝ) ≤ ((2 * s + 3 : ℕ) : ℝ) - 1 := by push_cast; linarith
    have := min_le_left ((((2 * s + 3 : ℕ) : ℝ) - 1)) (1 / l1 (gFamily (2 * s + 3)) g')
    linarith
  · have h' : 1 / ((2 * s + 3 : ℕ) : ℝ) ≤ l1 (gFamily (2 * s + 3)) g' := (not_le.mp h).le
    refine le_trans ?_ (collapse_lower s g' h' hε2 hpos)
    have := min_le_right ((((2 * s + 3 : ℕ) : ℝ) - 1)) (1 / l1 (gFamily (2 * s + 3)) g')
    rw [show 1 / (16 * l1 (gFamily (2 * s + 3)) g') = 1 / l1 (gFamily (2 * s + 3)) g' / 16 by
      field_simp]
    linarith

/-- **The hypotheses are satisfiable**: the unperturbed family has distance `0 <= 1/m` and a
positive free value. -/
theorem collapse_window_satisfiable (s : ℕ) :
    l1 (gFamily (2 * s + 3)) (gFamily (2 * s + 3)) ≤ 1 / ((2 * s + 3 : ℕ) : ℝ)
      ∧ 0 < trueValue (gFamily (2 * s + 3)) ((2 * s + 3 : ℕ) : ℝ) (interiorK (2 * s + 3))
          (interiorK_nonempty _ (by omega)) := by
  have hm : 3 ≤ 2 * s + 3 := by omega
  have hmo : (2 * s + 3) % 2 = 1 := by omega
  refine ⟨?_, ?_⟩
  · have h0 : l1 (gFamily (2 * s + 3)) (gFamily (2 * s + 3)) = 0 := by simp [l1]
    rw [h0]; positivity
  · have hM3 : (3 : ℝ) ≤ ((2 * s + 3 : ℕ) : ℝ) := by
      push_cast; linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)]
    rw [trueValue_family (2 * s + 3) hm,
      odd_free_value (2 * s + 3) hm hmo _ (by linarith)]
    unfold freeValue denom
    have : (0 : ℝ) < ((2 * s + 3 : ℕ) : ℝ) - 1 := by linarith
    positivity

#print axioms window_arith
#print axioms collapse_window
#print axioms collapse_all
#print axioms collapse_window_satisfiable

end CIGAMF.P13.PaperCCollapseWindow
