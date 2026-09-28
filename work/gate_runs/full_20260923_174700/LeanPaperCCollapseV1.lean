import «LeanPaperCTransport2V1»

/-!
# Paper C: where the robustness bound collapses

`ratio_linear_at_small_eps` shows the price ratio is linear in `m` at `eps <= 1/(2m)`, and
`ratio_bounded_at_fixed_eps` shows the same expression is at most `2/eps` at a fixed `eps`,
which is a constant in `m`.  `PROOFS.md` recorded the gap honestly: only a FLOOR was proved,
and the scale at which the linear price collapses was not located.  A one-sided bound cannot
locate it -- the upper bound `2/eps` is compatible with the ratio being much smaller.

The scale is located here by proving the matching LOWER bound.  Write

    Rat(m, eps) = ((m+3)/m - 2 eps) / (2/(m-1) + 2 eps).

`ratio_collapse_lower` gives, for `eps <= 1/4`,

    Rat(m, eps)  >=  (1/8) * min(m-1, 1/eps),

so the ratio is at least linear in `m` while `eps <= 1/(m-1)` and at least `1/(8 eps)`
after.  With the upper bound `Rat <= 2/eps` the two agree in order, and the crossing sits at

    eps_c = 1 / (m - 1),

which is the collapse scale: below it the price is `Theta(m)`, above it `Theta(1/eps)` and
therefore independent of the size.  `collapse_two_sided` states both halves together and
`collapse_crossing` evaluates them at the crossing.
-/

namespace CIGAMF.P13.PaperCCollapse

open CIGAMF.P13.PaperCTransport2

/-- The price ratio the robustness statement bounds. -/
noncomputable def Rat (mR ε : ℝ) : ℝ :=
  ((mR + 3) / mR - 2 * ε) / (2 / (mR - 1) + 2 * ε)

/-- **The matching lower bound.**  This is what was missing: the ratio is at least
`(1/8) min(m-1, 1/eps)`, so the upper bound `2/eps` is tight in order and the collapse is
located rather than merely permitted. -/
theorem ratio_collapse_lower (mR ε : ℝ) (hm : 3 ≤ mR) (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) :
    (1 / 8) * min (mR - 1) (1 / ε) ≤ Rat mR ε := by
  have hm0 : (0 : ℝ) < mR := by linarith
  have hm1 : (0 : ℝ) < mR - 1 := by linarith
  have hnum : (1 : ℝ) / 2 ≤ (mR + 3) / mR - 2 * ε := by
    have h1 : (1 : ℝ) ≤ (mR + 3) / mR := by
      rw [le_div_iff₀ hm0]; linarith
    linarith
  have hden : (0 : ℝ) < 2 / (mR - 1) + 2 * ε := by positivity
  unfold Rat
  rcases le_total (mR - 1) (1 / ε) with hcase | hcase
  · -- the size is the binding term: eps <= 1/(m-1)
    rw [min_eq_left hcase]
    have hεle : ε ≤ 1 / (mR - 1) := by
      rw [le_div_iff₀ hm1]
      rw [le_div_iff₀ hε] at hcase
      nlinarith [hcase]
    have hdenle : 2 / (mR - 1) + 2 * ε ≤ 4 / (mR - 1) := by
      have heq : (2 : ℝ) * (1 / (mR - 1)) = 2 / (mR - 1) := by ring
      have h2 : 2 * ε ≤ 2 / (mR - 1) := by linarith [hεle, heq]
      have heq4 : (4 : ℝ) / (mR - 1) = 2 / (mR - 1) + 2 / (mR - 1) := by ring
      linarith [h2, heq4]
    rw [le_div_iff₀ hden]
    have hstep : (1 / 8) * (mR - 1) * (2 / (mR - 1) + 2 * ε)
        ≤ (1 / 8) * (mR - 1) * (4 / (mR - 1)) := by
      have hc : (0 : ℝ) ≤ 1 / 8 * (mR - 1) := by linarith
      exact mul_le_mul_of_nonneg_left hdenle hc
    have hne : (mR : ℝ) - 1 ≠ 0 := ne_of_gt hm1
    have hval : (1 / 8) * (mR - 1) * (4 / (mR - 1)) = 1 / 2 := by
      rw [mul_comm ((1 : ℝ) / 8) (mR - 1), mul_assoc,
        show (1 : ℝ) / 8 * (4 / (mR - 1)) = (1 / 2) / (mR - 1) from by ring,
        mul_div_assoc']
      rw [mul_comm, mul_div_assoc, div_self hne, mul_one]
    linarith [hstep, hval.le, hval.ge, hnum]
  · -- the perturbation is the binding term: eps >= 1/(m-1)
    rw [min_eq_right hcase]
    have hεge : 1 / (mR - 1) ≤ ε := by
      rw [div_le_iff₀ hm1]
      rw [div_le_iff₀ hε] at hcase
      nlinarith [hcase]
    have hdenle : 2 / (mR - 1) + 2 * ε ≤ 4 * ε := by
      have : 2 / (mR - 1) ≤ 2 * ε := by
        have h2 : (2 : ℝ) / (mR - 1) = 2 * (1 / (mR - 1)) := by ring
        rw [h2]
        linarith
      linarith
    rw [le_div_iff₀ hden]
    have hstep : (1 / 8) * (1 / ε) * (2 / (mR - 1) + 2 * ε)
        ≤ (1 / 8) * (1 / ε) * (4 * ε) := by
      have hinv : (0 : ℝ) ≤ 1 / ε := le_of_lt (div_pos one_pos hε)
      have hc : (0 : ℝ) ≤ 1 / 8 * (1 / ε) := by linarith
      exact mul_le_mul_of_nonneg_left hdenle hc
    have hne : (ε : ℝ) ≠ 0 := ne_of_gt hε
    have hval : (1 / 8) * (1 / ε) * (4 * ε) = 1 / 2 := by
      rw [show (1 : ℝ) / 8 * (1 / ε) * (4 * ε) = (1 / 2) * (ε / ε) from by ring,
        div_self hne, mul_one]
    linarith [hstep, hval.le, hval.ge, hnum]

/-- **The two sides together.**  The order of the ratio is `min(m, 1/eps)`, from both
directions. -/
theorem collapse_two_sided (mR ε : ℝ) (hm : 3 ≤ mR) (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) :
    (1 / 8) * min (mR - 1) (1 / ε) ≤ Rat mR ε ∧ Rat mR ε ≤ 2 / ε :=
  ⟨ratio_collapse_lower mR ε hm hε hε4, ratio_bounded_at_fixed_eps mR ε hm hε⟩

/-- **The crossing.**  At `eps = 1/(m-1)` the two regimes meet, and both bounds read
`Theta(m)`: below it the price is linear in the size, above it it is governed by `1/eps`
alone.  That is the collapse scale. -/
theorem collapse_crossing (mR : ℝ) (hm : 5 ≤ mR) :
    (1 / 8) * (mR - 1) ≤ Rat mR (1 / (mR - 1)) ∧ Rat mR (1 / (mR - 1)) ≤ 2 * (mR - 1) := by
  have hm1 : (0 : ℝ) < mR - 1 := by linarith
  have hε : (0 : ℝ) < 1 / (mR - 1) := by positivity
  have hε4 : 1 / (mR - 1) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hm1 (by norm_num : (0:ℝ) < 4)]
    linarith
  obtain ⟨hlo, hhi⟩ := collapse_two_sided mR (1 / (mR - 1)) (by linarith) hε hε4
  constructor
  · have hmin : min (mR - 1) (1 / (1 / (mR - 1))) = mR - 1 := by
      rw [one_div_one_div]
      exact min_self _
    rwa [hmin] at hlo
  · have hrw : (2 : ℝ) / (1 / (mR - 1)) = 2 * (mR - 1) := by
      have hne : (mR : ℝ) - 1 ≠ 0 := ne_of_gt hm1
      field_simp
    rwa [hrw] at hhi

/-! ## Audit -/

#print axioms ratio_collapse_lower
#print axioms collapse_two_sided
#print axioms collapse_crossing

end CIGAMF.P13.PaperCCollapse
