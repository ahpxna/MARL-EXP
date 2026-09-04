import Mathlib

/-!
# The balanced-complement one-free-unit reduction

In an even `m = 2d` complement comparison, the two endpoint patches pay at
most `d * delta` each.  The sharp coefficient follows once endpoint and Top-C
slack save one full unit `delta`.  This file proves that exact algebraic
reduction; proving the scientific OFU premise from product-reference
consistency remains open.
-/

namespace CIGAMF.P13.D6OneFreeUnit

theorem balanced_half_factor_of_one_free_unit
    (d decision delta patchPlus patchMinus topSlack : ℝ)
    (hDecision : 2 * decision ≤ patchPlus + patchMinus - topSlack)
    (hPlus : patchPlus ≤ d * delta)
    (hMinus : patchMinus ≤ d * delta)
    (hOFU : delta ≤
      (d * delta - patchPlus) + (d * delta - patchMinus) + topSlack) :
    decision ≤ (2 * d - 1) * delta / 2 := by
  have hSlackPlus : 0 ≤ d * delta - patchPlus := sub_nonneg.mpr hPlus
  have hSlackMinus : 0 ≤ d * delta - patchMinus := sub_nonneg.mpr hMinus
  linarith

theorem one_free_unit_from_component_slacks
    (d delta patchPlus patchMinus topSlack
      slackPlus slackMinus : ℝ)
    (hSlackPlus : slackPlus = d * delta - patchPlus)
    (hSlackMinus : slackMinus = d * delta - patchMinus)
    (hSave : delta ≤ slackPlus + slackMinus + topSlack) :
    delta ≤
      (d * delta - patchPlus) + (d * delta - patchMinus) + topSlack := by
  rw [← hSlackPlus, ← hSlackMinus]
  exact hSave

end CIGAMF.P13.D6OneFreeUnit
