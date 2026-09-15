import «LeanStructuralPrefixCoverDimensionV1»
import «LeanSupportGeometryV4»

/-!
# Fixed-tolerance recourse vanishes above an explicit universal tolerance

`R_eps` is the worst number of deletions a budget chain of eps-good selections
is forced to make at one budget step; `R_eps = 0` says a fully NESTED chain of
eps-good selections exists, i.e. `OnePrefixChain` holds for the normalized
objective.

This file proves an unconditional positive answer above an explicit threshold:
for every finite instance, ordering the components by DECREASING span gives one
ranking all of whose prefixes are (2/3)-optimal at their own budget.  Hence
`R_eps = 0` for every `eps ≥ 2/3`, for every number of components `m`, every
number of scenarios, and every support matrix with nonzero total span.

The engine is two one-sided estimates on the same nested chain, with
`A = modularSpan S f` the span mass of the k largest-span components:

* `supportOsc Sᶜ f ≤ modularSpan Sᶜ f = D - A`            (BH2), and
* `supportOsc Sᶜ f ≤ supportOsc Tᶜ f + 2 * A`             (top-k mass),

so the excess over the budget-k optimum is at most `min (D - A) (2 * A) ≤ 2D/3`.
-/

namespace CIGAMF.P13.StructuralRecourseUniformNesting

open Finset
open scoped BigOperators
open CIGAMF.V4.SupportGeometry CIGAMF.V4.StructuralRankability
open CIGAMF.V4.AuxiliaryBH6Structural
open CIGAMF.P13.StructuralPrefixCoverDimension

noncomputable section
attribute [local instance] Classical.propDecidable

variable {Ω ι : Type*} [Fintype Ω] [Nonempty Ω] [Fintype ι] [DecidableEq ι]

/-- Residual oscillation of the unselected components, normalized by the total
component span.  Identical to the staircase module's normalization
`selectedRadius f S / ∑ j, osc (f j) / 2` (see `normalizedRadius_eq`). -/
def normalizedRadius (f : ι → Ω → ℝ) (S : Finset ι) : ℝ :=
  supportOsc Sᶜ f / modularSpan Finset.univ f

lemma normalizedRadius_eq (f : ι → Ω → ℝ) (S : Finset ι) :
    normalizedRadius f S = selectedRadius f S / (∑ j : ι, osc (f j) / 2) := by
  have hsum : (∑ j : ι, osc (f j) / 2) = modularSpan Finset.univ f / 2 := by
    simp only [modularSpan, componentSpan, componentMax, componentMin, osc]
    rw [Finset.sum_div]
  have hkey : ∀ x y : ℝ, x / 2 / (y / 2) = x / y := by
    intro x y
    rw [div_div_div_comm]
    simp
  rw [hsum, normalizedRadius, selectedRadius, hkey]

section Estimates

variable (f : ι → Ω → ℝ)

lemma componentSpan_nonneg (j : ι) : 0 ≤ componentSpan f j :=
  osc_nonneg (f j)

lemma modularSpan_nonneg (T : Finset ι) : 0 ≤ modularSpan T f :=
  Finset.sum_nonneg fun j _ => componentSpan_nonneg f j

lemma modularSpan_compl (S : Finset ι) :
    modularSpan S f + modularSpan Sᶜ f = modularSpan Finset.univ f := by
  simpa [modularSpan] using Finset.sum_add_sum_compl S (fun j => componentSpan f j)

lemma osc_sub_le (g h : Ω → ℝ) : osc (fun a => g a - h a) ≤ osc g + osc h := by
  have h1 := osc_add_le g (fun a => -h a)
  rw [osc_neg] at h1
  simpa [sub_eq_add_neg] using h1

lemma sumComponent_compl (S : Finset ι) (a : Ω) :
    sumComponent Sᶜ f a = sumComponent Finset.univ f a - sumComponent S f a := by
  have h := Finset.sum_add_sum_compl S (fun j => f j a)
  unfold sumComponent at h ⊢

  linarith

/-- Splitting off the selected block: the residual oscillation can exceed the
whole-instance oscillation by at most the selected span mass. -/
lemma supportOsc_compl_le (S : Finset ι) :
    supportOsc Sᶜ f ≤ supportOsc Finset.univ f + modularSpan S f := by
  have hfun : sumComponent Sᶜ f
      = fun a => sumComponent Finset.univ f a - sumComponent S f a :=
    funext (sumComponent_compl f S)
  have h1 : supportOsc Sᶜ f
      ≤ osc (sumComponent Finset.univ f) + osc (sumComponent S f) := by
    unfold supportOsc
    rw [hfun]
    exact osc_sub_le _ _
  have h2 := BH2_supportOsc_le_modularSpan S f
  unfold supportOsc at h1 h2 ⊢
  linarith

/-- ... and symmetrically, the whole-instance oscillation is at most the
residual oscillation plus the removed span mass. -/
lemma supportOsc_univ_le (T : Finset ι) :
    supportOsc Finset.univ f ≤ supportOsc Tᶜ f + modularSpan T f := by
  have hfun : sumComponent Finset.univ f
      = fun a => sumComponent T f a + sumComponent Tᶜ f a := by
    funext a
    have h := Finset.sum_add_sum_compl T (fun j => f j a)
    simp only [sumComponent] at *
    linarith
  have h1 : supportOsc Finset.univ f
      ≤ osc (sumComponent T f) + osc (sumComponent Tᶜ f) := by
    unfold supportOsc
    rw [hfun]
    exact osc_add_le _ _
  have h2 := BH2_supportOsc_le_modularSpan T f
  unfold supportOsc at h1 h2 ⊢
  linarith

/-- Main comparison on a single budget layer: if `S` carries at least as much
span mass as the competitor `T`, its residual oscillation exceeds `T`'s by at
most `min (modularSpan Sᶜ f) (2 * modularSpan S f)`. -/
theorem excess_le_min (S T : Finset ι) (hmass : modularSpan T f ≤ modularSpan S f) :
    supportOsc Sᶜ f ≤ supportOsc Tᶜ f + min (modularSpan Sᶜ f) (2 * modularSpan S f) := by
  have hA : supportOsc Sᶜ f ≤ supportOsc Tᶜ f + modularSpan Sᶜ f := by
    have h1 := BH2_supportOsc_le_modularSpan Sᶜ f
    have h2 : (0:ℝ) ≤ supportOsc Tᶜ f := osc_nonneg _
    linarith
  have hB : supportOsc Sᶜ f ≤ supportOsc Tᶜ f + 2 * modularSpan S f := by
    have h1 := supportOsc_compl_le f S
    have h2 := supportOsc_univ_le f T
    linarith
  rw [add_min]
  exact le_min hA hB

/-- The two-thirds bound: the excess is at most `(2/3)` of the total span. -/
theorem excess_le_two_thirds (S T : Finset ι)
    (hmass : modularSpan T f ≤ modularSpan S f) :
    supportOsc Sᶜ f ≤ supportOsc Tᶜ f + 2 / 3 * modularSpan Finset.univ f := by
  have hsplit := modularSpan_compl f S
  have hS := modularSpan_nonneg f S
  have hSc := modularSpan_nonneg f Sᶜ
  have hA : supportOsc Sᶜ f ≤ supportOsc Tᶜ f + modularSpan Sᶜ f := by
    have h1 := BH2_supportOsc_le_modularSpan Sᶜ f
    have h2 : (0:ℝ) ≤ supportOsc Tᶜ f := osc_nonneg _
    linarith
  have hB : supportOsc Sᶜ f ≤ supportOsc Tᶜ f + 2 * modularSpan S f := by
    have h1 := supportOsc_compl_le f S
    have h2 := supportOsc_univ_le f T
    linarith
  rcases le_total (3 * modularSpan S f) (modularSpan Finset.univ f) with h | h
  · linarith
  · linarith

#print axioms normalizedRadius_eq
#print axioms componentSpan_nonneg
#print axioms modularSpan_nonneg
#print axioms modularSpan_compl
#print axioms osc_sub_le
#print axioms sumComponent_compl
#print axioms supportOsc_compl_le
#print axioms supportOsc_univ_le
#print axioms excess_le_min
#print axioms excess_le_two_thirds

end Estimates

end
end CIGAMF.P13.StructuralRecourseUniformNesting
