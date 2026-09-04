import Mathlib
import «LeanStructuralPrefixCoverWitnessesV1»

/-!
# A five-relation exact `chi_prefix = 3` support-radius witness

Finite search found a five-support-action world with unique exact optima
`{2}`, `{0,2}`, `{0,1,4}`, `{1,2,3,4}` at budgets one through four.  The
first two are nested, whereas each subsequent transition breaks nesting.  This
file turns that exact finite witness into the first nontrivial lower-bound
target for prefix-cover dimension.
-/

namespace CIGAMF.P13.StructuralPrefixCoverChi3Witness

open CIGAMF.V4.SupportGeometry
open CIGAMF.V4.StructuralRankability
open CIGAMF.P13.StructuralPrefixCoverDimension
open CIGAMF.P13.StructuralPrefixCoverWitnesses

variable {Ω ι : Type*} [Fintype Ω] [Nonempty Ω]
  [Fintype ι] [DecidableEq ι]

theorem selectedRadius_ge_abs_gap
    (f : ι → Ω → ℝ) (S : Finset ι) (a b : Ω) :
    |sumComponent Sᶜ f a - sumComponent Sᶜ f b| / 2 ≤ selectedRadius f S := by
  let g : Ω → ℝ := sumComponent Sᶜ f
  have hupper : g a - g b ≤ maxVal g - minVal g := by
    linarith [le_maxVal g a, minVal_le g b]
  have hlower : -(maxVal g - minVal g) ≤ g a - g b := by
    linarith [le_maxVal g b, minVal_le g a]
  have habs : |g a - g b| ≤ maxVal g - minVal g := abs_le.mpr ⟨hlower, hupper⟩
  change |g a - g b| / 2 ≤ (maxVal g - minVal g) / 2
  nlinarith

@[simp] private theorem fin5_compl_0 :
    ({0} : Finset (Fin 5))ᶜ = {1, 2, 3, 4} := by decide
@[simp] private theorem fin5_compl_1 :
    ({1} : Finset (Fin 5))ᶜ = {0, 2, 3, 4} := by decide
@[simp] private theorem fin5_compl_2 :
    ({2} : Finset (Fin 5))ᶜ = {0, 1, 3, 4} := by decide
@[simp] private theorem fin5_compl_3 :
    ({3} : Finset (Fin 5))ᶜ = {0, 1, 2, 4} := by decide
@[simp] private theorem fin5_compl_4 :
    ({4} : Finset (Fin 5))ᶜ = {0, 1, 2, 3} := by decide

/-
OPEN SEARCH WITNESS (not a Lean theorem yet): exact enumeration over this
finite support table reports unique budget optima

  k=1: {2},  k=2: {0,2},  k=3: {0,1,4},  k=4: {1,2,3,4}.

Their successive nonnesting forces a three-ranking prefix cover if the table
is formally evaluated.  The next proof task is deliberately mechanical:
establish all finite radius comparisons using `selectedRadius_ge_abs_gap`,
then derive the no-two-menu lower bound.  No `chi_prefix >= 3` claim is made
by this module until those comparisons compile.
-/

end CIGAMF.P13.StructuralPrefixCoverChi3Witness
