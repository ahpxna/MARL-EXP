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

private theorem chi3_nonopt_one_gap
    (S : Finset (Fin 5)) (hcard : S.card = 1)
    (hne : S ≠ ({2} : Finset (Fin 5))) :
    ∃ a b : Fin 5,
      3 ≤ |sumComponent Sᶜ chi3F a - sumComponent Sᶜ chi3F b| := by
  rcases Finset.card_eq_one.mp hcard with ⟨j, rfl⟩
  fin_cases j
  · exact ⟨0, 1, by norm_num [sumComponent, chi3F]⟩
  · exact ⟨0, 1, by norm_num [sumComponent, chi3F]⟩
  · exact False.elim (hne rfl)
  · exact ⟨1, 4, by norm_num [sumComponent, chi3F]⟩
  · exact ⟨0, 4, by norm_num [sumComponent, chi3F]⟩

theorem chi3_one_nonopt_radius_gt_half
    (S : Finset (Fin 5)) (hcard : S.card = 1)
    (hne : S ≠ ({2} : Finset (Fin 5))) :
    (1 / 2 : ℝ) < selectedRadius chi3F S := by
  rcases chi3_nonopt_one_gap S hcard hne with ⟨a, b, hgap⟩
  have hrad := selectedRadius_ge_abs_gap chi3F S a b
  nlinarith

end CIGAMF.P13.StructuralPrefixCoverChi3Witness
