import Mathlib
import «LeanProductMixedDifferenceV4»
import «LeanSupportGeometryV4»
import «LeanPairwiseMasterV4»

/-!
# Structural elimination of typed certificate obligations

These lemmas state concrete conditions under which an evidence type contributes
no unresolved correction.  They are deterministic adapters to existing proved
geometry; they do not assert statistical coverage or empirical usefulness.
-/

namespace CIGAMF.P13.TypedObstructionElimination

open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.V4.SupportGeometry
open CIGAMF.V4.Pairwise

variable {U : Type*} [Fintype U] [Nonempty U]

/-- Vanishing mixed differences remove the interaction approximation error:
the product-reference first-order reconstruction is the world itself. -/
theorem interaction_obligation_eliminated_of_zero_mixed_difference {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1)
    (hZero : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      mixedDifference F i x c = 0) :
    F = productA q F := by
  funext x
  have hBound := D3_product_surrogate_mixed_difference_bound q F 0
    hWeight hNorm (by norm_num)
    (by intro i y c; simp [hZero i y c]) x
  have hBoundZero : |F x - productA q F x| ≤ 0 := by simpa using hBound
  have hAbs : |F x - productA q F x| = 0 :=
    le_antisymm hBoundZero (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp hAbs)

variable {Ω I : Type*} [Fintype Ω] [Nonempty Ω]
  [Fintype I] [DecidableEq I]

/-- Joint attainment of all component extrema on the queried coordinate set
removes its support-deficit correction exactly. -/
theorem support_obligation_eliminated_of_coextremizable
    (T : Finset I) (f : I → Ω → ℝ) (amax amin : Ω)
    (hmax : ∀ j ∈ T, f j amax = componentMax f j)
    (hmin : ∀ j ∈ T, f j amin = componentMin f j) :
    deficit T f = 0 := by
  unfold deficit
  rw [BH4_coextremizable_exactness T f amax amin hmax hmin]
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Strict separation of covered score intervals removes Top-K ranking
ambiguity.  This is an adapter to the existing operational interval theorem. -/
theorem ranking_obligation_eliminated_of_interval_separation
    (C Chat e : ι → ℝ) (selected : Finset ι) (k : ℕ)
    (hcover : scoreCovered C Chat e)
    (hcard : selected.card = k)
    (hseparation : ∀ j ∈ selected, ∀ l ∉ selected,
      upperScore Chat e l < lowerScore Chat e j) :
    IsStrictTopK C selected k :=
  P3_exact_topk_interval_certificate C Chat e selected k hcover hcard
    hseparation

/-- Exact reference invariance makes the reference-error radius zero. -/
theorem reference_obligation_eliminated_of_invariance
    (trueScore estimatedScore : ι → ℝ)
    (hInvariant : estimatedScore = trueScore) :
    ∀ j, |estimatedScore j - trueScore j| = 0 := by
  subst estimatedScore
  simp

end CIGAMF.P13.TypedObstructionElimination
