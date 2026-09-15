import «LeanD6PairContractionCounterexample»

/-!
# Kernel-checked replacement for the two `native_decide` steps of the pair-contraction counterexample

`LeanD6PairContractionCounterexample` proves the uniform mixed-difference bound
`|mixedDifferenceZ i x c| <= 13` and one closed evaluation by `native_decide`,
which records its answer through the axiom `Lean.ofReduceBool`.  That bound is
not auxiliary: the module's headline theorem
`pair_contraction_route_killed_exact` consumes it directly, so the headline was
a COMPILED ARTIFACT rather than PROVED.

Nothing is deleted.  Both facts are integer arithmetic on a four-coordinate
binary domain, so they are re-proved here by kernel `decide`, and the two
statements that depend on them are repeated.

Scale of the kernel work: `Fin 4 -> Fin 2` has 16 elements, so the uniform
bound is `4 * 16 * 16 = 1024` leaf checks, each walking the depth-four integer
decision tree `pcWorld4Z` four times.  The enumeration is split by the
coordinate index into four theorems of 256 leaves, so that a kernel failure
localises to one index instead of the whole bound.  The closed evaluation is a
single leaf.
-/

namespace CIGAMF.P13.D6PairContractionKernel

open scoped BigOperators Matrix
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.V4.SupportGeometry
open CIGAMF.V6.FunctionalRanking
open CIGAMF.P13.D6PairContractionCounterexample

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ## The uniform mixed-difference bound, one coordinate at a time -/

theorem mdz_bound_zero : ∀ x c : Fin 4 → Fin 2, |mixedDifferenceZ 0 x c| ≤ 13 := by
  decide

theorem mdz_bound_one : ∀ x c : Fin 4 → Fin 2, |mixedDifferenceZ 1 x c| ≤ 13 := by
  decide

theorem mdz_bound_two : ∀ x c : Fin 4 → Fin 2, |mixedDifferenceZ 2 x c| ≤ 13 := by
  decide

theorem mdz_bound_three : ∀ x c : Fin 4 → Fin 2, |mixedDifferenceZ 3 x c| ≤ 13 := by
  decide

theorem mixedDifferenceZ_le_thirteen_kernel
    (i : Fin 4) (x c : Fin 4 → Fin 2) :
    |mixedDifferenceZ i x c| ≤ 13 := by
  fin_cases i
  · exact mdz_bound_zero x c
  · exact mdz_bound_one x c
  · exact mdz_bound_two x c
  · exact mdz_bound_three x c

/-! ## The cast to the real-valued mixed difference -/

theorem mixedDifference_eq_cast_kernel
    (i : Fin 4) (x c : Fin 4 → Fin 2) :
    mixedDifference pcWorld4 i x c = (mixedDifferenceZ i x c : ℝ) := by
  simp [mixedDifference, mixedDifferenceZ, pcWorld4]

theorem mixedDifference_le_thirteen_kernel
    (i : Fin 4) (x c : Fin 4 → Fin 2) :
    |mixedDifference pcWorld4 i x c| ≤ 13 := by
  have hz := mixedDifferenceZ_le_thirteen_kernel i x c
  rw [mixedDifference_eq_cast_kernel]
  exact_mod_cast hz

/-- Sharpness: the bound 13 is attained, so it is the exact modulus and not a
convenient over-estimate. -/
theorem mixedDifference_attains_thirteen_kernel :
    |mixedDifference pcWorld4 0 (action4 0 0 0 0) (action4 1 1 0 1)| = 13 := by
  rw [mixedDifference_eq_cast_kernel]
  have hz : mixedDifferenceZ 0 (action4 0 0 0 0) (action4 1 1 0 1) = (13 : ℤ) := by
    decide
  rw [hz]
  norm_num

/-! ## The headline conclusion, with no `Lean.ofReduceBool` in its dependencies -/

theorem pair_contraction_route_killed_exact_kernel :
    IsTopKByScore (fun j ↦ osc (productResponse pointMass4 pcWorld4 j))
        selected 2 ∧
    productCompressionLoss pcWorld4 (productResponse pointMass4 pcWorld4)
        selected -
      productCompressionLoss pcWorld4 (productResponse pointMass4 pcWorld4)
        competitor = 13 ∧
    (∀ i x c, |mixedDifference pcWorld4 i x c| ≤ 13) ∧
    (17 - 4 ≤ (3 : ℝ) * 13 / 2) ∧
    17 - 4 > 13 + (-1 / 2 : ℝ) ∧
    17 - 4 > 13 + (-1 : ℝ) := by
  refine ⟨selected_is_topC, ?_, mixedDifference_le_thirteen_kernel, by norm_num,
    by norm_num, by norm_num⟩
  rw [selected_loss, competitor_loss]
  norm_num

#print axioms mdz_bound_zero
#print axioms mdz_bound_one
#print axioms mdz_bound_two
#print axioms mdz_bound_three
#print axioms mixedDifferenceZ_le_thirteen_kernel
#print axioms mixedDifference_le_thirteen_kernel
#print axioms mixedDifference_attains_thirteen_kernel
#print axioms pair_contraction_route_killed_exact_kernel

end CIGAMF.P13.D6PairContractionKernel
