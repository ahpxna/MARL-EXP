import Mathlib
import «LeanProductMixedDifferenceV4»

/-! Exact D6 sharpness evidence.  S1 is closed by a two-coordinate product
world.  S2/S3 are intentionally not asserted: exhaustive rational search is
reported separately and did not attain the decision factor. -/

namespace CIGAMF.V7.D6Sharpness

open scoped BigOperators
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference

def zeroAction2 : Fin 2 → Fin 2 := fun _ => 0
def oneAction2 : Fin 2 → Fin 2 := fun _ => 1

def pointMassZero2 (_i : Fin 2) (u : Fin 2) : ℝ := if u = 0 then 1 else 0

def andWorld2 (x : Fin 2 → Fin 2) : ℝ :=
  if x 0 = 1 ∧ x 1 = 1 then 1 else 0

theorem pointMassZero2_jointWeight (c : Fin 2 → Fin 2) :
    jointWeight pointMassZero2 c = if c = zeroAction2 then 1 else 0 := by
  classical
  by_cases h : c = zeroAction2
  · subst c
    norm_num [jointWeight, pointMassZero2, zeroAction2, Fin.prod_univ_two]
  · have hc : c 0 ≠ 0 ∨ c 1 ≠ 0 := by
      by_contra hn
      push_neg at hn
      apply h
      funext i
      fin_cases i <;> simp [zeroAction2, hn.1, hn.2]
    rcases hc with hc | hc
    · simp [jointWeight, pointMassZero2, Fin.prod_univ_two, hc, h]
    · simp [jointWeight, pointMassZero2, Fin.prod_univ_two, hc, h]

theorem pointMassZero2_expectation (G : (Fin 2 → Fin 2) → ℝ) :
    productExpectation pointMassZero2 G = G zeroAction2 := by
  classical
  unfold productExpectation
  simp_rw [pointMassZero2_jointWeight]
  rw [Finset.sum_eq_single zeroAction2]
  · simp
  · intro b hb hne
    simp [hne]
  · simp

theorem andWorld2_productA_at_one :
    productA pointMassZero2 andWorld2 oneAction2 = 0 := by
  simp [productA, CIGAMF.V4.ProductSurrogate.surrogate,
    productResponse, productB, pointMassZero2_expectation,
    andWorld2, zeroAction2, oneAction2, Fin.sum_univ_two]

theorem andWorld2_residual_attains_one :
    |andWorld2 oneAction2 - productA pointMassZero2 andWorld2 oneAction2| = 1 := by
  rw [andWorld2_productA_at_one]
  norm_num [andWorld2, oneAction2]

theorem andWorld2_mixed_difference_attains_one :
    |mixedDifference andWorld2 (0 : Fin 2) oneAction2 zeroAction2| = 1 := by
  norm_num [mixedDifference, andWorld2, oneAction2, zeroAction2,
    Function.update]

/- Any uniform mixed-difference modulus for this valid product world is at
least one, and the approximation residual is exactly one.  Thus the D6
coefficient `(m-1)=1` cannot be uniformly reduced; this closes S1 globally
because any proposed smaller universal multiplier already fails at m=2. -/
theorem S1_D6_approximation_constant_sharp
    (delta : ℝ)
    (hdelta : ∀ (i : Fin 2) (x c : Fin 2 → Fin 2),
      |mixedDifference andWorld2 i x c| ≤ delta) :
    1 ≤ delta ∧
      |andWorld2 oneAction2 - productA pointMassZero2 andWorld2 oneAction2| = 1 := by
  constructor
  · exact le_trans (le_of_eq andWorld2_mixed_difference_attains_one.symm)
      (hdelta 0 oneAction2 zeroAction2)
  · exact andWorld2_residual_attains_one

end CIGAMF.V7.D6Sharpness
