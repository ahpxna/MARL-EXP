import «LeanD6BlindLinearOptimalityV1»
import «LeanD6CyclicPhaseLawV1»
import «LeanD6CyclicPhaseDesignV1»

/-!
# The cyclic design attains the linear lower bound with equality

`LeanD6BlindLinearOptimalityV1.actual_variance_lower` bounds every fixed linear
`A`-invariant off-query statistic:

  `|U|^2 ≤ q^4 * |T| * Var(estimator w a)`.

`LeanD6CyclicPhaseLawV1.estimate_variance` computes the variance of the concrete
cyclic estimator.  The two were proved independently and never joined, so the
bound was not known to be attained.  This module closes that.

The join is exact, not asymptotic:

* the cyclic estimator **is** `estimator` with unit weights and `a = L*q^2`
  (`estimate_eq_estimator`);
* its design coefficient is constant on every admissible hidden set
  (`coefficient_cyclic`), which is what puts it inside the comparison class;
* substituting gives `q^4 * |T| * Var = |U|^2` exactly
  (`cyclic_attains_linear_lower_bound`).

Scope.  The class is fixed (non-adaptive) linear statistics of legal off queries
whose mean is `A`-invariant, with unit independent Gaussian noise.  Nothing here
claims optimality over adaptive algorithms, over nonlinear statistics, or over
query families outside this class.
-/

namespace CIGAMF.P13.D6CyclicOptimal

open scoped BigOperators
open Finset MeasureTheory ProbabilityTheory
open CIGAMF.P13.D6Threshold
open CIGAMF.P13.D6BlindLinearVariance
open CIGAMF.P13.D6BlindLinearOptimality
open CIGAMF.P13.D6CyclicPhaseDesign
open CIGAMF.P13.D6CyclicPhaseLaw

noncomputable section

variable {n : ℕ} {C : Type*} [Fintype C] [DecidableEq C] [AddCommGroup C]

/-- The repeated design: block `t.1`, row `t.2`. -/
def repeated {j : I n} (e : C ≃ Coordinates j) (Q : Finset C) (L : ℕ) :
    Fin L × C → Finset (I n) := fun t => actualRow e Q t.2

/-- Every row avoids `j`, hence sits inside the coordinate ground set. -/
theorem repeated_subset {j : I n} (e : C ≃ Coordinates j) (Q : Finset C) (L : ℕ)
    (t : Fin L × C) : repeated e Q L t ⊆ univ.erase j := by
  intro i hi
  obtain ⟨x, _, hx⟩ := mem_image.mp hi
  refine mem_erase.mpr ⟨?_, mem_univ i⟩
  intro h
  exact (e x).property (h ▸ hx)

theorem repeated_card {j : I n} (e : C ≃ Coordinates j) (Q : Finset C) (L : ℕ)
    (t : Fin L × C) : (repeated e Q L t).card = Q.card :=
  actualRow_card e Q t.2

/-- **The design coefficient is the same for every admissible hidden set.**
This is the membership test for the comparison class of `actual_variance_lower`. -/
theorem coefficient_cyclic {j : I n} (e : C ≃ Coordinates j) (Q : Finset C)
    (q L : ℕ) (hQ : Q.card = q) (B : Finset (I n))
    (hB : B ∈ (univ.erase j : Finset (I n)).powersetCard q) :
    coefficient (repeated e Q L) (fun _ => (1:ℝ)) B = (L:ℝ) * (q:ℝ)^2 := by
  rw [mem_powersetCard] at hB
  have hjB : j ∉ B := fun h => (mem_erase.mp (hB.1 h)).1 rfl
  have hrow : (∑ c : C, ((actualRow e Q c ∩ B).card : ℝ)) = (q:ℝ) * (q:ℝ) := by
    rw [actual_intersection_sum e Q B hjB, hQ, hB.2]
  unfold coefficient repeated
  rw [Fintype.sum_prod_type]
  simp only [one_mul]
  rw [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, hrow]
  ring

/-- **The cyclic estimator is a unit-weight linear statistic.** -/
theorem estimate_eq_estimator (q L : ℕ) :
    estimate (C := C) q L
      = estimator (T := Fin L × C) (fun _ => (1:ℝ)) ((L:ℝ) * (q:ℝ)^2) := by
  funext x
  unfold estimate estimator
  have hone : (∑ _t : Fin L × C, (1:ℝ)) = (L:ℝ) * Fintype.card C := by
    rw [Finset.sum_const, card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    ring
  rw [hone]
  simp only [one_mul]

/-- **The lower bound is attained, with equality.**  For the cyclic design at
`L` blocks the inequality of `actual_variance_lower` is tight. -/
theorem cyclic_attains_linear_lower_bound {j : I n}
    (e : C ≃ Coordinates j) (Q : Finset C) (q L : ℕ)
    (hq : 3 ≤ q) (hL : 0 < L) (hQ : Q.card = q) (hC : 0 < Fintype.card C)
    (A : Finset (I n)) (hj : j ∉ A) (hB : (others A j).card = q) (mu : ℝ)
    (hU : (univ.erase j : Finset (I n)).card = Fintype.card C) :
    ((univ.erase j : Finset (I n)).card : ℝ)^2
      = (q:ℝ)^4 * Fintype.card (Fin L × C) *
          variance (estimate (C := C) q L)
            (observations (actualRow e Q) A j mu L) := by
  have hq0 : (q:ℝ) ≠ 0 := by
    have : 0 < q := by omega
    exact_mod_cast (ne_of_gt this)
  have hL0 : (L:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
  have hC0 : (Fintype.card C : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hC)
  have hvar := estimate_variance (actualRow e Q) A j q L (by omega) hL hC mu
    (actual_mean_sum e Q q hq hQ A hj hB mu)
  rw [hvar, hU, Fintype.card_prod, Fintype.card_fin]
  push_cast
  field_simp <;> ring

#print axioms repeated_subset
#print axioms coefficient_cyclic
#print axioms estimate_eq_estimator
#print axioms cyclic_attains_linear_lower_bound

end
end CIGAMF.P13.D6CyclicOptimal
