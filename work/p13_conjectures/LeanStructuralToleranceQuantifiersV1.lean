import «LeanStructuralNormalizedToleranceLawV1»
import «LeanStructuralStaircaseToleranceCurveV1»

/-! # S02: the quantifier order of the normalized tolerance law

`normalized_upper` and `normalized_lower` are both already proved. Nothing here
repairs a gap in either. What is missing is a statement that fixes how the two
compose, because the pair is easy to misread as

> at a fixed normalized tolerance the menu can be unbounded

which is FALSE, and is refuted by the upper bound itself.

The three groups below pin the reading down.

1. `normalized_dimension_le` — at a fixed `eps > 0`, EVERY objective normalized
   by `B = ∑ osc(f i)/2` has `chi_eps ≤ ⌊2/eps⌋ + 1`. The bound mentions no
   component count, no action count and no width. So no family whatsoever can
   have unbounded dimension at one fixed normalized tolerance.

2. `staircase_dimension_one_of_large` — the staircase does not merely stay
   bounded at fixed `eps`, it collapses: past `r ≥ ⌈1/(2 eps)⌉ + 1` a single
   ranking suffices. Note the direction carefully. Collapse is a statement about
   growing `r` at FIXED `eps`, not about raising `eps` at fixed `r`: by
   `exact_curve` the dimension of `F_r` stays exactly `r` for every
   `eps < 1/(2r)`, so a tolerance merely larger than the witness tolerance
   `1/(4r)` does not trivialise it. It takes `eps ≥ 1/(2r)`.

3. `staircase_diagonal_dimension` and `exists_family_with_dimension_gt` — growth
   happens along the DIAGONAL `eps_r = 1/(4r)`, where `chi = r`. The tolerance
   is chosen after `r`; it sits inside the existential and cannot be pulled out.

`quantifier_order_not_interchangeable` states 1 and 3 together. Spelled out,
the pair that is actually proved is

    ∀ eps > 0, ∃ K(eps), ∀ r > 0 :  chi_eps (F_r / r) ≤ K(eps)      (1)
    ∀ K,      ∃ r, ∃ eps > 0     :  chi_eps (F_r / r) > K           (3)

and nothing stronger. In particular (3) is NOT "∀ eps ∃ family with large
dimension": at a fixed `eps` the dimension is capped by `⌊2/eps⌋ + 1` from (1),
so `eps` has to be free to shrink with `r`. It sits inside the existential of
(3) for that reason and cannot be pulled out in front.

## What this is NOT

Not a new asymptotic theorem, and not an independent result. Every inequality
here is an immediate consequence of `normalized_upper`, `dimension_below` and
`dimension_above` in the modules imported above. Its only job is to make the
quantifier structure a checked statement instead of a docstring remark, so a
later write-up cannot silently promote the lower bound to a fixed-tolerance
claim.
-/

namespace CIGAMF.P13.StructuralToleranceQuantifiers
open scoped BigOperators
open Finset
open CIGAMF.V4.SupportGeometry CIGAMF.V4.StructuralRankability
open CIGAMF.P13.StructuralPrefixCoverDimension
open CIGAMF.P13.StructuralMinimumTransversalWidth
open CIGAMF.P13.StructuralStaircaseFamily
open CIGAMF.P13.StructuralStaircaseToleranceLower
open CIGAMF.P13.StructuralNormalizedToleranceLaw
open CIGAMF.P13.StructuralStaircaseToleranceCurve
noncomputable section

/-! ## 1. At a fixed normalized tolerance the bound is width-free -/

/-- Numerical form of `normalized_upper`. The right-hand side depends on `eps`
alone: not on `I`, not on `Ω`, not on `B`. -/
theorem normalized_dimension_le {I Ω : Type*} [Fintype I] [DecidableEq I]
    [Fintype Ω] [Nonempty Ω]
    (f : I → Ω → ℝ) (B : ℝ) (hB : B = ∑ i, osc (f i)/2) (hpos : 0 < B)
    (eps : ℝ) (heps : 0 < eps) :
    prefixDimensionValue (fun S => selectedRadius f S/B) eps ≤ ⌊2/eps⌋₊+1 := by
  unfold prefixDimensionValue
  exact Nat.sInf_le (normalized_upper f B hB hpos eps heps)

/-- The staircase normalizer is exactly `r`, so the width-free bound applies to
the whole family at once, uniformly in `r`. -/
theorem staircase_dimension_le {r : ℕ} (hr : 0 < r) (eps : ℝ) (heps : 0 < eps) :
    prefixDimensionValue
        (fun S => selectedRadius (@staircaseF r) S/(r:ℝ)) eps ≤ ⌊2/eps⌋₊+1 := by
  have hrR : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
  exact normalized_dimension_le (@staircaseF r) (r:ℝ) (normalization r hr).symm
    hrR eps heps

/-- Therefore no family in this normalized class has unbounded prefix dimension
at a single fixed tolerance. This is the statement the lower bound must not be
read as contradicting. -/
theorem no_fixed_tolerance_has_unbounded_staircase_dimension
    (eps : ℝ) (heps : 0 < eps) :
    ∃ K : ℕ, ∀ r : ℕ, 0 < r →
      prefixDimensionValue
        (fun S => selectedRadius (@staircaseF r) S/(r:ℝ)) eps ≤ K :=
  ⟨⌊2/eps⌋₊+1, fun r hr => staircase_dimension_le hr eps heps⟩

/-! ## 2. Past a threshold in `r`, one ranking suffices -/

/-- With `eps` fixed, every staircase from `r = ⌈1/(2 eps)⌉ + 1` upwards needs a
single ranking. The witness family of the lower bound is not merely bounded at
larger tolerances; it is trivial there. -/
theorem staircase_dimension_one_of_large {r : ℕ} (hr : 0 < r) (eps : ℝ)
    (heps : 0 < eps) (hR : ⌈1/(2*eps)⌉₊+1 ≤ r) :
    prefixDimensionValue
      (fun S => selectedRadius (@staircaseF r) S/(r:ℝ)) eps = 1 := by
  apply dimension_above hr eps
  have hrR : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
  have hceil : (1/(2*eps) : ℝ) ≤ (⌈1/(2*eps)⌉₊ : ℝ) := Nat.le_ceil _
  have hcast : ((⌈1/(2*eps)⌉₊ : ℕ) : ℝ)+1 ≤ (r:ℝ) := by exact_mod_cast hR
  have hlt : (1/(2*eps) : ℝ) < (r:ℝ) := by linarith
  have h2eps : (0:ℝ) < 2*eps := by linarith
  have hone : (1:ℝ) < 2*eps*(r:ℝ) := by
    have := (div_lt_iff₀ h2eps).mp hlt
    linarith
  rw [div_le_iff₀ (by linarith : (0:ℝ) < 2*(r:ℝ))]
  linarith

/-! ## 3. Growth lives on the diagonal, with `eps` chosen after `r` -/

/-- On the diagonal `eps_r = 1/(4r)` the dimension is exactly `r`. -/
theorem staircase_diagonal_dimension (r : ℕ) (hr : 0 < r) :
    prefixDimensionValue
      (fun S => selectedRadius (@staircaseF r) S/(r:ℝ)) (1/(4*(r:ℝ))) = r := by
  have hrR : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
  apply dimension_below hr _ (by positivity)
  rw [div_lt_div_iff₀ (by linarith : (0:ℝ) < 4*(r:ℝ)) (by linarith : (0:ℝ) < 2*(r:ℝ))]
  linarith

/-- Unbounded dimension, with the tolerance INSIDE the existential. -/
theorem exists_family_with_dimension_gt (K : ℕ) :
    ∃ (r : ℕ) (eps : ℝ), 0 < r ∧ 0 < eps ∧
      K < prefixDimensionValue
        (fun S => selectedRadius (@staircaseF r) S/(r:ℝ)) eps := by
  refine ⟨K+1, 1/(4*((K+1 : ℕ):ℝ)), by omega, ?_, ?_⟩
  · have : (0:ℝ) < ((K+1 : ℕ):ℝ) := by positivity
    positivity
  · rw [staircase_diagonal_dimension (K+1) (by omega)]
    omega

/-! ## The two statements together -/

/-- S02. Both halves hold, at different quantifier depths, and neither implies
the other's mirror image. Reading the second line with `eps` pulled out in front
is exactly the error the first line forbids. -/
theorem quantifier_order_not_interchangeable :
    (∀ eps : ℝ, 0 < eps → ∀ r : ℕ, 0 < r →
      prefixDimensionValue
        (fun S => selectedRadius (@staircaseF r) S/(r:ℝ)) eps ≤ ⌊2/eps⌋₊+1)
    ∧ (∀ K : ℕ, ∃ (r : ℕ) (eps : ℝ), 0 < r ∧ 0 < eps ∧
      K < prefixDimensionValue
        (fun S => selectedRadius (@staircaseF r) S/(r:ℝ)) eps) :=
  ⟨fun eps heps r hr => staircase_dimension_le hr eps heps,
   exists_family_with_dimension_gt⟩

#print axioms normalized_dimension_le
#print axioms staircase_dimension_le
#print axioms no_fixed_tolerance_has_unbounded_staircase_dimension
#print axioms staircase_dimension_one_of_large
#print axioms staircase_diagonal_dimension
#print axioms exists_family_with_dimension_gt
#print axioms quantifier_order_not_interchangeable

end
end CIGAMF.P13.StructuralToleranceQuantifiers
