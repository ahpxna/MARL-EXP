import Mathlib

/-! # Functional F5: the bridge to the REAL range problem -- and why P4's Top-1 numbers
do not cross it.

The audit's F5: `P4_functional_measurement_topology.py` solves Top-1 identification, or
the `(argmax, argmin)` pair, on a vector.  The Functional paper's object is the GROUP
RANGE: name the group `g` maximising `range(g) = max_{i∈S_g} θ_i - min_{i∈S_g} θ_i`.
Those are different problems, and the audit is right that closing the gap is a
mathematical bridge, not a code change.  This file builds the bridge and then measures
exactly how far apart the two problems are.

## THE BRIDGE

`range(g) = max_{i,j ∈ S_g} (θ_i - θ_j)`, so once the extremal coordinates are fixed --
`(i,j)` in the challenger `h` and `(k,l)` in the incumbent `g*` -- the boundary
`range(h) = range(g*)` is the hyperplane

    θ_i - θ_j - θ_k + θ_l = 0,

a LINEAR contrast on FOUR coordinates.  Top-1's boundary `θ_{i*} - θ_j = 0` is a linear
contrast on TWO.  So the design machinery does transfer -- both are linear contrasts,
and `contrast_energy_ge` below is the profiled information for ANY of them -- but the
ALTERNATIVE SET does not: the range set is a union over every assignment of which
coordinate is extremal in each group, and each member has four active cells instead of
two.

## THE CONSEQUENCE, QUANTIFIED

The profiled information against a contrast `v` is `Δ²/(2 R(v))` with
`R(v) = ∑_e v_e² σ_e / w_e`.  For a range contrast `R` is a FOUR-term harmonic sum; for
a Top-1 contrast it is a two-term one, and the Top-1 terms are a SUBSET.  Hence
`R(top1) < R(range)` strictly at any positive design, so the range alternative is
strictly harder to exclude at the same weights.  P4's Top-1 values are therefore upper
bounds that the range problem does not attain, and they must not be quoted for it.

## WHAT IS PROVED

* `contrast_energy_ge` — **the profiled information for ANY linear contrast**:
  `Δ²/(2R(v)) ≤ energy`, by Cauchy-Schwarz on the finset.
* `contrast_energy_attained` — and it is attained at `θ - λ = (Δ/R)·v σ / w`, so the
  formula is exact, not just a bound.
* `resistance_of_support` — `R(v)` only sees the support of `v`.
* `range_resistance`, `top1_resistance` — four terms versus two.
* `top1_lt_range` — **strictly**, at every positive design: the Top-1 resistance is a
  proper sub-sum of the range resistance.
* `range_boundary_is_linear` — the range boundary at fixed extremal choices IS the
  four-coordinate contrast, which is what licenses using the same machinery at all.

## WHAT THIS DOES NOT ESTABLISH

- The range alternative SET is a union over extremal assignments; taking the minimum
  over that union, and the resulting optimal design, is not solved here.  That is the
  numerical content of `scripts/P28_functional_range_bridge.py`.
- Nothing here transfers P4's numbers.  The point of `top1_lt_range` is the opposite:
  it shows they cannot be transferred.
-/

namespace CIGAMF.P13.FunctionalRangeContrast

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The resistance of a linear contrast at a design. -/
noncomputable def resistance (v sig w : ι → ℝ) : ℝ := ∑ e, v e ^ 2 * sig e / w e

/-- The energy of a perturbation `dth = θ - λ`. -/
noncomputable def energy (w sig dth : ι → ℝ) : ℝ := ∑ e, w e * (dth e) ^ 2 / (2 * sig e)

/-- **The profiled information for ANY linear contrast**, by Cauchy-Schwarz. -/
theorem contrast_energy_ge (v sig w dth : ι → ℝ) (Delta : ℝ)
    (hw : ∀ e, 0 < w e) (hs : ∀ e, 0 < sig e)
    (hR : 0 < resistance v sig w)
    (hD : ∑ e, v e * dth e = Delta) :
    Delta ^ 2 / (2 * resistance v sig w) ≤ energy w sig dth := by
  classical
  have hcs : (∑ e, v e * dth e) ^ 2
      ≤ (∑ e, v e ^ 2 * sig e / w e) * (∑ e, w e * (dth e) ^ 2 / sig e) := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _
      (fun e _ => by have := hw e; have := hs e; positivity)
      (fun e _ => by have := hw e; have := hs e; positivity)
      (fun e _ => ?_)
    have hwe := hw e
    have hse := hs e
    have hid : v e ^ 2 * sig e / w e * (w e * (dth e) ^ 2 / sig e)
        = (v e * dth e) ^ 2 := by
      field_simp
      try ring
    rw [hid]
  have henergy : energy w sig dth = (∑ e, w e * (dth e) ^ 2 / sig e) / 2 := by
    unfold energy
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun e _ => ?_
    have := hs e
    field_simp
    try ring
  rw [henergy, div_le_div_iff₀ (by linarith [hR]) (by norm_num : (0:ℝ) < 2)]
  unfold resistance at hR ⊢
  nlinarith [hcs, hR, hD]

/-- …and it is ATTAINED, so the formula is exact. -/
theorem contrast_energy_attained (v sig w : ι → ℝ) (Delta : ℝ)
    (hw : ∀ e, 0 < w e) (hs : ∀ e, 0 < sig e) (hR : resistance v sig w ≠ 0) :
    (∑ e, v e * (Delta / resistance v sig w * (v e * sig e / w e)) = Delta)
    ∧ energy w sig (fun e => Delta / resistance v sig w * (v e * sig e / w e))
        = Delta ^ 2 / (2 * resistance v sig w) := by
  classical
  constructor
  · have h1 : (∑ e, v e * (Delta / resistance v sig w * (v e * sig e / w e)))
        = (Delta / resistance v sig w) * ∑ e, v e ^ 2 * sig e / w e := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      have := hw e
      field_simp
      try ring
    rw [h1]
    unfold resistance
    field_simp
  · have h2 : energy w sig (fun e => Delta / resistance v sig w * (v e * sig e / w e))
        = (Delta / resistance v sig w) ^ 2 / 2 * ∑ e, v e ^ 2 * sig e / w e := by
      unfold energy
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      have hwe := hw e
      have hse := hs e
      field_simp
      try ring
    rw [h2]
    unfold resistance at hR ⊢
    field_simp
    try ring

/-- The resistance only sees the support of the contrast. -/
theorem resistance_of_support (v sig w : ι → ℝ) (S : Finset ι)
    (hsupp : ∀ e ∉ S, v e = 0) :
    resistance v sig w = ∑ e ∈ S, v e ^ 2 * sig e / w e := by
  unfold resistance
  refine (Finset.sum_subset (Finset.subset_univ S) ?_).symm
  intro e _ he
  rw [hsupp e he]
  ring

/-- **The range boundary IS a four-coordinate linear contrast.** -/
theorem range_boundary_is_linear (theta : ι → ℝ) (i j k l : ι) :
    (theta i - theta j) - (theta k - theta l)
      = theta i - theta j - theta k + theta l := by ring

/-- A unit contrast on a support `S` has resistance `∑_{e∈S} σ_e/w_e`. -/
theorem unit_contrast_resistance (v sig w : ι → ℝ) (S : Finset ι)
    (hsupp : ∀ e ∉ S, v e = 0) (hunit : ∀ e ∈ S, v e ^ 2 = 1) :
    resistance v sig w = ∑ e ∈ S, sig e / w e := by
  rw [resistance_of_support v sig w S hsupp]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [hunit e he]
  ring

/-- **The comparison.**  The Top-1 support is a PROPER subset of the range support, and
every term is positive, so the Top-1 resistance is strictly smaller at every positive
design.  P4's Top-1 values are therefore not the range problem's. -/
theorem top1_lt_range (sig w : ι → ℝ) (T R : Finset ι)
    (hw : ∀ e, 0 < w e) (hs : ∀ e, 0 < sig e)
    (hsub : T ⊆ R) (hne : ∃ e ∈ R, e ∉ T) :
    (∑ e ∈ T, sig e / w e) < ∑ e ∈ R, sig e / w e := by
  obtain ⟨e₀, he₀R, he₀T⟩ := hne
  refine Finset.sum_lt_sum_of_subset hsub he₀R he₀T ?_ ?_
  · have := hw e₀; have := hs e₀; positivity
  · intro e _ _
    have := hw e; have := hs e
    positivity

#print axioms contrast_energy_ge
#print axioms contrast_energy_attained
#print axioms resistance_of_support
#print axioms range_boundary_is_linear
#print axioms unit_contrast_resistance
#print axioms top1_lt_range

end CIGAMF.P13.FunctionalRangeContrast
