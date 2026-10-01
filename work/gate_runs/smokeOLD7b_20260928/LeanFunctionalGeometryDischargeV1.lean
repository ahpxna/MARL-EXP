import Mathlib

/-! # Functional: discharging the geometric hypotheses of the heterogeneous instance.

`LeanFunctionalHeterogeneousInstanceV1` proves the instantiation of the
heterogeneous lower bound, but takes two geometric facts as HYPOTHESES:
`1 - D ≥ g + d/2` for an endpoint/middle pair and `1 - D ≥ g_a + g_b` for a
middle/middle pair.  Its own "what this does not establish" says so.  This file
derives both from the cell layout itself, so nothing geometric is assumed any more.

THE LAYOUT, exactly as `scripts/F2_heterogeneous_crossover_check.py` builds it:
the outsider has two endpoints at `± rho/2` with `rho = 1 - d`, and middle cells at
means `z` with `g = 1/2 - |z|`, i.e. `|z| ≤ 1/2 - g`.  `D` is the difference of the
two means of the ordered pair.

## WHAT IS PROVED

* `endpoint_middle_gap` — ordered pair (positive endpoint, middle cell `z`):
  `1 - D = (1+d)/2 + z ≥ g + d/2`, from `z ≥ -(1/2 - g)` alone.
* `middle_middle_gap` — ordered pair of middle cells: `1 - D ≥ g_a + g_b`.
* `endpoint_endpoint_gap` — the two endpoints: `1 - D = d` exactly.
* `middle_span` — and the bookkeeping fact these rest on: a middle cell with
  `g = 1/2 - |z|` satisfies `-(1/2 - g) ≤ z ≤ 1/2 - g`.

## WHAT THIS DOES NOT ESTABLISH

- Only the geometry.  The pinch algebra and the value are
  `LeanFunctionalHeterogeneousInstanceV1`; the bridge is
  `LeanFunctionalHeterogeneousLowerV1`.
- The layout is the one the probe builds; a different outsider shape needs its own
  discharge.
-/

namespace CIGAMF.P13.FunctionalGeometryDischarge

theorem middle_span (z g : ℝ) (hg : g = 1/2 - |z|) :
    -(1/2 - g) ≤ z ∧ z ≤ 1/2 - g := by
  have h : 1/2 - g = |z| := by rw [hg]; ring
  rw [h]
  exact ⟨neg_abs_le z, le_abs_self z⟩

/-- Positive endpoint against a middle cell. -/
theorem endpoint_middle_gap (d z g D : ℝ) (hg : g = 1/2 - |z|)
    (hD : D = (1 - d)/2 - z) : g + d/2 ≤ 1 - D := by
  have hz := (middle_span z g hg).1
  rw [hD]
  linarith

/-- Two middle cells, in the order that makes the gap smallest. -/
theorem middle_middle_gap (za zb ga gb D : ℝ)
    (hga : ga = 1/2 - |za|) (hgb : gb = 1/2 - |zb|)
    (hD : D = za - zb) : ga + gb ≤ 1 - D := by
  have h1 := (middle_span za ga hga).2
  have h2 := (middle_span zb gb hgb).1
  rw [hD]
  linarith

/-- The two endpoints: the gap is exactly `d`. -/
theorem endpoint_endpoint_gap (d D : ℝ) (hD : D = (1 - d)/2 - (-((1 - d)/2))) :
    1 - D = d := by
  rw [hD]; ring

#print axioms middle_span
#print axioms endpoint_middle_gap
#print axioms middle_middle_gap
#print axioms endpoint_endpoint_gap

end CIGAMF.P13.FunctionalGeometryDischarge
