import «LeanFunctionalCrossoverLowerV1»

/-! # The bridge, variance-weighted: heterogeneous means AND variances.

`LeanFunctionalCrossoverLowerV1.energy_ge_pairV` is the actual-alternative bridge
for the family whose outsider cells all have variance `1` and whose middle cells
all sit at `0`. This file removes both restrictions.

THE POINT, and the reason it is short: the variance enters the energy ONLY
through the PRECISION `w c / sig c`. Writing `u c = w c / sig c`,

    w c * (l c - mean c)^2 / sig c  =  u c * (l c - mean c)^2,

so the two-quadratic pinch `two_point` applies verbatim with the precisions in
place of the masses, and the whole argument of `energy_ge_pairV` carries over
with `mean` an arbitrary function instead of `meanO`. Nothing about the geometry
of the means is used except that no two of them are a full unit apart.

## What is proved

* `energyU_ge_pairV` — for an arbitrary flipping alternative on an arbitrary
  finite family of outsider cells with arbitrary means and arbitrary positive
  variances, there exist two DISTINCT cells `a ≠ b` with

      pairV wI0 wI1 (w a/sig a) (w b/sig b) (mean a - mean b)  ≤  energyU.

  The pair is the one the alternative's own flip condition hands over, so nothing
  is assumed about which cells carry the extrema.

`FlipsU` asks for two DISTINCT cells spread at least as far as the incumbent.
When the family has at least two cells this is equivalent to
`|lI1 - lI0| ≤ range`: if the range is attained at a single cell it is `0`, the
incumbent is then flat too, and any distinct pair witnesses it.

## WHAT THIS DOES NOT ESTABLISH

- This is the BRIDGE only. Instantiating it at the explicit allocation
  `u = c^2 H_n/(16 + c^2 H_n)`, `w i ∝ sig i/(g i)^2` — and hence the lower half
  of the heterogeneous crossover law — is NOT done here. That instantiation is
  verified in exact rational arithmetic on 140 configurations by
  `scripts/F2_heterogeneous_crossover_check.py`, where the value comes out
  exactly `d^2/(32 + 2 d^2 S)`; it is not a receipt.
- The hypothesis `mean a - mean b < 1` is needed and is assumed, not derived. In
  the crossover family it holds because `rho < 1` and every middle cell is
  strictly inside `(-1/2, 1/2)`; outside that region the bound is false, which is
  the same boundary the probe finds (`g0 < d/2`).
- Masses and variances are assumed strictly positive; degenerate cells are
  excluded, not handled.
- The incumbent still has exactly two cells of variance `1` and means `∓1/2`.
- Nothing here concerns an algorithm, a stopping rule, or sample complexity.
-/

namespace CIGAMF.P13.FunctionalHeterogeneousLower
open Finset
open scoped BigOperators
open CIGAMF.P13.FunctionalCrossoverLower
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Energy of an alternative: incumbent cells at `∓1/2` with variance `1`, and a
finite family of outsider cells with means `mean c`, masses `w c`, variances
`sig c`. -/
def energyU (wI0 wI1 : ℝ) (w sig mean : ι → ℝ) (lI0 lI1 : ℝ) (l : ι → ℝ) : ℝ :=
  (wI0*(lI0+1/2)^2 + wI1*(lI1-1/2)^2)/2
    + (∑ c, w c*(l c - mean c)^2/sig c)/2

/-- The alternative reverses the decision: two DISTINCT outsider cells are spread
at least as far as the incumbent. -/
def FlipsU (lI0 lI1 : ℝ) (l : ι → ℝ) : Prop :=
  ∃ a b : ι, a ≠ b ∧ |lI1 - lI0| ≤ l a - l b

/-- Precision of a cell: mass over variance. The variance enters nowhere else. -/
def prec (w sig : ι → ℝ) (c : ι) : ℝ := w c / sig c

theorem prec_pos (w sig : ι → ℝ) (hw : ∀ c, 0 < w c) (hs : ∀ c, 0 < sig c) (c : ι) :
    0 < prec w sig c := div_pos (hw c) (hs c)

/-- The outsider half, for one pair of cells, in precision form. -/
theorem outsiderU_lower (w sig mean : ι → ℝ) (hw : ∀ c, 0 < w c) (hs : ∀ c, 0 < sig c)
    (l : ι → ℝ) (a b : ι) (hab : a ≠ b) :
    prec w sig a*prec w sig b*((l a - l b) - (mean a - mean b))^2
      ≤ (∑ c, w c*(l c - mean c)^2/sig c)*(prec w sig a + prec w sig b) := by
  classical
  have hterm : ∀ c : ι, w c*(l c - mean c)^2/sig c
      = prec w sig c*(l c - mean c)^2 := by
    intro c; unfold prec; field_simp
  have hpair : prec w sig a*(l a - mean a)^2 + prec w sig b*(l b - mean b)^2
      ≤ ∑ c, w c*(l c - mean c)^2/sig c := by
    have hsub : ({a, b} : Finset ι) ⊆ univ := subset_univ _
    have hnn : ∀ c ∈ univ, c ∉ ({a, b} : Finset ι) →
        0 ≤ w c*(l c - mean c)^2/sig c := by
      intro c _ _
      exact div_nonneg (mul_nonneg (hw c).le (sq_nonneg _)) (hs c).le
    have h := Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
    rw [Finset.sum_pair hab, hterm a, hterm b] at h
    exact h
  have h2 := two_point (prec w sig a) (prec w sig b)
    (l a - mean a) (l b - mean b)
    (prec_pos w sig hw hs a).le (prec_pos w sig hw hs b).le
  have he : (l a - mean a) - (l b - mean b)
      = (l a - l b) - (mean a - mean b) := by ring
  rw [he] at h2
  refine h2.trans (mul_le_mul_of_nonneg_right hpair ?_)
  have := prec_pos w sig hw hs a; have := prec_pos w sig hw hs b; linarith

/-- THE BRIDGE, variance-weighted. Every flipping alternative — arbitrary means,
arbitrary positive variances, extrema anywhere — costs at least the pinch value
of some pair of outsider cells. -/
theorem energyU_ge_pairV (wI0 wI1 : ℝ) (hI0 : 0 < wI0) (hI1 : 0 < wI1)
    (w sig mean : ι → ℝ) (hw : ∀ c, 0 < w c) (hs : ∀ c, 0 < sig c)
    (hD : ∀ a b : ι, mean a - mean b < 1)
    (lI0 lI1 : ℝ) (l : ι → ℝ) (hflip : FlipsU lI0 lI1 l) :
    ∃ a b : ι, a ≠ b ∧
      pairV wI0 wI1 (prec w sig a) (prec w sig b) (mean a - mean b)
        ≤ energyU wI0 wI1 w sig mean lI0 lI1 l := by
  classical
  obtain ⟨a, b, hab, hle⟩ := hflip
  refine ⟨a, b, hab, ?_⟩
  set z : ℝ := l a - l b with hz
  set D : ℝ := mean a - mean b with hD'
  set A : ℝ := wI0*wI1/(2*(wI0+wI1)) with hA
  set B : ℝ := prec w sig a*prec w sig b/(2*(prec w sig a + prec w sig b)) with hB
  have hpa := prec_pos w sig hw hs a
  have hpb := prec_pos w sig hw hs b
  have hIsum : (0:ℝ) < wI0 + wI1 := by linarith
  have hOsum : (0:ℝ) < prec w sig a + prec w sig b := by linarith
  have hApos : 0 < A := by rw [hA]; exact div_pos (mul_pos hI0 hI1) (by linarith)
  have hBpos : 0 < B := by rw [hB]; exact div_pos (mul_pos hpa hpb) (by linarith)
  have hDlt : D < 1 := by rw [hD']; exact hD a b
  set SI : ℝ := wI0*(lI0+1/2)^2 + wI1*(lI1-1/2)^2 with hSI
  set SO : ℝ := ∑ c, w c*(l c - mean c)^2/sig c with hSO
  have hE : energyU wI0 wI1 w sig mean lI0 lI1 l = SI/2 + SO/2 := by
    unfold energyU; rw [hSI, hSO]
  have hIlow : A*(1-(lI1-lI0))^2 ≤ SI/2 := by
    have h := incumbent_lower wI0 wI1 lI0 lI1 hI0.le hI1.le
    rw [hA, hSI, div_mul_eq_mul_div,
      div_le_iff₀ (by linarith : (0:ℝ) < 2*(wI0+wI1))]
    have hring : (wI0*(lI0+1/2)^2 + wI1*(lI1-1/2)^2)/2 * (2*(wI0+wI1))
        = (wI0*(lI0+1/2)^2 + wI1*(lI1-1/2)^2)*(wI0+wI1) := by ring
    rw [hring]; exact h
  have hOlow : B*(z-D)^2 ≤ SO/2 := by
    have h := outsiderU_lower w sig mean hw hs l a b hab
    rw [hB, hSO, hz, hD', div_mul_eq_mul_div,
      div_le_iff₀ (by linarith : (0:ℝ) < 2*(prec w sig a + prec w sig b))]
    have hring : (∑ c, w c*(l c - mean c)^2/sig c)/2
          * (2*(prec w sig a + prec w sig b))
        = (∑ c, w c*(l c - mean c)^2/sig c)*(prec w sig a + prec w sig b) := by ring
    rw [hring]; exact h
  have hSOnn : 0 ≤ SO := by
    rw [hSO]
    exact Finset.sum_nonneg (fun c _ =>
      div_nonneg (mul_nonneg (hw c).le (sq_nonneg _)) (hs c).le)
  have hSInn : 0 ≤ SI := by
    rw [hSI]
    have h1 : 0 ≤ wI0*(lI0+1/2)^2 := mul_nonneg hI0.le (sq_nonneg _)
    have h2 : 0 ≤ wI1*(lI1-1/2)^2 := mul_nonneg hI1.le (sq_nonneg _)
    linarith
  have hABpos : (0:ℝ) < A + B := by linarith
  have hpv : pairV wI0 wI1 (prec w sig a) (prec w sig b) D = A*B*(1-D)^2/(A+B) := by
    rw [hA, hB]; exact pairV_eq wI0 wI1 _ _ D hI0 hI1 hpa hpb
  rw [hpv, hE, div_le_iff₀ hABpos]
  by_cases hz1 : z < 1
  · have ht : lI1 - lI0 ≤ z := (le_abs_self _).trans hle
    have hstep : A*(1-z)^2 ≤ A*(1-(lI1-lI0))^2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ 1-z) (by linarith) 2) hApos.le
    have hsum : A*(1-z)^2 + B*(z-D)^2 ≤ SI/2 + SO/2 := by linarith
    have hp := pinch A B (1-z) (z-D) hApos.le hBpos.le
    have heq : (1-z) + (z-D) = 1 - D := by ring
    rw [heq] at hp
    exact hp.trans (mul_le_mul_of_nonneg_right hsum hABpos.le)
  · push_neg at hz1
    have hDpos : 0 < 1 - D := by linarith
    have hsq : (1-D)^2 ≤ (z-D)^2 :=
      pow_le_pow_left₀ hDpos.le (by linarith : 1 - D ≤ z - D) 2
    have hBD : B*(1-D)^2 ≤ SO/2 :=
      (mul_le_mul_of_nonneg_left hsq hBpos.le).trans hOlow
    have h1 : A*(B*(1-D)^2) ≤ A*(SO/2) := mul_le_mul_of_nonneg_left hBD hApos.le
    have h2 : A*(SO/2) ≤ (SI/2 + SO/2)*(A+B) := by
      have e1 : 0 ≤ SI*(A+B) := mul_nonneg hSInn hABpos.le
      have e2 : 0 ≤ SO*B := mul_nonneg hSOnn hBpos.le
      nlinarith [e1, e2]
    calc A*B*(1-D)^2 = A*(B*(1-D)^2) := by ring
      _ ≤ A*(SO/2) := h1
      _ ≤ (SI/2 + SO/2)*(A+B) := h2

#print axioms prec_pos
#print axioms outsiderU_lower
#print axioms energyU_ge_pairV

end
end CIGAMF.P13.FunctionalHeterogeneousLower
