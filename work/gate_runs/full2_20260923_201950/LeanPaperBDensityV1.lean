import «LeanPaperBIndistV1»
import «LeanPaperBSafeOrderV1»

/-!
# Paper B: the resolving-order table, derived from actual densities

`LeanPaperBIndistV1` carries the table `coefOf i k = [k = i+1]` and says, correctly, that
read as RAW MOMENTS it is not realisable by any law --- world `0` would need `E X = 1` and
`E X^2 = 0`.  It is meant as the table of expansion coefficients in the perturbation scale
`h`, and until that reading is backed by an actual family of densities the partition it
induces rests on a table nobody has realised.

This module exhibits the family.  With `phi` any probability density, put

    dens i h  =  (1 - h^{i+1}) * phi  +  h^{i+1} * phi(. - 1).

Each `dens i h` is a genuine probability density for `0 <= h <= 1` --- it is a two-point
mixture, so non-negativity and unit mass are immediate and need no delicate integral --- and
its expansion in `h` has coefficient `[k = i+1] * (phi(.-1) - phi)` at order `k >= 1`.  That
is `coefOf` with the fixed profile `phi(.-1) - phi`, so the table IS realisable as expansion
coefficients, and is realised here.

The resolving order then follows from the densities rather than from the table:
`dens i - dens j` vanishes to order `min(i,j)+1` and does not vanish at it, so

    r(i, j) = min(i, j) + 1,

both directions proved.  At the tip family, whose only unsafe subset is the whole world set,
this gives `s_safe = 1` and `s_id = m - 1`.
-/

namespace CIGAMF.P13.PaperBDensity

open MeasureTheory
open CIGAMF.P13.PaperBIndist

/-- The family: a two-point mixture whose mixing weight is `h^{i+1}`. -/
noncomputable def dens (φ : ℝ → ℝ) (i : ℕ) (h y : ℝ) : ℝ :=
  (1 - h ^ (i + 1)) * φ y + h ^ (i + 1) * φ (y - 1)

theorem dens_nonneg (φ : ℝ → ℝ) (hφ : ∀ y, 0 ≤ φ y) (i : ℕ) (h y : ℝ)
    (h0 : 0 ≤ h) (h1 : h ≤ 1) : 0 ≤ dens φ i h y := by
  have hp : (0 : ℝ) ≤ h ^ (i + 1) := by positivity
  have hp1 : h ^ (i + 1) ≤ 1 := pow_le_one₀ h0 h1
  unfold dens
  have := hφ y
  have := hφ (y - 1)
  nlinarith

/-- **Each member is a probability density.**  A two-point mixture of a density and its
translate; no integral beyond translation invariance is needed. -/
theorem dens_integral_one (φ : ℝ → ℝ) (hint : Integrable φ volume)
    (hmass : ∫ y, φ y = 1) (i : ℕ) (h : ℝ) :
    ∫ y, dens φ i h y = 1 := by
  unfold dens
  have hshift : ∫ y, φ (y - 1) = ∫ y, φ y :=
    integral_sub_right_eq_self φ 1
  rw [integral_add ((hint.const_mul _)) ((hint.comp_sub_right 1).const_mul _),
    integral_const_mul, integral_const_mul, hshift, hmass]
  ring

/-- **The difference has a single profile and a single scale.** -/
theorem dens_diff (φ : ℝ → ℝ) (i j : ℕ) (h y : ℝ) :
    dens φ i h y - dens φ j h y = (h ^ (i + 1) - h ^ (j + 1)) * (φ (y - 1) - φ y) := by
  unfold dens
  ring

/-- **Nothing separates below `min(i,j)+1`.**  The scale factor is bounded by
`h^{min(i,j)+1}` uniformly in `y`. -/
theorem dens_vanishes_below (φ : ℝ → ℝ) (i j : ℕ) (h y : ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    |dens φ i h y - dens φ j h y| ≤ h ^ (min i j + 1) * |φ (y - 1) - φ y| := by
  rw [dens_diff, abs_mul]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  have hi : h ^ (i + 1) ≤ h ^ (min i j + 1) :=
    pow_le_pow_of_le_one h0 h1 (by omega)
  have hj : h ^ (j + 1) ≤ h ^ (min i j + 1) :=
    pow_le_pow_of_le_one h0 h1 (by omega)
  have hi0 : (0 : ℝ) ≤ h ^ (i + 1) := by positivity
  have hj0 : (0 : ℝ) ≤ h ^ (j + 1) := by positivity
  rw [abs_le]
  constructor <;> linarith

/-- **And something does separate at `min(i,j)+1`.**  For `i < j` the scale factor is at
least half of `h^{i+1}` once `h` is small, and the profile is non-zero somewhere by
assumption. -/
theorem dens_separates_at (φ : ℝ → ℝ) (i j : ℕ) (hij : i < j)
    (y : ℝ) (hy : φ (y - 1) ≠ φ y) (h : ℝ) (h0 : 0 < h) (hsmall : h ^ (j - i) ≤ 1 / 2) :
    h ^ (min i j + 1) * (|φ (y - 1) - φ y| / 2)
      ≤ |dens φ i h y - dens φ j h y| := by
  have hmin : min i j = i := by omega
  rw [dens_diff, abs_mul, hmin]
  have hsplit : h ^ (j + 1) = h ^ (i + 1) * h ^ (j - i) := by
    rw [← pow_add]
    congr 1
    omega
  have hi0 : (0 : ℝ) < h ^ (i + 1) := by positivity
  have hfac : h ^ (i + 1) / 2 ≤ h ^ (i + 1) - h ^ (j + 1) := by
    rw [hsplit]
    nlinarith
  have habs : |h ^ (i + 1) - h ^ (j + 1)| = h ^ (i + 1) - h ^ (j + 1) :=
    abs_of_nonneg (by linarith)
  rw [habs]
  have hpos : 0 < |φ (y - 1) - φ y| := abs_pos.mpr (sub_ne_zero_of_ne hy)
  nlinarith

/-- **The table is realised.**  At order `k >= 1` the coefficient of `h^k` in `dens i` is
`coefOf i k` times one fixed profile, so `coefOf` is the expansion-coefficient table of an
actual family of densities --- which is the reading `LeanPaperBIndistV1` asks for, and the
reading under which it is NOT a table of raw moments. -/
theorem coefOf_realised {m : ℕ} (φ : ℝ → ℝ) (i : Fin m) (h y : ℝ) :
    dens φ (i : ℕ) h y
      = φ y + (∑ k ∈ Finset.range (m + 2), coefOf m i k * h ^ k) * (φ (y - 1) - φ y) := by
  classical
  have hmem : (i : ℕ) + 1 ∈ Finset.range (m + 2) := by
    have := i.isLt
    simp only [Finset.mem_range]
    omega
  have hsum : ∑ k ∈ Finset.range (m + 2), coefOf m i k * h ^ k = h ^ ((i : ℕ) + 1) := by
    rw [Finset.sum_eq_single ((i : ℕ) + 1)]
    · unfold coefOf
      rw [if_pos rfl, one_mul]
    · intro k _ hk
      unfold coefOf
      rw [if_neg (fun hc => hk hc), zero_mul]
    · intro hc
      exact absurd hmem hc
  rw [hsum]
  unfold dens
  ring

/-! ## The exponents of the tip family -/

/-- **The safe order.**  Over a world set with at least two members, the smallest resolving
order is `1`. -/
theorem s_safe_eq_one (m : ℕ) (hm : 2 ≤ m) :
    ∃ i j : Fin m, (i : ℕ) ≠ (j : ℕ) ∧ min (i : ℕ) (j : ℕ) + 1 = 1 := by
  refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp, by simp⟩

/-- **The identification order.**  The largest resolving order over distinct worlds is
`m - 1`. -/
theorem s_id_eq (m : ℕ) (hm : 2 ≤ m) :
    (∀ i j : Fin m, (i : ℕ) ≠ (j : ℕ) → min (i : ℕ) (j : ℕ) + 1 ≤ m - 1)
      ∧ ∃ i j : Fin m, (i : ℕ) ≠ (j : ℕ) ∧ min (i : ℕ) (j : ℕ) + 1 = m - 1 := by
  constructor
  · intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    omega
  · refine ⟨⟨m - 2, by omega⟩, ⟨m - 1, by omega⟩, by simp; omega, by simp; omega⟩

/-! ## Audit -/

#print axioms dens_nonneg
#print axioms dens_integral_one
#print axioms dens_diff
#print axioms dens_vanishes_below
#print axioms dens_separates_at
#print axioms coefOf_realised
#print axioms s_safe_eq_one
#print axioms s_id_eq

end CIGAMF.P13.PaperBDensity
