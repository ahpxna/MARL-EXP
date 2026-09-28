import «LeanFunctionalPairFlipCostV1»

/-! # Functional F05 steps 2-3: SHRINK by interval projection, EXPAND by opening one
ordered pair.

The oracle to be closed is

    J(w) = min_{i ∈ T, j ∉ T} inf_{z ≥ 0} [ S_i(z) + E_j(z) ],
    S_i(z) = min_l ½ ∑_a α_{i,a} · dist(θ_{i,a}, [l, l+z])²,
    E_j(z) = min_{a ≠ b} [ z − (θ_{j,a} − θ_{j,b}) ]₊² / (2(1/α_{j,a} + 1/α_{j,b})).

Its three steps are decomposition, shrink and expand.  This file proves the two
geometric steps -- the ones that say WHY those two formulas are the right ones -- and
leaves the decomposition, which is the separability statement across relation blocks, to
be assembled on top.

## WHAT IS PROVED

* `range_le_iff_exists_interval` — `range λ ≤ z` **iff** all cells lie in a common
  interval of length `z`.  This is the constraint `S_i` optimises over, stated as an
  equivalence so nothing is relaxed.
* `range_ge_iff_exists_pair_ge` — `range λ ≥ z` **iff** some ORDERED pair of cells is
  separated by at least `z`.  This is why `E_j` ranges over ordered pairs and why no
  third cell has to move.
* `clamp_mem`, `clamp_dist_le` — for a fixed interval the separable quadratic is minimised
  coordinate-wise by the CLAMP, which is the projection.  `shrink_cell_lower` is the
  per-cell consequence and `shrink_lower` sums it: every feasible point costs at least the
  projection cost.
* `shrink_attained` — the clamp is itself feasible, so `S_i(z)` is attained and the lower
  bound is exact.
* `expand_lower` — opening a pair to gap `g` costs at least
  `g₊²/(2(1/α_a + 1/α_b))`, via `pair_flip_lower`; `expand_attained` exhibits the
  minimiser, so `E_j` is exact too.

## WHAT THIS DOES NOT ESTABLISH

- The DECOMPOSITION step is not here.  That relations `i` and `j` occupy disjoint blocks
  and every other relation stays at zero cost is a statement about the model, and the
  equality `J = min_{i,j} inf_z [S_i + E_j]` is not assembled in this file.
- Free response table, known variance, positive precision.  Under realizability coupling
  the cost does not separate and none of this transfers.
- `S_i` and `E_j` are shown exact for a FIXED `z`.  The infimum over `z ≥ 0`, and the
  convexity/monotonicity in `z` that makes it a one-dimensional convex problem, are not
  proved here.
-/

namespace CIGAMF.P13.FunctionalShrinkExpand

open Finset
open CIGAMF.P13.FunctionalPairFlipCost

variable {A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]

/-- The range of a finite family. -/
noncomputable def rng (lam : A → ℝ) : ℝ :=
  (univ.sup' univ_nonempty lam) - (univ.inf' univ_nonempty lam)

/-- **Shrink, as an equivalence.**  The range is at most `z` exactly when all cells lie in
one interval of length `z`. -/
theorem range_le_iff_exists_interval (lam : A → ℝ) (z : ℝ) :
    rng lam ≤ z ↔ ∃ l : ℝ, ∀ a : A, l ≤ lam a ∧ lam a ≤ l + z := by
  constructor
  · intro h
    refine ⟨univ.inf' univ_nonempty lam, fun a => ⟨Finset.inf'_le _ (mem_univ a), ?_⟩⟩
    have hsup : lam a ≤ univ.sup' univ_nonempty lam := Finset.le_sup' _ (mem_univ a)
    unfold rng at h
    linarith
  · rintro ⟨l, hl⟩
    have hsup : univ.sup' univ_nonempty lam ≤ l + z :=
      Finset.sup'_le _ _ fun a _ => (hl a).2
    have hinf : l ≤ univ.inf' univ_nonempty lam :=
      Finset.le_inf' _ _ fun a _ => (hl a).1
    unfold rng
    linarith

/-- **Expand, as an equivalence.**  The range is at least `z` exactly when some ORDERED
pair is separated by at least `z`.  No third cell is involved. -/
theorem range_ge_iff_exists_pair_ge (lam : A → ℝ) (z : ℝ) :
    z ≤ rng lam ↔ ∃ a b : A, z ≤ lam a - lam b := by
  classical
  constructor
  · intro h
    obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup' univ_nonempty lam
    obtain ⟨b, _, hb⟩ := Finset.exists_mem_eq_inf' univ_nonempty lam
    refine ⟨a, b, ?_⟩
    unfold rng at h
    rw [ha, hb] at h
    exact h
  · rintro ⟨a, b, hab⟩
    have hsup : lam a ≤ univ.sup' univ_nonempty lam := Finset.le_sup' _ (mem_univ a)
    have hinf : univ.inf' univ_nonempty lam ≤ lam b := Finset.inf'_le _ (mem_univ b)
    unfold rng
    linarith

/-! ## The projection onto an interval. -/

/-- The clamp of `t` into `[l, l+z]`. -/
noncomputable def clamp (l z t : ℝ) : ℝ := max l (min t (l + z))

theorem clamp_mem (l z t : ℝ) (hz : 0 ≤ z) :
    l ≤ clamp l z t ∧ clamp l z t ≤ l + z := by
  unfold clamp
  constructor
  · exact le_max_left _ _
  · apply max_le (by linarith)
    exact min_le_right _ _

/-- **The clamp is the projection**: it is at least as close to `t` as any feasible
point. -/
theorem clamp_dist_le (l z t x : ℝ) (hz : 0 ≤ z) (hx1 : l ≤ x) (hx2 : x ≤ l + z) :
    |clamp l z t - t| ≤ |x - t| := by
  unfold clamp
  rcases le_or_gt t l with hlt | hgt
  · have hmin : min t (l + z) = t := min_eq_left (by linarith)
    rw [hmin, max_eq_left_iff.mpr hlt]
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ l - t),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ x - t)]
    linarith
  · rcases le_or_gt t (l + z) with hle | hgt2
    · have hmin : min t (l + z) = t := min_eq_left hle
      rw [hmin, max_eq_right_iff.mpr (le_of_lt hgt)]
      simp
    · have hmin : min t (l + z) = l + z := min_eq_right (le_of_lt hgt2)
      rw [hmin, max_eq_right_iff.mpr (by linarith)]
      rw [abs_of_nonpos (by linarith : l + z - t ≤ 0),
          abs_of_nonpos (by linarith : x - t ≤ 0)]
      linarith

/-- Per cell: the projection cost lower-bounds every feasible cost. -/
theorem shrink_cell_lower (alpha l z t x : ℝ) (halpha : 0 ≤ alpha) (hz : 0 ≤ z)
    (hx1 : l ≤ x) (hx2 : x ≤ l + z) :
    alpha * (clamp l z t - t) ^ 2 / 2 ≤ alpha * (x - t) ^ 2 / 2 := by
  have hd := clamp_dist_le l z t x hz hx1 hx2
  have hsq : (clamp l z t - t) ^ 2 ≤ (x - t) ^ 2 := by
    rw [← sq_abs (clamp l z t - t), ← sq_abs (x - t)]
    exact pow_le_pow_left₀ (abs_nonneg _) hd 2
  have := mul_le_mul_of_nonneg_left hsq halpha
  linarith

/-- **Shrink, summed.**  Every point of the interval costs at least the projection cost. -/
theorem shrink_lower (alpha th : A → ℝ) (l z : ℝ) (lam : A → ℝ)
    (halpha : ∀ a, 0 ≤ alpha a) (hz : 0 ≤ z)
    (hfeas : ∀ a, l ≤ lam a ∧ lam a ≤ l + z) :
    ∑ a, alpha a * (clamp l z (th a) - th a) ^ 2 / 2
      ≤ ∑ a, alpha a * (lam a - th a) ^ 2 / 2 :=
  Finset.sum_le_sum fun a _ =>
    shrink_cell_lower (alpha a) l z (th a) (lam a) (halpha a) hz (hfeas a).1 (hfeas a).2

/-- …and the projection is itself feasible, so the bound is attained. -/
theorem shrink_attained (th : A → ℝ) (l z : ℝ) (hz : 0 ≤ z) :
    ∀ a : A, l ≤ clamp l z (th a) ∧ clamp l z (th a) ≤ l + z :=
  fun a => clamp_mem l z (th a) hz

/-! ## Opening one ordered pair. -/

/-- **Expand, lower bound.**  Opening the pair to gap `g` costs at least
`g₊²/(2(1/α_a + 1/α_b))`, written with variances `v = 1/α_a`, `w = 1/α_b`. -/
theorem expand_lower (v w g u t : ℝ) (hv : 0 < v) (hw : 0 < w) (hg : 0 ≤ g)
    (hopen : g ≤ u + t) :
    g ^ 2 / (2 * (v + w)) ≤ energy v w u t :=
  pair_flip_lower v w g u t hv hw hg hopen

/-- …and the split `u : t = v : w` attains it, so `E_j` is exact. -/
theorem expand_attained (v w g : ℝ) (hv : 0 < v) (hw : 0 < w) :
    g * v / (v + w) + g * w / (v + w) = g ∧
      energy v w (g * v / (v + w)) (g * w / (v + w)) = g ^ 2 / (2 * (v + w)) :=
  pair_flip_attained v w g hv hw

#print axioms range_le_iff_exists_interval
#print axioms range_ge_iff_exists_pair_ge
#print axioms clamp_mem
#print axioms clamp_dist_le
#print axioms shrink_cell_lower
#print axioms shrink_lower
#print axioms shrink_attained
#print axioms expand_lower
#print axioms expand_attained

end CIGAMF.P13.FunctionalShrinkExpand
