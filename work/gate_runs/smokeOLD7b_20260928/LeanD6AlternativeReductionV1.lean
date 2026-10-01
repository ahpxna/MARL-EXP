import Mathlib

/-! # D6: making the CONTINUOUS alternative family a finite check, and turning a grid
into a certified statement.

Two audit items.

 D5  `sup_err_grid` is a supremum over a GRID.  A sign change between adjacent grid
     points does not by itself give a boundary, and no sign change on the grid does not
     rule one out.  What repairs this is a MODULUS: with a Lipschitz constant on the
     cell, either the cell provably contains no zero, or a sign change brackets one.

 D6/4 The alternative family is `(d, x)` with `d` ranging over finitely many integers
     and `x` over an INTERVAL.  The information is exactly quadratic in `x`
     (`P18` certifies the coefficients), so the infimum over the interval is pinned by
     the vertex and the two endpoints -- a finite check, not a search.

## WHAT IS PROVED

* `quadratic_ge_vertex` — the vertex value is the global minimum of `ax² + bx + c`
  when `a > 0`.
* `quadratic_inf_Icc` — hence `min(f(lo), f(hi), f(vertex))` is a valid LOWER bound for
  the infimum over `[lo, hi]`, whether or not the vertex is inside.
* `quadratic_inf_attained` — and when the vertex IS inside, that minimum is attained,
  so the finite check is exact.
* `quadratic_inf_endpoint_left/right` — when the vertex is outside, the quadratic is
  monotone on the interval and the relevant endpoint is the minimiser.
* `no_crossing_of_modulus` — **`f` stays positive on a cell** when it is `m` positive at
  the left end and the Lipschitz travel `Λ(t₁-t₀)` is below `m`.  This is what a grid
  needs to say anything between its points.
* `crossing_bracket` — a sign change on a cell brackets a zero (intermediate value).

## WHAT THIS DOES NOT ESTABLISH

- No Lipschitz constant is computed here; `Λ` is an input.  Computing it for the D6
  slack is `scripts/P24_d6_boundary_modulus.py`.
- No phase boundary is claimed: what these give is EITHER "no crossing in this cell" OR
  "a crossing bracketed in this cell", cell by cell.
- The reduction to a finite check is about `x`; `d` is already finite.
-/

namespace CIGAMF.P13.D6AlternativeReduction

/-- The vertex is the global minimum of an upward parabola. -/
theorem quadratic_ge_vertex (a b c x : ℝ) (ha : 0 < a) :
    a * (-b / (2 * a)) ^ 2 + b * (-b / (2 * a)) + c ≤ a * x ^ 2 + b * x + c := by
  have hane : a ≠ 0 := ne_of_gt ha
  have hkey : 0 ≤ a * (x + b / (2 * a)) ^ 2 := by positivity
  have hexp : a * x ^ 2 + b * x + c
      - (a * (-b / (2 * a)) ^ 2 + b * (-b / (2 * a)) + c)
      = a * (x + b / (2 * a)) ^ 2 := by
    field_simp
    ring
  linarith [hexp ▸ hkey]

/-- So the three-point minimum is a valid LOWER bound for the infimum over `[lo, hi]`,
whether or not the vertex lies inside. -/
theorem quadratic_inf_Icc (a b c lo hi x : ℝ) (ha : 0 < a)
    (hx1 : lo ≤ x) (hx2 : x ≤ hi) :
    min (min (a * lo ^ 2 + b * lo + c) (a * hi ^ 2 + b * hi + c))
        (a * (-b / (2 * a)) ^ 2 + b * (-b / (2 * a)) + c)
      ≤ a * x ^ 2 + b * x + c :=
  le_trans (min_le_right _ _) (quadratic_ge_vertex a b c x ha)

/-- …and when the vertex is inside, the minimum is ATTAINED there, so the finite check
is exact. -/
theorem quadratic_inf_attained (a b c lo hi : ℝ) (ha : 0 < a)
    (hv1 : lo ≤ -b / (2 * a)) (hv2 : -b / (2 * a) ≤ hi) :
    (∀ x, lo ≤ x → x ≤ hi →
        a * (-b / (2 * a)) ^ 2 + b * (-b / (2 * a)) + c ≤ a * x ^ 2 + b * x + c)
    ∧ lo ≤ -b / (2 * a) ∧ -b / (2 * a) ≤ hi :=
  ⟨fun x _ _ => quadratic_ge_vertex a b c x ha, hv1, hv2⟩

/-- Vertex to the LEFT of the interval: the left endpoint is the minimiser. -/
theorem quadratic_inf_endpoint_left (a b c lo hi x : ℝ) (ha : 0 < a)
    (hv : -b / (2 * a) ≤ lo) (hx1 : lo ≤ x) (hx2 : x ≤ hi) :
    a * lo ^ 2 + b * lo + c ≤ a * x ^ 2 + b * x + c := by
  have hane : a ≠ 0 := ne_of_gt ha
  have hb : -b ≤ 2 * a * lo := by
    rw [div_le_iff₀ (by linarith)] at hv
    linarith
  nlinarith [sq_nonneg (x - lo), ha, hx1]

/-- Vertex to the RIGHT of the interval: the right endpoint is the minimiser. -/
theorem quadratic_inf_endpoint_right (a b c lo hi x : ℝ) (ha : 0 < a)
    (hv : hi ≤ -b / (2 * a)) (hx1 : lo ≤ x) (hx2 : x ≤ hi) :
    a * hi ^ 2 + b * hi + c ≤ a * x ^ 2 + b * x + c := by
  have hane : a ≠ 0 := ne_of_gt ha
  have hb : 2 * a * hi ≤ -b := by
    rw [le_div_iff₀ (by linarith)] at hv
    linarith
  nlinarith [sq_nonneg (x - hi), ha, hx2]

/-- **The modulus.**  If `f` is `m` positive at the left end of a cell and the Lipschitz
travel across the cell is below `m`, then `f` is positive THROUGHOUT the cell -- so the
grid has said something about the points between its nodes. -/
theorem no_crossing_of_modulus (f : ℝ → ℝ) (t0 t1 Lip m : ℝ) (ht : t0 ≤ t1)
    (hLip : 0 ≤ Lip)
    (hlip : ∀ s ∈ Set.Icc t0 t1, |f s - f t0| ≤ Lip * (s - t0))
    (hm : m ≤ f t0) (hpos : 0 < m) (hgap : Lip * (t1 - t0) < m) :
    ∀ t ∈ Set.Icc t0 t1, 0 < f t := by
  intro t htmem
  obtain ⟨h1, h2⟩ := htmem
  have hb := hlip t ⟨h1, h2⟩
  have hb' : f t0 - f t ≤ Lip * (t - t0) := by
    have := (abs_le.1 hb).1
    linarith
  have htravel : Lip * (t - t0) ≤ Lip * (t1 - t0) :=
    mul_le_mul_of_nonneg_left (by linarith) hLip
  linarith

/-- A sign change on a cell brackets a zero. -/
theorem crossing_bracket (f : ℝ → ℝ) (t0 t1 : ℝ) (ht : t0 ≤ t1)
    (hc : ContinuousOn f (Set.Icc t0 t1)) (h0 : f t0 ≤ 0) (h1 : 0 ≤ f t1) :
    ∃ t ∈ Set.Icc t0 t1, f t = 0 := by
  have := intermediate_value_Icc ht hc
  have hmem : (0:ℝ) ∈ Set.Icc (f t0) (f t1) := ⟨h0, h1⟩
  obtain ⟨t, htmem, htval⟩ := this hmem
  exact ⟨t, htmem, htval⟩

#print axioms quadratic_ge_vertex
#print axioms quadratic_inf_Icc
#print axioms quadratic_inf_attained
#print axioms quadratic_inf_endpoint_left
#print axioms quadratic_inf_endpoint_right
#print axioms no_crossing_of_modulus
#print axioms crossing_bracket

end CIGAMF.P13.D6AlternativeReduction
