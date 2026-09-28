import Mathlib

/-!
# Paper A: the region oracle's two traps

Decomposing `Alt` into regions turns the inner problem into a convex QP on each region, but
two steps are routinely got wrong and both change the answer.

**Replacing `>` by `>=` is not free.**  The true alternative set is strict, and a region's
closure may contain points the strict region does not.  What licenses the replacement is a
segment argument, and only when the region HAS a strictly bad point: if `lam` is strictly
bad and `x` is on the boundary, the segment `(1-t)x + t·lam` stays in the ordering
polyhedron (convexity), is strictly bad for every `t > 0` (the constraint is affine), and
converges to `x` (continuity).  So a lower bound valid on the strict region is valid on the
closure --- `lower_bound_transfers` --- and the two infima agree.  A region whose strict part
is EMPTY contributes nothing and must be dropped, which `empty_strict_contributes_nothing`
records.

**Zero weights degenerate the Hessian.**  A coordinate with `w_e = 0` does not appear in the
objective at all, so any formula that inverts the Hessian is inapplicable there;
`objective_indep_of_zero_weight` states the fact that breaks it, and
`zero_weight_unbounded_below_direction` shows the inner problem is genuinely unconstrained in
that coordinate.
-/

namespace CIGAMF.P13.PaperAOracleRegion

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The segment argument.**  From a strictly bad point in the region, every boundary point
is approached by strictly bad points of the region. -/
theorem exists_strict_near (P : Set E) (hP : Convex ℝ P) (g : E → ℝ)
    (hg : ∀ (a b : E) (s t : ℝ), s + t = 1 → g (s • a + t • b) = s * g a + t * g b)
    (f : E → ℝ) (hf : Continuous f)
    (x lam : E) (hx : x ∈ P) (hgx : 0 ≤ g x) (hlam : lam ∈ P) (hglam : 0 < g lam)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ y ∈ P, 0 < g y ∧ f y < f x + ε := by
  classical
  have hcont : Continuous (fun t : ℝ => f ((1 - t) • x + t • lam)) := by
    refine hf.comp ?_
    exact ((continuous_const.sub continuous_id).smul continuous_const).add
      (continuous_id.smul continuous_const)
  have htend : Filter.Tendsto (fun t : ℝ => f ((1 - t) • x + t • lam))
      (nhds 0) (nhds (f x)) := by
    have h := hcont.tendsto (0 : ℝ)
    simpa using h
  have hball : ∀ᶠ t in nhds (0 : ℝ), f ((1 - t) • x + t • lam) < f x + ε :=
    htend (Iio_mem_nhds (by linarith))
  obtain ⟨δ, hδ, hδball⟩ := Metric.eventually_nhds_iff.mp hball
  set t : ℝ := min (δ / 2) (1 / 2) with ht
  have ht0 : 0 < t := lt_min (by linarith) (by norm_num)
  have ht1 : t ≤ 1 / 2 := min_le_right _ _
  have htδ : dist t (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht0]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  refine ⟨(1 - t) • x + t • lam, ?_, ?_, hδball htδ⟩
  · exact hP hx hlam (by linarith) (le_of_lt ht0) (by ring)
  · rw [hg x lam (1 - t) t (by ring)]
    nlinarith

/-- **A lower bound valid on the strict region is valid on its closure.**  This is what makes
solving the closed QP legitimate. -/
theorem lower_bound_transfers (P : Set E) (hP : Convex ℝ P) (g : E → ℝ)
    (hg : ∀ (a b : E) (s t : ℝ), s + t = 1 → g (s • a + t • b) = s * g a + t * g b)
    (f : E → ℝ) (hf : Continuous f)
    (lam : E) (hlam : lam ∈ P) (hglam : 0 < g lam)
    (c : ℝ) (hc : ∀ y ∈ P, 0 < g y → c ≤ f y)
    (x : E) (hx : x ∈ P) (hgx : 0 ≤ g x) : c ≤ f x := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨y, hyP, hgy, hfy⟩ :=
    exists_strict_near P hP g hg f hf x lam hx hgx hlam hglam ((c - f x) / 2) (by linarith)
  have := hc y hyP hgy
  linarith

/-- **A region with no strictly bad point contributes nothing.** -/
theorem empty_strict_contributes_nothing (P : Set E) (g : E → ℝ)
    (hnone : ∀ y ∈ P, ¬ (0 < g y)) : {y | y ∈ P ∧ 0 < g y} = ∅ := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  exact fun hy => hnone y hy

/-! ## Zero weights -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The inner objective. -/
noncomputable def innerObj (w σ2 θ : ι → ℝ) (lam : ι → ℝ) : ℝ :=
  ∑ e, w e * ((θ e - lam e) ^ 2 / (2 * σ2 e))

/-- **A coordinate with zero weight does not appear in the objective.**  Any formula that
inverts the Hessian is therefore inapplicable at a design with a zero weight. -/
theorem objective_indep_of_zero_weight (w σ2 θ : ι → ℝ) (e₀ : ι) (hw : w e₀ = 0)
    (lam lam' : ι → ℝ) (hagree : ∀ e, e ≠ e₀ → lam e = lam' e) :
    innerObj w σ2 θ lam = innerObj w σ2 θ lam' := by
  classical
  unfold innerObj
  refine Finset.sum_congr rfl (fun e _ => ?_)
  by_cases he : e = e₀
  · subst he; rw [hw]; ring
  · rw [hagree e he]

/-- **And the inner problem is unconstrained in that coordinate**: moving it changes nothing,
so a strict-convexity or unique-minimiser argument fails there. -/
theorem zero_weight_unbounded_below_direction (w σ2 θ : ι → ℝ) (e₀ : ι) (hw : w e₀ = 0)
    (lam : ι → ℝ) (c : ℝ) :
    innerObj w σ2 θ (Function.update lam e₀ c) = innerObj w σ2 θ lam := by
  classical
  refine objective_indep_of_zero_weight w σ2 θ e₀ hw _ _ (fun e he => ?_)
  rw [Function.update_of_ne he]

/-! ## Audit -/

#print axioms exists_strict_near
#print axioms lower_bound_transfers
#print axioms empty_strict_contributes_nothing
#print axioms objective_indep_of_zero_weight
#print axioms zero_weight_unbounded_below_direction

end CIGAMF.P13.PaperAOracleRegion
