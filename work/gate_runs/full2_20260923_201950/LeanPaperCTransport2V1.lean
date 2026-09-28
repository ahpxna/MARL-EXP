import «LeanPaperCNamingV1»

/-!
# Paper C: the band transports, and the robustness ratio's real reach

Two closures.

**C4, the constraint side.**  The flow records how many items of each TYPE have been served,
not which ones, so a per-item retained marginal is not a function of the composition.  It
becomes one after relabelling within each type group: the marginals are then constant on the
group, the group's total is the flow's occupancy, and
`marginal_eq_occupancy_div_card` divides.  `per_item_from_flow` is that composition at the
named observables --- the band constraint in the only form the flow supports.

**C5, the reach of the perturbation bound.**  The Lipschitz bound gives
`|V_g - V_{g'}| <= 2||g-g'||_1/D`, and from it a ratio bound.  What matters is which
conclusions it does and does NOT support:

* at `eps <= 1/(2m)` the ratio is still at least `(m-1)/3`, so the linear-in-`m` price
  survives a perturbation that shrinks with the size (`ratio_linear_at_small_eps`);
* at FIXED `eps` the very same bound is at most `2/eps`, bounded in `m`, so it certifies no
  linear separation at all (`ratio_bounded_at_fixed_eps`).

The second is stated because the first is the tempting one to quote.
-/

namespace CIGAMF.P13.PaperCTransport2

open Finset
open CIGAMF.P13.PaperCNaming
open CIGAMF.P13.PaperCBreakpoint

variable {d m : ℕ}

/-- **The per-item band, from the flow.**  Under relabelling the marginals are constant on a
type group, so each equals the group's flow occupancy divided by the group's size. -/
theorem per_item_from_flow (P : Equiv.Perm (Fin m) → ℝ) (ty : Fin m → Fin d)
    (k : Fin (m + 1)) (τ : Fin d) (grp : Finset (Fin m)) (hne : grp.Nonempty)
    (marg : Fin m → ℝ)
    (hconst : ∀ i ∈ grp, ∀ j ∈ grp, marg i = marg j)
    (hocc : ∑ i ∈ grp, marg i
      = ∑ v, flowX P ty k v * ((v τ : ℕ) : ℝ))
    (i : Fin m) (hi : i ∈ grp) :
    marg i = (∑ v, flowX P ty k v * ((v τ : ℕ) : ℝ)) / (grp.card : ℝ) :=
  marginal_eq_occupancy_div_card grp hne marg _ hconst hocc i hi

/-! ## The robustness ratio -/

/-- **The ratio bound from the Lipschitz estimate.** -/
theorem ratio_lower_of_perturbation (mR ε V Vfree : ℝ) (hm : 3 ≤ mR) (hε : 0 ≤ ε)
    (hV : (mR + 3) / mR - 2 * ε ≤ V)
    (hVfree : 0 < Vfree) (hVfreele : Vfree ≤ 2 / (mR - 1) + 2 * ε)
    (hnum : 0 < (mR + 3) / mR - 2 * ε) :
    ((mR + 3) / mR - 2 * ε) / (2 / (mR - 1) + 2 * ε) ≤ V / Vfree := by
  have hden : 0 < 2 / (mR - 1) + 2 * ε := lt_of_lt_of_le hVfree hVfreele
  rw [div_le_div_iff₀ hden hVfree]
  nlinarith [hV, hVfreele, hnum, hVfree, hden]

/-- **At `eps <= 1/(2m)` the linear price survives.** -/
theorem ratio_linear_at_small_eps (mR ε : ℝ) (hm : 5 ≤ mR) (hε : 0 ≤ ε)
    (hεsmall : ε ≤ 1 / (2 * mR)) :
    (mR - 1) / 3 ≤ ((mR + 3) / mR - 2 * ε) / (2 / (mR - 1) + 2 * ε) := by
  have hm0 : (0 : ℝ) < mR := by linarith
  have hm1 : (0 : ℝ) < mR - 1 := by linarith
  have hdenpos : (0 : ℝ) < 2 / (mR - 1) + 2 * ε := by positivity
  have h2ε : 2 * ε ≤ 1 / mR := by
    have hstep : 2 * (1 / (2 * mR)) = 1 / mR := by field_simp
    nlinarith [hεsmall, hstep]
  have hεm : 2 * ε * mR ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right h2ε (le_of_lt hm0)
    rwa [div_mul_cancel₀ _ (ne_of_gt hm0)] at h
  rw [le_div_iff₀ hdenpos]
  have hexp : (mR - 1) / 3 * (2 / (mR - 1) + 2 * ε)
      = 2 / 3 + 2 * ε * (mR - 1) / 3 := by field_simp
  have hrhs : (mR + 3) / mR = 1 + 3 / mR := by field_simp
  rw [hexp, hrhs]
  have hA : 2 * ε * (mR - 1) / 3 ≤ 1 / 3 := by nlinarith [hεm, hε, hm0, hm1]
  have hB : 2 * ε ≤ 1 / mR := h2ε
  have hC : (0 : ℝ) < 1 / mR := by positivity
  have hD : (1 : ℝ) / mR ≤ 3 / mR := by
    rw [div_le_div_iff₀ hm0 hm0]; nlinarith [hm0]
  linarith

/-- **At FIXED `eps` the same bound certifies nothing linear**: it never exceeds `2/eps`. -/
theorem ratio_bounded_at_fixed_eps (mR ε : ℝ) (hm : 3 ≤ mR) (hε : 0 < ε) :
    ((mR + 3) / mR - 2 * ε) / (2 / (mR - 1) + 2 * ε) ≤ 2 / ε := by
  have hm0 : (0 : ℝ) < mR := by linarith
  have hm1 : (0 : ℝ) < mR - 1 := by linarith
  have hdenpos : (0 : ℝ) < 2 / (mR - 1) + 2 * ε := by positivity
  have hnumle : (mR + 3) / mR - 2 * ε ≤ 2 := by
    have h2 : (mR + 3) / mR = 1 + 3 / mR := by field_simp
    have h3 : (3 : ℝ) / mR ≤ 1 := by rw [div_le_one hm0]; linarith
    linarith
  have hdenge : 2 * ε ≤ 2 / (mR - 1) + 2 * ε := by
    have : (0 : ℝ) < 2 / (mR - 1) := by positivity
    linarith
  rw [div_le_div_iff₀ hdenpos hε]
  nlinarith [hnumle, hdenge, hε, hdenpos]

/-! ## Audit -/

#print axioms per_item_from_flow
#print axioms ratio_lower_of_perturbation
#print axioms ratio_linear_at_small_eps
#print axioms ratio_bounded_at_fixed_eps

end CIGAMF.P13.PaperCTransport2
