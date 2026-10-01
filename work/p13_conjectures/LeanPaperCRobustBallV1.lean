import «LeanPaperCCollapseWindowV1»

/-!
# Paper C: the price that survives every perturbation of a given size

For odd `m = 2s + 3` and `ε > 0` let
```
R_m(ε) = inf { V(g';0) / V(g';m) : ‖g_m - g'‖₁ ≤ ε, V(g';m) > 0 },
```
the worst price ratio over the whole `ℓ₁` ball around the family, among perturbations whose free
value stays positive (`robustPrice`). This is the guarantee a designer keeps without knowing
which perturbation occurred.

* `robust_lower`: `R_m(ε) ≥ min(m - 1, 1/ε)/16` for `0 < ε ≤ 1/6`.
  - Below `1/(2m)`, every member keeps `(m-1)/4` (`physical_price_linear`).
  - Above it, every member keeps `min(m-1, 1/d)/16` at its own size `d ≤ ε` (`collapse_all`).
* `robust_upper`: `R_m(ε) ≤ min((m+3)(m-1)/(2m), 10/ε)`, for `0 < ε ≤ 1`, from two members of
  the ball: `g_m` itself (`trueValue_family`, `odd_zero_value`, `odd_free_value`) and the
  one-item witness `gD s ε` (`collapse_upper`).
* `robust_ball`: both sides, and `min((m+3)(m-1)/(2m), 10/ε) ≤ 10 min(m-1, 1/ε)`, so
  `R_m(ε) = Θ(min(m, 1/ε))` with explicit constants `1/16` and `10`.

No minimiser is assumed to exist: the statements are about the infimum.
-/

namespace CIGAMF.P13.PaperCRobustBall

open Finset
open CIGAMF.P13.PaperCRanking CIGAMF.P13.PaperCInstantiation CIGAMF.P13.PaperCFamily
open CIGAMF.P13.PaperCEndpoint CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCFrontier
open CIGAMF.P13.PaperCStabilityEndgame CIGAMF.P13.PaperCEndgame CIGAMF.P13.PaperCEndpointLaw
open CIGAMF.P13.PaperCStabilityFamily CIGAMF.P13.PaperCRelaxedJoin CIGAMF.P13.PaperCRatioJoin
open CIGAMF.P13.PaperCLawPush CIGAMF.P13.PaperCBaselineAttain CIGAMF.P13.PaperCCollapseScale
open CIGAMF.P13.PaperCCollapseWindow

/-- The price ratio of a weight vector `g'` for size `2s + 3`. -/
noncomputable def priceRatio (s : ℕ) (g' : Fin (2 * s + 3) → ℝ) : ℝ :=
  trueValue g' 0 (interiorK (2 * s + 3)) (interiorK_nonempty _ (by omega))
    / trueValue g' ((2 * s + 3 : ℕ) : ℝ) (interiorK (2 * s + 3)) (interiorK_nonempty _ (by omega))

/-- The price ratios over the `ℓ₁` ball of radius `ε`, among perturbations with positive free
value. -/
def ratioSet (s : ℕ) (ε : ℝ) : Set ℝ :=
  {r | ∃ g' : Fin (2 * s + 3) → ℝ, l1 (gFamily (2 * s + 3)) g' ≤ ε
    ∧ 0 < trueValue g' ((2 * s + 3 : ℕ) : ℝ) (interiorK (2 * s + 3))
        (interiorK_nonempty _ (by omega))
    ∧ r = priceRatio s g'}

/-- **The robust price**: the infimum of the price ratio over the ball. -/
noncomputable def robustPrice (s : ℕ) (ε : ℝ) : ℝ := sInf (ratioSet s ε)

/-- The family's free value is positive. -/
theorem family_free_pos (s : ℕ) :
    0 < trueValue (gFamily (2 * s + 3)) ((2 * s + 3 : ℕ) : ℝ) (interiorK (2 * s + 3))
      (interiorK_nonempty _ (by omega)) := by
  rw [trueValue_family (2 * s + 3) (by omega),
    odd_free_value (2 * s + 3) (by omega) (by omega) _ (by
      have : (1 : ℝ) ≤ ((2 * s + 3 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ 2 * s + 3 by omega)
      exact this)]
  unfold freeValue denom
  have : (3 : ℝ) ≤ ((2 * s + 3 : ℕ) : ℝ) := by exact_mod_cast (show 3 ≤ 2 * s + 3 by omega)
  apply div_pos (by norm_num)
  apply mul_pos <;> linarith

/-- The family's own price ratio, `(m+3)(m-1)/(2m)`. -/
theorem family_price (s : ℕ) :
    priceRatio s (gFamily (2 * s + 3))
      = (((2 * s + 3 : ℕ) : ℝ) + 3) * (((2 * s + 3 : ℕ) : ℝ) - 1)
        / (2 * ((2 * s + 3 : ℕ) : ℝ)) := by
  unfold priceRatio
  rw [trueValue_family (2 * s + 3) (by omega), trueValue_family (2 * s + 3) (by omega),
    odd_zero_value (2 * s + 3) (by omega) (by omega),
    odd_free_value (2 * s + 3) (by omega) (by omega) _ (by
      have : (1 : ℝ) ≤ ((2 * s + 3 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ 2 * s + 3 by omega)
      exact this)]
  unfold freeValue denom
  have h3 : (3 : ℝ) ≤ ((2 * s + 3 : ℕ) : ℝ) := by exact_mod_cast (show 3 ≤ 2 * s + 3 by omega)
  have h1 : ((2 * s + 3 : ℕ) : ℝ) - 1 ≠ 0 := by linarith
  have h2 : ((2 * s + 3 : ℕ) : ℝ) ≠ 0 := by linarith
  have h4 : ((2 * s + 3 : ℕ) : ℝ) + 4 ≠ 0 := by linarith
  field_simp

theorem family_mem (s : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    priceRatio s (gFamily (2 * s + 3)) ∈ ratioSet s ε := by
  refine ⟨gFamily (2 * s + 3), ?_, family_free_pos s, rfl⟩
  have : l1 (gFamily (2 * s + 3)) (gFamily (2 * s + 3)) = 0 := by simp [l1]
  rw [this]; exact hε

theorem witness_mem (s : ℕ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    priceRatio s (gD s ε) ∈ ratioSet s ε := by
  obtain ⟨hl1, hpos, -⟩ := collapse_upper s ε hε0 hε1
  exact ⟨gD s ε, hl1.le, hpos, rfl⟩

/-- **Every member of the ball keeps the lower bound.** -/
theorem member_lower (s : ℕ) (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 6) (r : ℝ)
    (hr : r ∈ ratioSet s ε) :
    min ((((2 * s + 3 : ℕ) : ℝ)) - 1) (1 / ε) / 16 ≤ r := by
  obtain ⟨g', hl1, hpos, rfl⟩ := hr
  have hm3 : (3 : ℝ) ≤ ((2 * s + 3 : ℕ) : ℝ) := by exact_mod_cast (show 3 ≤ 2 * s + 3 by omega)
  by_cases hsmall : l1 (gFamily (2 * s + 3)) g' ≤ 1 / (2 * ((2 * s + 3 : ℕ) : ℝ))
  · have h := physical_price_linear (2 * s + 3) (by omega) (by omega) g' hsmall
    have hle : min ((((2 * s + 3 : ℕ) : ℝ)) - 1) (1 / ε) / 16 ≤ (((2 * s + 3 : ℕ) : ℝ) - 1) / 4 := by
      have : 0 ≤ ((2 * s + 3 : ℕ) : ℝ) - 1 := by linarith
      have hmn : min ((((2 * s + 3 : ℕ) : ℝ)) - 1) (1 / ε) ≤ ((2 * s + 3 : ℕ) : ℝ) - 1 :=
        min_le_left _ _
      linarith
    exact hle.trans h
  · push_neg at hsmall
    have hd0 : 0 < l1 (gFamily (2 * s + 3)) g' := lt_trans (by positivity) hsmall
    have h := collapse_all s g' hd0 (hl1.trans hε) hpos
    refine le_trans ?_ h
    gcongr

/-- **The lower side of the robust price.** -/
theorem robust_lower (s : ℕ) (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 6) :
    min ((((2 * s + 3 : ℕ) : ℝ)) - 1) (1 / ε) / 16 ≤ robustPrice s ε :=
  le_csInf ⟨_, family_mem s ε hε0.le⟩ (member_lower s ε hε0 hε)

theorem ratioSet_bddBelow (s : ℕ) (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 6) :
    BddBelow (ratioSet s ε) :=
  ⟨_, fun r hr => member_lower s ε hε0 hε r hr⟩

/-- **The upper side of the robust price.** -/
theorem robust_upper (s : ℕ) (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 6) :
    robustPrice s ε
      ≤ min ((((2 * s + 3 : ℕ) : ℝ) + 3) * (((2 * s + 3 : ℕ) : ℝ) - 1)
          / (2 * ((2 * s + 3 : ℕ) : ℝ))) (10 / ε) := by
  have hb := ratioSet_bddBelow s ε hε0 hε
  refine le_min ?_ ?_
  · rw [← family_price s]
    exact csInf_le hb (family_mem s ε hε0.le)
  · have hε1 : ε ≤ 1 := hε.trans (by norm_num)
    exact (csInf_le hb (witness_mem s ε hε0 hε1)).trans (collapse_upper s ε hε0 hε1).2.2

/-- **The robust price, both sides.**  For odd `m = 2s+3` and `0 < ε ≤ 1/6`,
`min(m-1, 1/ε)/16 ≤ R_m(ε) ≤ min((m+3)(m-1)/(2m), 10/ε) ≤ 10 min(m-1, 1/ε)`. -/
theorem robust_ball (s : ℕ) (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 6) :
    min ((((2 * s + 3 : ℕ) : ℝ)) - 1) (1 / ε) / 16 ≤ robustPrice s ε
      ∧ robustPrice s ε
          ≤ min ((((2 * s + 3 : ℕ) : ℝ) + 3) * (((2 * s + 3 : ℕ) : ℝ) - 1)
              / (2 * ((2 * s + 3 : ℕ) : ℝ))) (10 / ε)
      ∧ min ((((2 * s + 3 : ℕ) : ℝ) + 3) * (((2 * s + 3 : ℕ) : ℝ) - 1)
              / (2 * ((2 * s + 3 : ℕ) : ℝ))) (10 / ε)
          ≤ 10 * min ((((2 * s + 3 : ℕ) : ℝ)) - 1) (1 / ε) := by
  refine ⟨robust_lower s ε hε0 hε, robust_upper s ε hε0 hε, ?_⟩
  set x : ℝ := ((2 * s + 3 : ℕ) : ℝ) with hx
  have hx3 : (3 : ℝ) ≤ x := by rw [hx]; exact_mod_cast (show 3 ≤ 2 * s + 3 by omega)
  rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 10)]
  refine le_min ((min_le_left _ _).trans ?_) ((min_le_right _ _).trans (le_of_eq (by ring)))
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-! ## Uniform rescaling keeps the whole price

`g' = (1 + ε/(m+4)) g_m` lies at `ℓ₁` distance exactly `ε` from `g_m`, and every normalised
regret, hence every value and the price ratio, is unchanged. So no statement of the form "every
perturbation of size `ε` collapses the price" can hold. The robust price above is a statement
about the worst member of the ball, not about every member. -/

theorem inf'_const_mul {α : Type*} (s : Finset α) (hne : s.Nonempty) (f : α → ℝ) (c : ℝ)
    (hc : 0 ≤ c) : s.inf' hne (fun x => c * f x) = c * s.inf' hne f := by
  apply le_antisymm
  · obtain ⟨x, hx, hxe⟩ := Finset.exists_mem_eq_inf' hne f
    rw [hxe]
    exact Finset.inf'_le _ hx
  · exact Finset.le_inf' _ _ fun x hx => mul_le_mul_of_nonneg_left (Finset.inf'_le _ hx) hc

variable {m : ℕ}

theorem trueBaseline_smul (g : Fin m → ℝ) (c : ℝ) (hc : 0 < c) (k : Fin (m + 1)) :
    trueBaseline (fun i => c * g i) k = c * trueBaseline g k := by
  unfold trueBaseline baseline
  rw [← inf'_const_mul _ _ _ c hc.le]
  congr 1
  funext S
  rw [← Finset.mul_sum, abs_mul, abs_of_pos hc]

theorem normMass_smul (g : Fin m → ℝ) (c : ℝ) (hc : 0 < c) :
    normMass (fun i => c * g i) = c * normMass g := by
  unfold normMass
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [abs_mul, abs_of_pos hc]

theorem normalizedRegret_smul (g : Fin m → ℝ) (c : ℝ) (hc : 0 < c)
    (σ : Equiv.Perm (Fin m)) (k : Fin (m + 1)) :
    normalizedRegret (fun i => c * g i) σ k = normalizedRegret g σ k := by
  unfold normalizedRegret rawRegret
  rw [trueBaseline_smul g c hc, normMass_smul g c hc, ← Finset.mul_sum, abs_mul, abs_of_pos hc]
  by_cases h0 : normMass g = 0
  · rw [h0]; simp
  · field_simp

/-- **Uniform rescaling leaves every value unchanged.** -/
theorem trueValue_smul (g : Fin m → ℝ) (c : ℝ) (hc : 0 < c) (η : ℝ)
    (K : Finset (Fin (m + 1))) (hK : K.Nonempty) :
    trueValue (fun i => c * g i) η K hK = trueValue g η K hK := by
  unfold trueValue trueObjective
  simp_rw [normalizedRegret_smul g c hc]

/-- **A perturbation of every size that keeps the whole price.**  For every `ε ≥ 0`, the
rescaled family `(1 + ε/(m+4)) g_m` is at `ℓ₁` distance exactly `ε` from `g_m`, keeps a positive
free value, and has the family's own price ratio `(m+3)(m-1)/(2m)`. -/
theorem rescaled_keeps_price (s : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    l1 (gFamily (2 * s + 3))
        (fun i => (1 + ε / (((2 * s + 3 : ℕ) : ℝ) + 4)) * gFamily (2 * s + 3) i) = ε
      ∧ 0 < trueValue (fun i => (1 + ε / (((2 * s + 3 : ℕ) : ℝ) + 4)) * gFamily (2 * s + 3) i)
          ((2 * s + 3 : ℕ) : ℝ) (interiorK (2 * s + 3)) (interiorK_nonempty _ (by omega))
      ∧ priceRatio s (fun i => (1 + ε / (((2 * s + 3 : ℕ) : ℝ) + 4)) * gFamily (2 * s + 3) i)
          = (((2 * s + 3 : ℕ) : ℝ) + 3) * (((2 * s + 3 : ℕ) : ℝ) - 1)
            / (2 * ((2 * s + 3 : ℕ) : ℝ)) := by
  have hd : (0 : ℝ) < ((2 * s + 3 : ℕ) : ℝ) + 4 := by positivity
  have hc : 0 < 1 + ε / (((2 * s + 3 : ℕ) : ℝ) + 4) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · unfold l1
    have hterm : ∀ i, |gFamily (2 * s + 3) i
        - (1 + ε / (((2 * s + 3 : ℕ) : ℝ) + 4)) * gFamily (2 * s + 3) i|
        = ε / (((2 * s + 3 : ℕ) : ℝ) + 4) * |gFamily (2 * s + 3) i| := by
      intro i
      rw [show gFamily (2 * s + 3) i - (1 + ε / (((2 * s + 3 : ℕ) : ℝ) + 4)) * gFamily (2 * s + 3) i
          = -(ε / (((2 * s + 3 : ℕ) : ℝ) + 4) * gFamily (2 * s + 3) i) by ring,
        abs_neg, abs_mul, abs_of_nonneg (div_nonneg hε hd.le)]
    simp_rw [hterm]
    rw [← Finset.mul_sum]
    have hmass := PaperCRatioJoin.normMass_gFamily (2 * s + 3) (by omega)
    unfold normMass at hmass
    rw [hmass]
    field_simp
  · rw [trueValue_smul _ _ hc]; exact family_free_pos s
  · unfold priceRatio
    rw [trueValue_smul _ _ hc, trueValue_smul _ _ hc]
    exact family_price s

#print axioms family_price
#print axioms member_lower
#print axioms robust_lower
#print axioms robust_upper
#print axioms robust_ball
#print axioms trueValue_smul
#print axioms rescaled_keeps_price

end CIGAMF.P13.PaperCRobustBall
