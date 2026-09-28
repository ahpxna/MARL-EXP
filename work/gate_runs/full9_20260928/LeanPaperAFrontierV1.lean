import «LeanPaperACentredV1»

/-!
# Paper A: the repair frontier — what it costs at the surrogate to buy back true information

`LeanPaperACentredV1` proves a negative result: every design attaining the surrogate's
optimum has *zero* information against the alternatives the compression decision turns on,
and a design within `xi` of that optimum has at most `64 xi / (9 r M)`.  Read alone, that
says the surrogate is bad and stops.

The operational question is the trade-off.  If one is willing to give up a fraction `beta`
of the surrogate's value -- which is what a practitioner controls -- how much true
information can be bought back?  Define

    F(beta) = sup { J_true(w) : w an allocation, J_fr(w) >= (1 - beta) * Gamma_fr } .

Both bounds come from material already proved, plus one structural fact: each game's value
is an infimum of functions LINEAR in the design, hence CONCAVE in the design, so mixing two
designs cannot lose more than linearly.

* **Upper.** Substituting `xi = beta * Gamma_fr` into the near-optimal starvation bound
  gives `F(beta) <= beta / (8 r M)`.  Giving up a `beta` fraction buys back at most a
  `beta` fraction of the true game's own ceiling.
* **Lower.** Mix the surrogate's optimum with the certifying design of the true lower bound,
  `w_beta = (1 - beta) * wUnifC + beta * wCert`.  Concavity gives
  `J_fr(w_beta) >= (1 - beta) * Gamma_fr` -- so `w_beta` is feasible -- and
  `J_true(w_beta) >= beta * 9 / (128 (4 + 2 r M))`.

Together, for `r M >= 1`,

    9 beta / (128 (4 + 2 r M))  <=  F(beta)  <=  beta / (8 r M),

so `F(beta) = Theta(beta / (r M))`: the exchange rate is linear in the sacrifice and carries
the same `1/(rM)` factor as the separation itself.  Mixing two designs is not new; the
content is that on this problem the trade-off is pinned from both sides at the same order.
-/

namespace CIGAMF.P13.PaperAFrontier

open Finset
open CIGAMF.P13.PaperARPair
open CIGAMF.P13.PaperACentred

variable {r : ℕ}

/-! ## The design mixture, and why the value cannot drop faster than linearly -/

/-- The convex combination of two designs. -/
noncomputable def mixW (t : ℝ) (w₁ w₂ : Cell r → ℝ) : Cell r → ℝ :=
  fun e => (1 - t) * w₁ e + t * w₂ e

theorem mixW_isAlloc (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (w₁ w₂ : Cell r → ℝ)
    (h₁ : IsAlloc w₁) (h₂ : IsAlloc w₂) : IsAlloc (mixW t w₁ w₂) := by
  refine ⟨fun e => ?_, ?_⟩
  · have := h₁.1 e
    have := h₂.1 e
    have h1t : (0 : ℝ) ≤ 1 - t := by linarith
    unfold mixW
    positivity
  · unfold mixW
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h₁.2, h₂.2]
    ring

/-- **`energy` is linear in the design.**  This is the only structural input the frontier
needs: the alternative is held fixed and the weights enter once, multiplicatively. -/
theorem energy_mixW (t : ℝ) (w₁ w₂ var θ lam : Cell r → ℝ) :
    energy (mixW t w₁ w₂) var θ lam
      = (1 - t) * energy w₁ var θ lam + t * energy w₂ var θ lam := by
  unfold energy mixW
  have h : ∀ e : Cell r, ((1 - t) * w₁ e + t * w₂ e) * (lam e - θ e) ^ 2 / var e
      = (1 - t) * (w₁ e * (lam e - θ e) ^ 2 / var e)
        + t * (w₂ e * (lam e - θ e) ^ 2 / var e) := by
    intro e
    ring
  rw [Finset.sum_congr rfl (fun e _ => h e), Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- **A value is concave in the design**, because it is an infimum of linear functions.
Stated for an arbitrary alternative set, so both games use the one proof. -/
theorem value_concave (S : Set (Cell r → ℝ)) [Nonempty S] (M : ℝ) (hM : 0 < M)
    (w₁ w₂ : Cell r → ℝ) (h₁ : ∀ e, 0 ≤ w₁ e) (h₂ : ∀ e, 0 ≤ w₂ e)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * (⨅ lam : S, energy w₁ (pairVar M) (thetaC r) (lam : Cell r → ℝ))
        + t * (⨅ lam : S, energy w₂ (pairVar M) (thetaC r) (lam : Cell r → ℝ))
      ≤ ⨅ lam : S, energy (mixW t w₁ w₂) (pairVar M) (thetaC r) (lam : Cell r → ℝ) := by
  have hb₁ : BddBelow (Set.range (fun lam : S =>
      energy w₁ (pairVar M) (thetaC r) (lam : Cell r → ℝ))) := by
    refine ⟨0, ?_⟩
    rintro x ⟨lam, rfl⟩
    exact energyC_nonneg M hM w₁ _ h₁
  have hb₂ : BddBelow (Set.range (fun lam : S =>
      energy w₂ (pairVar M) (thetaC r) (lam : Cell r → ℝ))) := by
    refine ⟨0, ?_⟩
    rintro x ⟨lam, rfl⟩
    exact energyC_nonneg M hM w₂ _ h₂
  refine le_ciInf (fun lam => ?_)
  have e₁ := ciInf_le hb₁ lam
  have e₂ := ciInf_le hb₂ lam
  have h1t : (0 : ℝ) ≤ 1 - t := by linarith
  rw [energy_mixW]
  nlinarith [e₁, e₂, h1t, ht0]

/-! ## The frontier, both sides -/

/-- **Upper side.**  Keeping a `(1 - beta)` fraction of the surrogate's value costs all but
`beta / (8 r M)` of the true information --- `beta` times the true game's own ceiling. -/
theorem frontier_upper (M : ℝ) (hM : 0 < M) (r : ℕ) (hr : 0 < r)
    (w : Cell r → ℝ) (hw : IsAlloc w) (β : ℝ) (hβ : 0 ≤ β)
    (hfeas : (1 - β) * (9 / 512) ≤ frozenValueC₀ M w) :
    trueValueC₀ M w ≤ β / (8 * M * (r : ℝ)) := by
  have hrr : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hnear : (9 : ℝ) / 512 - (9 / 512 * β) ≤ frozenValueC₀ M w := by nlinarith [hfeas]
  have h := near_optimal_trueValueC₀_le M hM r hr w hw (9 / 512 * β) (by positivity) hnear
  have hid : 64 * (9 / 512 * β) / (9 * M * (r : ℝ)) = β / (8 * M * (r : ℝ)) := by
    field_simp
    ring
  rwa [hid] at h

/-- **Lower side.**  An explicit feasible design: mix the surrogate's optimum with the
design that certifies the true game's lower bound. -/
theorem frontier_lower (M : ℝ) (hM : 0 < M) (r : ℕ) (hr : 0 < r) [NeZero r]
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    ∃ w : Cell r → ℝ, IsAlloc w
      ∧ (1 - β) * (9 / 512) ≤ frozenValueC₀ M w
      ∧ 9 * β / (128 * (4 + 2 * (r : ℝ) * M)) ≤ trueValueC₀ M w := by
  classical
  have hrr : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hden : (0 : ℝ) < 4 + 2 * (r : ℝ) * M := by positivity
  have hufr : (9 : ℝ) / 512 ≤ frozenValueC₀ M (wUnifC r) :=
    le_trans (frozenValueC_unif_ge M hM)
      (frozenValueC_le_restricted M hM (wUnifC r) (wUnifC_isAlloc r).1)
  have hcert : (9 : ℝ) / (128 * (4 + 2 * (r : ℝ) * M)) ≤ trueValueC₀ M (wCert r M) :=
    trueValueC₀_wCert_ge r M hM
  refine ⟨mixW β (wUnifC r) (wCert r M),
    mixW_isAlloc β hβ0 hβ1 _ _ (wUnifC_isAlloc r) (wCert_isAlloc r M hM), ?_, ?_⟩
  · have hconc := value_concave (FrozenAltC₀ r) M hM (wUnifC r) (wCert r M)
      (wUnifC_isAlloc r).1 (wCert_isAlloc r M hM).1 β hβ0 hβ1
    have hnn : 0 ≤ frozenValueC₀ M (wCert r M) :=
      le_ciInf (fun lam => energyC_nonneg M hM _ _ (wCert_isAlloc r M hM).1)
    have h1t : (0 : ℝ) ≤ 1 - β := by linarith
    calc (1 - β) * (9 / 512)
        ≤ (1 - β) * frozenValueC₀ M (wUnifC r) + β * frozenValueC₀ M (wCert r M) := by
          nlinarith [hufr, hnn, h1t, hβ0]
      _ ≤ frozenValueC₀ M (mixW β (wUnifC r) (wCert r M)) := hconc
  · have hconc := value_concave (TrueAltC₀ r) M hM (wUnifC r) (wCert r M)
      (wUnifC_isAlloc r).1 (wCert_isAlloc r M hM).1 β hβ0 hβ1
    have hnn : 0 ≤ trueValueC₀ M (wUnifC r) :=
      trueValueC₀_nonneg M hM (wUnifC r) (wUnifC_isAlloc r).1
    have h1t : (0 : ℝ) ≤ 1 - β := by linarith
    calc 9 * β / (128 * (4 + 2 * (r : ℝ) * M))
        = β * (9 / (128 * (4 + 2 * (r : ℝ) * M))) := by ring
      _ ≤ (1 - β) * trueValueC₀ M (wUnifC r) + β * trueValueC₀ M (wCert r M) := by
          nlinarith [hcert, hnn, h1t, hβ0]
      _ ≤ trueValueC₀ M (mixW β (wUnifC r) (wCert r M)) := hconc

/-- **The frontier, pinned from both sides at the same order.**  For every sacrifice
`beta in [0,1]` there is a feasible design achieving at least `9 beta / (128 (4 + 2 r M))`,
and NO feasible design achieves more than `beta / (8 r M)`. -/
theorem frontier_two_sided (M : ℝ) (hM : 0 < M) (r : ℕ) (hr : 0 < r) [NeZero r]
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    (∃ w : Cell r → ℝ, IsAlloc w ∧ (1 - β) * (9 / 512) ≤ frozenValueC₀ M w
        ∧ 9 * β / (128 * (4 + 2 * (r : ℝ) * M)) ≤ trueValueC₀ M w)
      ∧ (∀ w : Cell r → ℝ, IsAlloc w → (1 - β) * (9 / 512) ≤ frozenValueC₀ M w →
          trueValueC₀ M w ≤ β / (8 * M * (r : ℝ))) :=
  ⟨frontier_lower M hM r hr β hβ0 hβ1,
   fun w hw hfeas => frontier_upper M hM r hr w hw β hβ0 hfeas⟩

/-- **At `beta = 0` the frontier collapses to the starvation theorem**, so the two results
are one family rather than two: no sacrifice buys nothing. -/
theorem frontier_at_zero (M : ℝ) (hM : 0 < M) (r : ℕ) (hr : 0 < r) [NeZero r]
    (w : Cell r → ℝ) (hw : IsAlloc w) (hopt : (9 : ℝ) / 512 ≤ frozenValueC₀ M w) :
    trueValueC₀ M w = 0 := by
  refine le_antisymm ?_ (trueValueC₀_nonneg M hM w hw.1)
  have h := frontier_upper M hM r hr w hw 0 le_rfl (by linarith [hopt])
  simpa using h

/-! ## Audit -/

#print axioms mixW_isAlloc
#print axioms energy_mixW
#print axioms value_concave
#print axioms frontier_upper
#print axioms frontier_lower
#print axioms frontier_two_sided
#print axioms frontier_at_zero

end CIGAMF.P13.PaperAFrontier
