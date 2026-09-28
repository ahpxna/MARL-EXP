import «LeanPaperARepairLawV1»
import «LeanPaperA7IdealFamilyV1»

/-!
# Paper A: the repair frontier as a rate — concavity, continuity and the limit steps

In the abstract setting of `LeanPaperASacrificeDualityV1` (concave `J_f`, `J_t` on the simplex,
`Γ = J_f(w*) > 0`), the repair frontier is `R(b) = sup{J_t(w) : s(w) ≤ b}`.

* `R_le`, `R_mono`: `R` bounds every design within the budget and is nondecreasing.
* `R_concave`: `R` is concave on `[0, ∞)`. Mixing two designs mixes their sacrifices convexly
  and their true information concavely.
* `R_continuousAt`: hence `R` is continuous at every `b > 0` (Mathlib's
  `ConcaveOn.continuousOn_interior`).
* `near_design`: for `b > 0` and `ε > 0`, some design has sacrifice strictly below `b` and true
  information above `R(b) - ε`. This is the design the attaining learner holds.
* `frontier_lower_rate`: suppose a family of expected costs satisfies
  `E_δ · R(b + c/E_δ) ≥ (1-δ) log(1/δ) - log 2`, which is the eventual-class budget law. Then
  `LowerRate E (R b)`, i.e. `liminf E_δ / log(1/δ) ≥ 1/R(b)`.

With `fix_upper_rate` (`LeanPaperABudgetUpperV1`) at the design of `near_design`, these are the
concavity and limit steps of the corollary "the frontier is the optimal rate". What remains
informal there is only the identification of the stream budget with the kernel class.
-/

namespace CIGAMF.P13.PaperARepairRate

open Finset Set
open CIGAMF.P13.PaperASacrificeDuality CIGAMF.P13.PaperAEndgame

variable {ι : Type*} [Fintype ι]

/-- **The repair frontier.** -/
noncomputable def Rfront (Jf Jt : (ι → ℝ) → ℝ) (Γ b : ℝ) : ℝ :=
  sSup {x | ∃ w, IsAllocG w ∧ sac Jf Γ w ≤ b ∧ x = Jt w}

section Frontier

variable (Jf Jt : (ι → ℝ) → ℝ) (Γ : ℝ) (Jmax : ℝ)
  (hJmax : ∀ w, IsAllocG w → Jt w ≤ Jmax)
  (wstar : ι → ℝ) (hws : IsAllocG wstar) (hopt : Jf wstar = Γ) (hΓ : 0 < Γ)

include hJmax in
theorem R_bdd (b : ℝ) : BddAbove {x | ∃ w, IsAllocG w ∧ sac Jf Γ w ≤ b ∧ x = Jt w} :=
  ⟨Jmax, by rintro _ ⟨w, hw, -, rfl⟩; exact hJmax w hw⟩

include hws hopt hΓ in
theorem R_nonempty (b : ℝ) (hb : 0 ≤ b) :
    {x | ∃ w, IsAllocG w ∧ sac Jf Γ w ≤ b ∧ x = Jt w}.Nonempty := by
  refine ⟨Jt wstar, wstar, hws, ?_, rfl⟩
  unfold sac; rw [hopt, div_self hΓ.ne']; linarith

include hJmax in
theorem R_le (b : ℝ) (w : ι → ℝ) (hw : IsAllocG w) (hs : sac Jf Γ w ≤ b) :
    Jt w ≤ Rfront Jf Jt Γ b :=
  le_csSup (R_bdd Jf Jt Γ Jmax hJmax b) ⟨w, hw, hs, rfl⟩

include hJmax hws hopt hΓ in
theorem R_mono (b₁ b₂ : ℝ) (h0 : 0 ≤ b₁) (h : b₁ ≤ b₂) :
    Rfront Jf Jt Γ b₁ ≤ Rfront Jf Jt Γ b₂ :=
  csSup_le_csSup (R_bdd Jf Jt Γ Jmax hJmax b₂) (R_nonempty Jf Jt Γ wstar hws hopt hΓ b₁ h0)
    (by rintro _ ⟨w, hw, hs, rfl⟩; exact ⟨w, hw, hs.trans h, rfl⟩)

include hJmax hws hopt hΓ in
/-- **The frontier is concave.** -/
theorem R_concave
    (hconcf : ∀ a b, IsAllocG a → IsAllocG b → ∀ β : ℝ, 0 ≤ β → β ≤ 1 →
      (1 - β) * Jf a + β * Jf b ≤ Jf (mixD β a b))
    (hconct : ∀ a b, IsAllocG a → IsAllocG b → ∀ β : ℝ, 0 ≤ β → β ≤ 1 →
      (1 - β) * Jt a + β * Jt b ≤ Jt (mixD β a b)) :
    ConcaveOn ℝ (Ici 0) (Rfront Jf Jt Γ) := by
  refine ⟨convex_Ici 0, fun x hx y hy p q hp hq hpq => ?_⟩
  simp only [Set.mem_Ici] at hx hy
  simp only [smul_eq_mul]
  have hxy : 0 ≤ p * x + q * y := by positivity
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨_, ⟨w1, hw1, hs1, rfl⟩, h1⟩ := exists_lt_of_lt_csSup
    (R_nonempty Jf Jt Γ wstar hws hopt hΓ x hx) (show Rfront Jf Jt Γ x - ε / 2 < Rfront Jf Jt Γ x by linarith)
  obtain ⟨_, ⟨w2, hw2, hs2, rfl⟩, h2⟩ := exists_lt_of_lt_csSup
    (R_nonempty Jf Jt Γ wstar hws hopt hΓ y hy) (show Rfront Jf Jt Γ y - ε / 2 < Rfront Jf Jt Γ y by linarith)
  have hq1 : q ≤ 1 := by linarith
  have hmix := mixD_alloc q hq hq1 w1 w2 hw1 hw2
  have hsac : sac Jf Γ (mixD q w1 w2) ≤ p * x + q * y := by
    have hf := hconcf w1 w2 hw1 hw2 q hq hq1
    unfold sac at hs1 hs2 ⊢
    have hp' : 1 - q = p := by linarith
    rw [hp'] at hf
    have : (p * Jf w1 + q * Jf w2) / Γ ≤ Jf (mixD q w1 w2) / Γ :=
      div_le_div_of_nonneg_right hf hΓ.le
    have e : (p * Jf w1 + q * Jf w2) / Γ = p * (Jf w1 / Γ) + q * (Jf w2 / Γ) := by ring
    rw [e] at this
    nlinarith
  have hJ := hconct w1 w2 hw1 hw2 q hq hq1
  have hp' : 1 - q = p := by linarith
  rw [hp'] at hJ
  have hR := R_le Jf Jt Γ Jmax hJmax _ _ hmix hsac
  have hp1 : p * (Rfront Jf Jt Γ x - ε / 2) ≤ p * Jt w1 := mul_le_mul_of_nonneg_left h1.le hp
  have hq1' : q * (Rfront Jf Jt Γ y - ε / 2) ≤ q * Jt w2 := mul_le_mul_of_nonneg_left h2.le hq
  have hsum : p * (ε / 2) + q * (ε / 2) = ε / 2 := by rw [← add_mul, hpq, one_mul]
  nlinarith

include hJmax hws hopt hΓ in
/-- **The frontier is continuous at every interior budget.** -/
theorem R_continuousAt
    (hconcf : ∀ a b, IsAllocG a → IsAllocG b → ∀ β : ℝ, 0 ≤ β → β ≤ 1 →
      (1 - β) * Jf a + β * Jf b ≤ Jf (mixD β a b))
    (hconct : ∀ a b, IsAllocG a → IsAllocG b → ∀ β : ℝ, 0 ≤ β → β ≤ 1 →
      (1 - β) * Jt a + β * Jt b ≤ Jt (mixD β a b)) (b : ℝ) (hb : 0 < b) :
    ContinuousAt (Rfront Jf Jt Γ) b := by
  have hc := (R_concave Jf Jt Γ Jmax hJmax wstar hws hopt hΓ hconcf hconct).continuousOn_interior
  rw [interior_Ici] at hc
  exact hc.continuousAt (Ioi_mem_nhds hb)

include hJmax hws hopt hΓ in
/-- **A design strictly inside the budget, near the frontier.** -/
theorem near_design
    (hconcf : ∀ a b, IsAllocG a → IsAllocG b → ∀ β : ℝ, 0 ≤ β → β ≤ 1 →
      (1 - β) * Jf a + β * Jf b ≤ Jf (mixD β a b))
    (hconct : ∀ a b, IsAllocG a → IsAllocG b → ∀ β : ℝ, 0 ≤ β → β ≤ 1 →
      (1 - β) * Jt a + β * Jt b ≤ Jt (mixD β a b)) (b : ℝ) (hb : 0 < b) (ε : ℝ) (hε : 0 < ε) :
    ∃ w, IsAllocG w ∧ sac Jf Γ w < b ∧ Rfront Jf Jt Γ b - ε < Jt w := by
  have hcont := R_continuousAt Jf Jt Γ Jmax hJmax wstar hws hopt hΓ hconcf hconct b hb
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨ρ, hρ, hball⟩ := hcont (ε / 2) (by positivity)
  set b' := max (b / 2) (b - ρ / 2) with hb'
  have hb'0 : 0 ≤ b' := le_max_of_le_left (by linarith)
  have hb'lt : b' < b := max_lt (by linarith) (by linarith)
  have hdist : dist b' b < ρ := by
    rw [Real.dist_eq, abs_lt]
    constructor
    · have : b - ρ / 2 ≤ b' := le_max_right _ _
      linarith
    · linarith
  have hclose := hball hdist
  rw [Real.dist_eq, abs_lt] at hclose
  obtain ⟨_, ⟨w, hw, hs, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup
    (R_nonempty Jf Jt Γ wstar hws hopt hΓ b' hb'0)
    (show Rfront Jf Jt Γ b' - ε / 2 < Rfront Jf Jt Γ b' by linarith)
  exact ⟨w, hw, lt_of_le_of_lt hs hb'lt, by linarith⟩

end Frontier

/-! ## The limit on the lower side -/

/-- **The eventual-class budget law gives the lower rate `1/R(b)`.**  `Rf` is any nondecreasing
function continuous at `b`, bounded by `Jmax`, with `Rf b > 0`; the costs `E δ` satisfy the law
with excess `c / E δ`. -/
theorem frontier_lower_rate (Rf : ℝ → ℝ) (b c Jmax : ℝ) (hc : 0 ≤ c) (hRb : 0 < Rf b)
    (hbd : ∀ x, b ≤ x → Rf x ≤ Jmax)
    (hcont : ContinuousAt Rf b) (E : ℝ → ℝ) (δ0 : ℝ) (hδ0 : 0 < δ0)
    (hlaw : ∀ δ, 0 < δ → δ < δ0 →
      0 < E δ ∧ (1 - δ) * Real.log (1 / δ) - Real.log 2 ≤ E δ * Rf (b + c / E δ)) :
    LowerRate E (Rf b) := by
  intro ε hε
  have hJ : 0 < Jmax := hRb.trans_le (hbd b le_rfl)
  -- the slack in the rate
  set η0 := min (Rf b) (ε * Rf b ^ 2 / 4) with hη0
  have hη0p : 0 < η0 := lt_min hRb (by positivity)
  have hGam : 1 / Rf b - ε / 2 ≤ 1 / (Rf b + η0) := by
    rw [div_sub' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : η0 ≤ ε * Rf b ^ 2 / 4 := min_le_right _ _
    have h2 : η0 ≤ Rf b := min_le_left _ _
    nlinarith [mul_pos hε hRb]
  -- continuity: a neighbourhood where Rf is within η0
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨ρ, hρ, hball⟩ := hcont η0 hη0p
  -- E δ is large once δ is small
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K := c / ρ + 1 with hK
  set T := 2 * (K * Jmax + Real.log 2) with hT
  have hT0 : 0 < T := by positivity
  set δ1 := min (min δ0 (1 / 2)) (Real.exp (-T)) with hδ1
  have hbound : ∀ δ, 0 < δ → δ < δ1 →
      ((1 - 2 * δ) * Real.log (1 / (2 * δ)) - Real.log 2) / (Rf b + η0) ≤ E δ := by
    intro δ hδ hδlt
    have hδ0' : δ < δ0 := lt_of_lt_of_le hδlt (le_trans (min_le_left _ _) (min_le_left _ _))
    have hδh : δ < 1 / 2 := lt_of_lt_of_le hδlt (le_trans (min_le_left _ _) (min_le_right _ _))
    have hδe : δ < Real.exp (-T) := lt_of_lt_of_le hδlt (min_le_right _ _)
    obtain ⟨hE, hD⟩ := hlaw δ hδ hδ0'
    have hL : T < Real.log (1 / δ) := by
      rw [one_div, Real.log_inv, lt_neg]
      calc Real.log δ < Real.log (Real.exp (-T)) := Real.log_lt_log hδ hδe
        _ = -T := Real.log_exp _
    have hL0 : 0 ≤ Real.log (1 / δ) := by linarith
    -- the budget law with the crude bound Rf ≤ Jmax gives E δ ≥ K
    have hEK : K ≤ E δ := by
      have hcx : b ≤ b + c / E δ := le_add_of_nonneg_right (div_nonneg hc hE.le)
      have h1 := hbd _ hcx
      have h2 : (1 - δ) * Real.log (1 / δ) - Real.log 2 ≤ E δ * Jmax :=
        hD.trans (mul_le_mul_of_nonneg_left h1 hE.le)
      have h3 : Real.log (1 / δ) / 2 - Real.log 2 ≤ (1 - δ) * Real.log (1 / δ) - Real.log 2 := by
        nlinarith
      have h4 : K * Jmax < E δ * Jmax := by nlinarith
      exact (lt_of_mul_lt_mul_right h4 hJ.le).le
    -- so the excess is inside the continuity ball
    have hexc : c / E δ < ρ := by
      rw [div_lt_iff₀ hE]
      have : c < ρ * K := by
        rw [hK, mul_add, mul_div_cancel₀ c hρ.ne', mul_one]; linarith
      nlinarith
    have hdist : dist (b + c / E δ) b < ρ := by
      rw [Real.dist_eq, add_sub_cancel_left, abs_of_nonneg (div_nonneg hc hE.le)]
      exact hexc
    have hnear := hball hdist
    rw [Real.dist_eq, abs_lt] at hnear
    have hRup : Rf (b + c / E δ) ≤ Rf b + η0 := by linarith
    have h5 : (1 - δ) * Real.log (1 / δ) - Real.log 2 ≤ E δ * (Rf b + η0) :=
      hD.trans (mul_le_mul_of_nonneg_left hRup hE.le)
    have h6 : (1 - 2 * δ) * Real.log (1 / (2 * δ)) - Real.log 2
        ≤ (1 - δ) * Real.log (1 / δ) - Real.log 2 := by
      have hlog : Real.log (1 / (2 * δ)) ≤ Real.log (1 / δ) := by
        apply Real.log_le_log (by positivity)
        rw [div_le_div_iff₀ (by positivity) hδ]; linarith
      have hlog0 : 0 ≤ Real.log (1 / (2 * δ)) := Real.log_nonneg (by
        rw [le_div_iff₀ (by positivity)]; linarith)
      nlinarith
    rw [div_le_iff₀ (by positivity)]
    linarith
  obtain ⟨u, hu, hU⟩ := CIGAMF.P13.PaperA7IdealFamily.lower_rate_of_bound E (Rf b + η0)
    (by positivity) δ1 (by positivity) hbound (ε / 2) (by positivity)
  exact ⟨u, hu, fun δ hδ hδu => by have := hU δ hδ hδu; linarith⟩

#print axioms R_le
#print axioms R_mono
#print axioms R_concave
#print axioms R_continuousAt
#print axioms near_design
#print axioms frontier_lower_rate

end CIGAMF.P13.PaperARepairRate
