import «LeanPaperAPolicyClassesV1»
import «LeanPaperARepairRateV1»

/-!
# Paper A: the budget law on the simplex, the repair frontier, and the truncation limit

The budget laws of `LeanPaperARepairLawV1` and `LeanPaperAPolicyClassesV1` take a bound
`hR : ∀ w ≥ 0, s(w) ≤ b → J_t(w) ≤ R` over **every** nonnegative vector. The repair frontier
`R_θ(b)` is a supremum over the **simplex**. With `s = 1 - J_f/Γ` and `J_f`, `J_t` homogeneous,
the scaled design `c v` has `s(cv) → -∞` and `J_t(cv) → ∞`. So `hR` cannot be discharged by a
finite frontier value, and the frontier never entered those laws. This module closes the gap.

* `ebar_alloc`: the expected design is on the simplex and puts no mass on the dummy.
* `budget_law_alloc`: the budget law needs `hR` only on the simplex.
* `Jt_concave`, `Jt_le_sum`, `Jt_nonneg`: an infimum of linear forms is concave, bounded and
  nonnegative on designs. These are the hypotheses of the frontier lemmas.
* `eventual_frontier_law`: every policy of the eventual class `EventualClass t₀` that decides
  with an event of probability `p` at `θ` and at most `δ` at the alternatives pays
  `p log(1/δ) - log 2 ≤ E|N| · R_θ(b + (1-b) t₀/E|N|)`, with `R_θ = Rfront` itself.
* `scale_mono`: for a concave nonnegative frontier, `x ↦ x R(b + c/x)` is nondecreasing.
* `truncation_limit`: the truncations `π ∧ n` of one stopping policy with expected informative
  count at most `E` give `(1-δ) log(1/δ) - log 2 ≤ E · R(b + c/E)` in the limit `n → ∞`,
  as soon as their success probabilities tend to `1 - δ`. The budget is imposed pathwise after
  the burn-in, so every truncation is in the eventual class: no budget at the stopping time is
  transferred to the truncation.
* `frontier_rate_lower`: a family of δ-correct policies of the eventual class with **one
  burn-in `t₀` for all δ** has `liminf E_δ|N|/log(1/δ) ≥ 1/R_θ(b)`, on any channel.
-/

namespace CIGAMF.P13.PaperARepairBridge

open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperALowerKL CIGAMF.P13.PaperALowerGame
open CIGAMF.P13.PaperASacrificeDuality CIGAMF.P13.PaperARepairLaw CIGAMF.P13.PaperAFamilyLower
open CIGAMF.P13.PaperAPolicyClasses CIGAMF.P13.PaperARepairRate CIGAMF.P13.PaperAEndgame

section Channel

variable {W Q : Type*} [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q]
  [DecidableEq Q] [Fintype Q]

/-! ## 1. The expected design lives on the simplex -/

theorem ebar_sum (C : Channel W Q) (π : Policy Q) (θ : W) (n : ℕ) (hpos : 0 < etot C π θ n) :
    ∑ q, ebar C π θ n q = 1 := by
  have e : ∑ q, ecnt C π θ n q * (if q = C.dummy then 0 else 1) = etot C π θ n := rfl
  unfold ebar
  rw [← Finset.sum_div, e, div_self hpos.ne']

theorem ebar_dummy (C : Channel W Q) (π : Policy Q) (θ : W) (n : ℕ) :
    ebar C π θ n C.dummy = 0 := by
  unfold ebar; simp

theorem ebar_alloc (C : Channel W Q) (π : Policy Q) (θ : W) (n : ℕ) (hpos : 0 < etot C π θ n) :
    IsAllocG (ebar C π θ n) :=
  ⟨ebar_nonneg C π θ n hpos, ebar_sum C π θ n hpos⟩

/-! ## 2. The true game on designs -/

theorem infoAt_mix (C : Channel W Q) (θ l : W) (β : ℝ) (a b : Q → ℝ) :
    infoAt C θ l (mixD β a b) = (1 - β) * infoAt C θ l a + β * infoAt C θ l b := by
  unfold infoAt mixD
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun q _ => by ring

theorem Jt_nonneg (C : Channel W Q) (θ : W) (L : Set W) [Nonempty L] (w : Q → ℝ)
    (hw : ∀ q, 0 ≤ w q) : 0 ≤ Jt C θ L w :=
  le_ciInf fun l => infoAt_nonneg C θ l w hw

theorem Jt_bdd (C : Channel W Q) (θ : W) (L : Set W) (w : Q → ℝ) (hw : ∀ q, 0 ≤ w q) :
    BddBelow (Set.range fun l : L => infoAt C θ l w) :=
  ⟨0, by rintro _ ⟨l, rfl⟩; exact infoAt_nonneg C θ l w hw⟩

/-- **An infimum of linear forms is concave on nonnegative vectors.** -/
theorem Jt_concave (C : Channel W Q) (θ : W) (L : Set W) [Nonempty L] (a b : Q → ℝ)
    (ha : IsAllocG a) (hb : IsAllocG b) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    (1 - β) * Jt C θ L a + β * Jt C θ L b ≤ Jt C θ L (mixD β a b) := by
  refine le_ciInf fun l => ?_
  rw [infoAt_mix]
  have h1 : Jt C θ L a ≤ infoAt C θ l a := ciInf_le (Jt_bdd C θ L a ha.1) l
  have h2 : Jt C θ L b ≤ infoAt C θ l b := ciInf_le (Jt_bdd C θ L b hb.1) l
  have := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1 - β)
  have := mul_le_mul_of_nonneg_left h2 hβ0
  linarith

/-- **The true game is bounded on designs**, by the total information against one
alternative. -/
theorem Jt_le_sum (C : Channel W Q) (θ : W) (L : Set W) (l₀ : L) (w : Q → ℝ)
    (hw : IsAllocG w) : Jt C θ L w ≤ ∑ q, (klq C θ l₀ q).toReal := by
  refine (ciInf_le (Jt_bdd C θ L w hw.1) l₀).trans ?_
  unfold infoAt
  refine Finset.sum_le_sum fun q _ => ?_
  have hwq : w q ≤ 1 := by
    rw [← hw.2]
    exact Finset.single_le_sum (fun i _ => hw.1 i) (Finset.mem_univ q)
  have := ENNReal.toReal_nonneg (a := klq C θ l₀ q)
  nlinarith [hw.1 q]

/-! ## 3. The eventual-class law with the frontier itself -/

/-- **The budget law with an event of any probability `p` at `θ`.** -/
theorem event_law (C : Channel W Q) (π : Policy Q) (n : ℕ) (θ : W) (L : Set W) [Nonempty L]
    (S : Set (Hist Q n)) (hS : MeasurableSet S) (δ p : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hθ : p ≤ (hist C π θ n).real S) (hL : ∀ l ∈ L, (hist C π l n).real S ≤ δ)
    (hfin : ∀ l ∈ L, ∀ q, klq C θ l q ≠ ⊤) (hpos : 0 < etot C π θ n) :
    p * Real.log (1 / δ) - Real.log 2 ≤ etot C π θ n * Jt C θ L (ebar C π θ n) := by
  have hlog : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have hper : ∀ l : L, (p * Real.log (1 / δ) - Real.log 2) / etot C π θ n
      ≤ infoAt C θ l (ebar C π θ n) := by
    intro l
    have h := event_info C π n θ l S hS δ hδ (hL l l.2) (hfin l l.2)
    rw [← etot_mul_infoAt C π θ n l hpos] at h
    rw [div_le_iff₀ hpos]
    have := mul_le_mul_of_nonneg_right hθ hlog
    nlinarith
  have hJ : (p * Real.log (1 / δ) - Real.log 2) / etot C π θ n ≤ Jt C θ L (ebar C π θ n) :=
    le_ciInf hper
  rw [div_le_iff₀ hpos] at hJ
  linarith [mul_comm (Jt C θ L (ebar C π θ n)) (etot C π θ n)]

/-- **The budget law, with the frontier bound needed only on the simplex.** -/
theorem budget_law_alloc (C : Channel W Q) (π : Policy Q) (n : ℕ) (θ : W) (L : Set W)
    [Nonempty L] (S : Set (Hist Q n)) (hS : MeasurableSet S) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hθ : 1 - δ ≤ (hist C π θ n).real S) (hL : ∀ l ∈ L, (hist C π l n).real S ≤ δ)
    (hfin : ∀ l ∈ L, ∀ q, klq C θ l q ≠ ⊤) (hpos : 0 < etot C π θ n)
    (s : (Q → ℝ) → ℝ) (b R : ℝ) (hR : ∀ w : Q → ℝ, IsAllocG w → s w ≤ b → Jt C θ L w ≤ R)
    (hbud : s (ebar C π θ n) ≤ b) :
    (1 - δ) * Real.log (1 / δ) - Real.log 2 ≤ etot C π θ n * R :=
  (event_law C π n θ L S hS δ (1 - δ) hδ hδ1 hθ hL hfin hpos).trans
    (mul_le_mul_of_nonneg_left (hR _ (ebar_alloc C π θ n hpos) hbud) hpos.le)

/-- **The eventual-class law against the repair frontier.**  `Rfront` is the supremum of the
true game over the simplex designs whose sacrifice is within the budget. -/
theorem eventual_frontier_law (C : Channel W Q) (π : Policy Q) (n : ℕ) (θ : W) (L Lf : Set W)
    [Nonempty L] [Nonempty Lf] (l₀ : L) (S : Set (Hist Q n)) (hS : MeasurableSet S) (δ p : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hθ : p ≤ (hist C π θ n).real S)
    (hL : ∀ l ∈ L, (hist C π l n).real S ≤ δ)
    (hfin : ∀ l ∈ L, ∀ q, klq C θ l q ≠ ⊤) (hfinf : ∀ l ∈ Lf, ∀ q, klq C θ l q ≠ ⊤)
    (hpos : 0 < etot C π θ n) (Γ b : ℝ) (t₀ : ℕ) (hΓ : 0 < Γ) (hb : b ≤ 1)
    (hE : EventualClass C π θ Lf Γ b n t₀) :
    p * Real.log (1 / δ) - Real.log 2
      ≤ etot C π θ n * Rfront (Jt C θ Lf) (Jt C θ L) Γ (b + (1 - b) * t₀ / etot C π θ n) := by
  have h1 := event_law C π n θ L S hS δ p hδ hδ1 hθ hL hfin hpos
  have hs := (eventual_expected C π θ Lf Γ b n t₀ hΓ hb hfinf hpos hE).2
  have hR := R_le (Jt C θ Lf) (Jt C θ L) Γ (∑ q, (klq C θ l₀ q).toReal)
    (fun w hw => Jt_le_sum C θ L l₀ w hw) _ _ (ebar_alloc C π θ n hpos) hs
  exact h1.trans (mul_le_mul_of_nonneg_left hR hpos.le)

end Channel

/-! ## 4. The scale monotonicity and the truncation limit -/

/-- **`x ↦ x R(b + c/x)` is nondecreasing** for a frontier concave on `[0, ∞)` with
`R(b) ≥ 0`. Write `b + c/y` as the mix of `b` and `b + c/x` with weight `x/y`. -/
theorem scale_mono (R : ℝ → ℝ) (hR : ConcaveOn ℝ (Set.Ici 0) R) (b c : ℝ) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hRb : 0 ≤ R b) (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) :
    x * R (b + c / x) ≤ y * R (b + c / y) := by
  have hy : 0 < y := hx.trans_le hxy
  have hmix : (1 - x / y) * b + (x / y) * (b + c / x) = b + c / y := by
    field_simp; ring
  have h01 : 0 ≤ x / y := div_nonneg hx.le hy.le
  have h1 : x / y ≤ 1 := (div_le_one hy).mpr hxy
  have hconc := hR.2 (Set.mem_Ici.mpr hb) (Set.mem_Ici.mpr (by positivity : 0 ≤ b + c / x))
    (by linarith : 0 ≤ 1 - x / y) h01 (by ring)
  simp only [smul_eq_mul] at hconc
  rw [hmix] at hconc
  have : x / y * R (b + c / x) ≤ R (b + c / y) := by nlinarith
  have := mul_le_mul_of_nonneg_left this hy.le
  rw [← mul_assoc, mul_div_cancel₀ _ hy.ne'] at this
  exact this

/-- **The truncation limit.**  Horizon-`n` truncations with success probabilities `p n → p`,
expected informative counts `0 < E_n ≤ E`, each obeying the eventual-class law, give the law at
`E` with probability `p`. -/
theorem truncation_limit (R : ℝ → ℝ) (hR : ConcaveOn ℝ (Set.Ici 0) R) (b c : ℝ) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hRb : 0 ≤ R b) (δ : ℝ) (En : ℕ → ℝ) (E : ℝ) (p : ℕ → ℝ) (pinf : ℝ)
    (hEn : ∀ n, 0 < En n) (hEE : ∀ n, En n ≤ E) (hp : Tendsto p atTop (𝓝 pinf))
    (hlaw : ∀ n, p n * Real.log (1 / δ) - Real.log 2 ≤ En n * R (b + c / En n)) :
    pinf * Real.log (1 / δ) - Real.log 2 ≤ E * R (b + c / E) := by
  have hbound : ∀ n, p n * Real.log (1 / δ) - Real.log 2 ≤ E * R (b + c / E) := fun n =>
    (hlaw n).trans (scale_mono R hR b c hb hc hRb (En n) E (hEn n) (hEE n))
  have hlim : Tendsto (fun n => p n * Real.log (1 / δ) - Real.log 2) atTop
      (𝓝 (pinf * Real.log (1 / δ) - Real.log 2)) :=
    (hp.mul_const _).sub_const _
  exact le_of_tendsto' hlim hbound

/-! ## 5. The frontier is a lower rate, on any channel -/

section Rate

variable {W Q : Type*} [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q]
  [DecidableEq Q] [Fintype Q]

/-- **The repair frontier bounds the rate of every family of the eventual class with a common
burn-in.**  For each `δ` the policy `π δ` at horizon `n δ` decides with an event of probability
`1-δ` at `θ` and at most `δ` at the alternatives. Then
`liminf E_δ|N|/log(1/δ) ≥ 1/R_θ(b)`. -/
theorem frontier_rate_lower (C : Channel W Q) (θ : W) (L Lf : Set W) [Nonempty L] [Nonempty Lf]
    (l₀ : L) (hfin : ∀ l ∈ L, ∀ q, klq C θ l q ≠ ⊤) (hfinf : ∀ l ∈ Lf, ∀ q, klq C θ l q ≠ ⊤)
    (Γ b : ℝ) (t₀ : ℕ) (hΓ : 0 < Γ) (hb0 : 0 < b) (hb : b ≤ 1)
    (wstar : Q → ℝ) (hws : IsAllocG wstar) (hopt : Jt C θ Lf wstar = Γ)
    (hRb : 0 < Rfront (Jt C θ Lf) (Jt C θ L) Γ b)
    (π : ℝ → Policy Q) (n : ℝ → ℕ) (S : ∀ δ, Set (Hist Q (n δ)))
    (hS : ∀ δ, MeasurableSet (S δ)) (δ0 : ℝ) (hδ0 : 0 < δ0) (hδ01 : δ0 ≤ 1)
    (hθ : ∀ δ, 0 < δ → δ < δ0 → 1 - δ ≤ (hist C (π δ) θ (n δ)).real (S δ))
    (hL : ∀ δ, 0 < δ → δ < δ0 → ∀ l ∈ L, (hist C (π δ) l (n δ)).real (S δ) ≤ δ)
    (hpos : ∀ δ, 0 < δ → δ < δ0 → 0 < etot C (π δ) θ (n δ))
    (hE : ∀ δ, 0 < δ → δ < δ0 → EventualClass C (π δ) θ Lf Γ b (n δ) t₀) :
    LowerRate (fun δ => etot C (π δ) θ (n δ)) (Rfront (Jt C θ Lf) (Jt C θ L) Γ b) := by
  set Jmax := ∑ q, (klq C θ l₀ q).toReal
  have hJmax : ∀ w, IsAllocG w → Jt C θ L w ≤ Jmax := fun w hw => Jt_le_sum C θ L l₀ w hw
  have hconc := fun a b ha hb β h0 h1 => Jt_concave C θ Lf a b ha hb β h0 h1
  have hconct := fun a b ha hb β h0 h1 => Jt_concave C θ L a b ha hb β h0 h1
  refine frontier_lower_rate (Rfront (Jt C θ Lf) (Jt C θ L) Γ) b ((1 - b) * t₀) Jmax
    (mul_nonneg (by linarith) (Nat.cast_nonneg _)) hRb ?_ ?_ _ δ0 hδ0 ?_
  · intro x hx
    refine csSup_le (R_nonempty (Jt C θ Lf) (Jt C θ L) Γ wstar hws hopt hΓ x (by linarith)) ?_
    rintro _ ⟨w, hw, -, rfl⟩
    exact hJmax w hw
  · exact R_continuousAt (Jt C θ Lf) (Jt C θ L) Γ Jmax hJmax wstar hws hopt hΓ hconc hconct b hb0
  · intro δ hδ hδlt
    refine ⟨hpos δ hδ hδlt, ?_⟩
    have h := eventual_frontier_law C (π δ) (n δ) θ L Lf l₀ (S δ) (hS δ) δ (1 - δ) hδ
      (by linarith) (hθ δ hδ hδlt) (hL δ hδ hδlt) hfin hfinf (hpos δ hδ hδlt) Γ b t₀ hΓ hb
      (hE δ hδ hδlt)
    exact h

end Rate

#print axioms ebar_alloc
#print axioms budget_law_alloc
#print axioms Jt_concave
#print axioms Jt_le_sum
#print axioms event_law
#print axioms eventual_frontier_law
#print axioms scale_mono
#print axioms truncation_limit
#print axioms frontier_rate_lower

end CIGAMF.P13.PaperARepairBridge
