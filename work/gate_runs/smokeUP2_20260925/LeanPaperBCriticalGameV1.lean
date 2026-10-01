import «LeanPaperBDecisionOrderV1»

/-!
# Paper B: the characteristic game in two layers, the exponent and the critical constant

The decision order (`LeanPaperBDecisionOrderV1`) fixes the **exponent** of the characteristic
game: `D_h(w) ≍ h^{2 s}`. This module fixes the **constant**: after rescaling by `h^{-2s}` the
game converges to a finite *critical game* `G*`. It is built only from the alternatives at the
critical order and the queries that see them at that order.

**Setting.** Finite queries `Q`, a finite set `S` of alternatives, and nonnegative information
`f i q l` along a filter (in the channel, `f_h(q,l) = h^{-2s} κ_q(w,l;h)` as `h → 0⁺`).
* The game value is `gval S f = sup_{α ∈ Δ(Q)} min_{l ∈ S} Σ_q α_q f q l`.
* `Crit ⊆ S` are the critical alternatives. On them the rescaled information converges to a
  finite `ĉ`.
* Off `Crit`, some query's rescaled information diverges (the alternative sits at a lower
  order).

**What is proved.**
* `critical_limit`: `gval S (f i) → gval Crit ĉ`. The limit and the max-min exchange because
  `Q` and `S` are finite. The lower side moves the maximiser toward uniform so that every fast
  alternative is seen.
* `expansion_hyps`: the per-query expansion `κ_q(l;h) = c_{q,l} h^{2 s_{q,l}} + o(h^{2 s_{q,l}})`,
  with `c_{q,l} > 0` or `κ_q(l;·) ≡ 0`, produces both hypotheses at the largest order
  `s = max_l ord l`. The critical coefficient is `c_{q,l}` when `s_{q,l} = s` and `0` otherwise.
  This is the order layer first and the coefficient layer second.
* `decision_limit`: with several safe answers, the rescaled decision value converges to the
  best critical game among the answers at the decision order. Answers at a higher order vanish.
* **The exponent does not fix the constant** (`private_game`, `shared_game`,
  `same_order_ratio`). Two channels with the same order `s` at every alternative:
  - one query per alternative (private) has `G* = 1/k`;
  - every query sees every alternative (shared) has `G* = 1`.
  So `Γ_shared(h)/Γ_private(h) → k`, the menu size. `s*` determines the exponent, not the
  characteristic complexity.
-/

namespace CIGAMF.P13.PaperBCriticalGame

open Finset Filter Topology

variable {Q L : Type*} [Fintype Q] [Nonempty Q]

/-- An allocation over the queries. -/
def Alloc (α : Q → ℝ) : Prop := (∀ q, 0 ≤ α q) ∧ ∑ q, α q = 1

/-- The inner value of an allocation: its worst alternative in `S`. -/
noncomputable def inner (S : Finset L) (hS : S.Nonempty) (f : Q → L → ℝ) (α : Q → ℝ) : ℝ :=
  S.inf' hS (fun l => ∑ q, α q * f q l)

/-- **The game value**: the best allocation's worst alternative. -/
noncomputable def gval (S : Finset L) (hS : S.Nonempty) (f : Q → L → ℝ) : ℝ :=
  sSup (inner S hS f '' {α | Alloc α})

/-- The uniform allocation. -/
noncomputable def unif : Q → ℝ := fun _ => 1 / (Fintype.card Q : ℝ)

theorem card_pos_real : (0 : ℝ) < Fintype.card Q := by exact_mod_cast Fintype.card_pos

theorem unif_alloc : Alloc (unif (Q := Q)) := by
  refine ⟨fun q => by unfold unif; positivity, ?_⟩
  unfold unif
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [card_pos_real.ne']

theorem alloc_le_one {α : Q → ℝ} (hα : Alloc α) (q : Q) : α q ≤ 1 := by
  rw [← hα.2]
  exact Finset.single_le_sum (f := α) (fun q _ => hα.1 q) (Finset.mem_univ q)

theorem image_nonempty (S : Finset L) (hS : S.Nonempty) (f : Q → L → ℝ) :
    (inner S hS f '' {α | Alloc α}).Nonempty :=
  ⟨_, unif, unif_alloc, rfl⟩

theorem inner_le_at (S : Finset L) (hS : S.Nonempty) (f : Q → L → ℝ) (α : Q → ℝ) (l : L)
    (hl : l ∈ S) : inner S hS f α ≤ ∑ q, α q * f q l :=
  Finset.inf'_le _ hl

theorem inner_bound (S : Finset L) (hS : S.Nonempty) (f : Q → L → ℝ) {α : Q → ℝ}
    (hα : Alloc α) : inner S hS f α ≤ ∑ q, |f q hS.choose| := by
  refine (inner_le_at S hS f α _ hS.choose_spec).trans ?_
  refine Finset.sum_le_sum fun q _ => ?_
  calc α q * f q hS.choose ≤ α q * |f q hS.choose| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (hα.1 q)
    _ ≤ 1 * |f q hS.choose| := mul_le_mul_of_nonneg_right (alloc_le_one hα q) (abs_nonneg _)
    _ = |f q hS.choose| := one_mul _

theorem image_bdd (S : Finset L) (hS : S.Nonempty) (f : Q → L → ℝ) :
    BddAbove (inner S hS f '' {α | Alloc α}) := by
  refine ⟨∑ q, |f q hS.choose|, ?_⟩
  rintro _ ⟨α, hα, rfl⟩
  exact inner_bound S hS f hα

theorem le_gval (S : Finset L) (hS : S.Nonempty) (f : Q → L → ℝ) {α : Q → ℝ} (hα : Alloc α) :
    inner S hS f α ≤ gval S hS f :=
  le_csSup (image_bdd S hS f) ⟨α, hα, rfl⟩

theorem gval_le (S : Finset L) (hS : S.Nonempty) (f : Q → L → ℝ) (B : ℝ)
    (h : ∀ α, Alloc α → inner S hS f α ≤ B) : gval S hS f ≤ B :=
  csSup_le (image_nonempty S hS f) (by rintro _ ⟨α, hα, rfl⟩; exact h α hα)

theorem inner_nonneg (S : Finset L) (hS : S.Nonempty) (f : Q → L → ℝ) (hf : ∀ q l, 0 ≤ f q l)
    {α : Q → ℝ} (hα : Alloc α) : 0 ≤ inner S hS f α :=
  Finset.le_inf' _ _ fun l _ => Finset.sum_nonneg fun q _ => mul_nonneg (hα.1 q) (hf q l)

theorem gval_nonneg (S : Finset L) (hS : S.Nonempty) (f : Q → L → ℝ) (hf : ∀ q l, 0 ≤ f q l) :
    0 ≤ gval S hS f :=
  (inner_nonneg S hS f hf unif_alloc).trans (le_gval S hS f unif_alloc)

/-- The mixture of an allocation with the uniform one. -/
noncomputable def mixU (β : ℝ) (α : Q → ℝ) : Q → ℝ := fun q => (1 - β) * α q + β * unif q

theorem mixU_alloc {α : Q → ℝ} (hα : Alloc α) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    Alloc (mixU β α) := by
  refine ⟨fun q => ?_, ?_⟩
  · unfold mixU
    have := hα.1 q
    have : 0 ≤ unif (Q := Q) q := unif_alloc.1 q
    have : 0 ≤ 1 - β := by linarith
    positivity
  · unfold mixU
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hα.2, unif_alloc.2]
    ring

/-! ## 1. The critical limit -/

/-- **The rescaled game converges to the critical game.** -/
theorem critical_limit {ι : Type*} {F : Filter ι} [F.NeBot] (S : Finset L) (hS : S.Nonempty)
    (Crit : Finset L) (hC : Crit.Nonempty) (hCS : Crit ⊆ S)
    (f : ι → Q → L → ℝ) (hf : ∀ i q l, 0 ≤ f i q l) (c : Q → L → ℝ) (hc : ∀ q l, 0 ≤ c q l)
    (hcrit : ∀ l ∈ Crit, ∀ q, Tendsto (fun i => f i q l) F (𝓝 (c q l)))
    (hfast : ∀ l ∈ S, l ∉ Crit → ∃ q, Tendsto (fun i => f i q l) F atTop) :
    Tendsto (fun i => gval S hS (f i)) F (𝓝 (gval Crit hC c)) := by
  classical
  set G := gval Crit hC c with hG
  have hG0 : 0 ≤ G := gval_nonneg Crit hC c hc
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- upper side: uniform closeness on the critical alternatives
  have hclose : ∀ᶠ i in F, ∀ l ∈ Crit, ∀ q, |f i q l - c q l| < ε / 4 := by
    rw [Filter.eventually_all_finset]
    intro l hl
    rw [Filter.eventually_all]
    intro q
    have := (hcrit l hl q)
    rw [Metric.tendsto_nhds] at this
    filter_upwards [this (ε / 4) (by positivity)] with i hi
    simpa [Real.dist_eq] using hi
  have hup : ∀ᶠ i in F, gval S hS (f i) ≤ G + ε / 4 := by
    filter_upwards [hclose] with i hi
    refine gval_le S hS (f i) _ fun α hα => ?_
    obtain ⟨l, hl, hle⟩ := Finset.exists_mem_eq_inf' hC (fun l => ∑ q, α q * c q l)
    have h1 : inner S hS (f i) α ≤ ∑ q, α q * f i q l := inner_le_at S hS (f i) α l (hCS hl)
    have h2 : ∑ q, α q * f i q l ≤ ∑ q, α q * c q l + ε / 4 := by
      have : ∑ q, α q * f i q l ≤ ∑ q, α q * (c q l + ε / 4) :=
        Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_left
          (by have := hi l hl q; rw [abs_lt] at this; linarith) (hα.1 q)
      calc _ ≤ _ := this
        _ = ∑ q, α q * c q l + (∑ q, α q) * (ε / 4) := by
            rw [Finset.sum_mul, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun q _ => by ring
        _ = _ := by rw [hα.2, one_mul]
    have h3 : ∑ q, α q * c q l ≤ G := by
      have : inner Crit hC c α = ∑ q, α q * c q l := by unfold inner; exact hle
      rw [← this]
      exact le_gval Crit hC c hα
    linarith
  -- lower side: a near-optimal critical allocation, moved toward uniform
  obtain ⟨_, ⟨α0, hα0, rfl⟩, hα0gt⟩ :=
    exists_lt_of_lt_csSup (image_nonempty Crit hC c) (show G - ε / 4 < G by linarith)
  set β : ℝ := min (1 / 2) (ε / (4 * (G + 1))) with hβ
  have hβ0 : 0 < β := lt_min (by norm_num) (by positivity)
  have hβ1 : β ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hβG : β * (G + 1) ≤ ε / 4 := by
    have := min_le_right (1 / 2 : ℝ) (ε / (4 * (G + 1)))
    calc β * (G + 1) ≤ ε / (4 * (G + 1)) * (G + 1) := mul_le_mul_of_nonneg_right this (by linarith)
      _ = ε / 4 := by field_simp
  set α1 := mixU β α0 with hα1
  have hα1a : Alloc α1 := mixU_alloc hα0 hβ0.le hβ1
  have hg0 : inner Crit hC c α0 ≤ G := le_gval Crit hC c hα0
  have hg0n : 0 ≤ inner Crit hC c α0 := inner_nonneg Crit hC c hc hα0
  have hcritval : ∀ l ∈ Crit, G - ε / 2 ≤ ∑ q, α1 q * c q l := by
    intro l hl
    have hmix : (1 - β) * ∑ q, α0 q * c q l ≤ ∑ q, α1 q * c q l := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun q _ => ?_
      unfold α1 mixU
      have hu := unif_alloc (Q := Q) |>.1 q
      have e : ((1 - β) * α0 q + β * unif q) * c q l
          = (1 - β) * (α0 q * c q l) + β * unif q * c q l := by ring
      rw [e]
      linarith [mul_nonneg (mul_nonneg hβ0.le hu) (hc q l)]
    have hat : inner Crit hC c α0 ≤ ∑ q, α0 q * c q l := inner_le_at Crit hC c α0 l hl
    have hb : β * inner Crit hC c α0 ≤ ε / 4 := by nlinarith
    nlinarith
  have hlow : ∀ᶠ i in F, ∀ l ∈ S, G - 3 * ε / 4 < ∑ q, α1 q * f i q l := by
    rw [Filter.eventually_all_finset]
    intro l hl
    by_cases hlc : l ∈ Crit
    · have ht : Tendsto (fun i => ∑ q, α1 q * f i q l) F (𝓝 (∑ q, α1 q * c q l)) :=
        tendsto_finsetSum _ fun q _ => (hcrit l hlc q).const_mul (α1 q)
      have := hcritval l hlc
      exact ht.eventually (lt_mem_nhds (by linarith))
    · obtain ⟨q0, hq0⟩ := hfast l hl hlc
      have hw : 0 < α1 q0 := by
        unfold α1 mixU unif
        have := hα0.1 q0
        have : 0 ≤ 1 - β := by linarith
        have : 0 < β * (1 / (Fintype.card Q : ℝ)) := mul_pos hβ0 (by
          have := card_pos_real (Q := Q); positivity)
        nlinarith
      have ht : Tendsto (fun i => α1 q0 * f i q0 l) F atTop := hq0.const_mul_atTop hw
      filter_upwards [ht.eventually_gt_atTop (G - 3 * ε / 4)] with i hi
      refine lt_of_lt_of_le hi ?_
      exact Finset.single_le_sum (f := fun q => α1 q * f i q l)
        (fun q _ => mul_nonneg (hα1a.1 q) (hf i q l)) (Finset.mem_univ q0)
  filter_upwards [hup, hlow] with i hi hl
  have hge : G - 3 * ε / 4 ≤ gval S hS (f i) := by
    refine le_trans ?_ (le_gval S hS (f i) hα1a)
    exact Finset.le_inf' _ _ fun l hlS => (hl l hlS).le
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-! ## 2. The expansion produces the hypotheses: order first, coefficient second -/

theorem pow_tendsto_zero (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (fun h : ℝ => h ^ k) (𝓝[>] 0) (𝓝 0) := by
  have h := ((continuous_pow k).tendsto (0 : ℝ))
  rw [zero_pow (by omega)] at h
  exact h.mono_left nhdsWithin_le_nhds

theorem inv_pow_tendsto_atTop (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (fun h : ℝ => (h ^ k)⁻¹) (𝓝[>] 0) atTop := by
  have h := (tendsto_pow_atTop (α := ℝ) (by omega : k ≠ 0)).comp tendsto_inv_nhdsGT_zero
  refine h.congr fun h => ?_
  simp [inv_pow]

/-- **From per-query expansions to the critical game's hypotheses.**
`κ_q(l;h)/h^{2 s_{q,l}} → c_{q,l}`, with `κ ≡ 0` where `c = 0`; `ord l` is the least order of a
visible query. At `s = max_l ord l`, a critical alternative's rescaled information converges to
`c` on the queries at order exactly `s` and to `0` elsewhere; a lower-order alternative's
diverges on its best query. -/
theorem expansion_hyps (sq : Q → L → ℕ) (c : Q → L → ℝ) (κ : ℝ → Q → L → ℝ)
    (hexp : ∀ q l, Tendsto (fun h => κ h q l / h ^ (2 * sq q l)) (𝓝[>] 0) (𝓝 (c q l)))
    (hvis : ∀ q l, c q l = 0 → ∀ h, κ h q l = 0) (hc0 : ∀ q l, 0 ≤ c q l)
    (ord : L → ℕ) (hbest : ∀ l, ∃ q, 0 < c q l ∧ sq q l = ord l)
    (hmin : ∀ l q, 0 < c q l → ord l ≤ sq q l) (s : ℕ) (hs : ∀ l, ord l ≤ s) :
    (∀ l, ord l = s → ∀ q, Tendsto (fun h => κ h q l / h ^ (2 * s)) (𝓝[>] 0)
        (𝓝 (if sq q l = s then c q l else 0)))
      ∧ ∀ l, ord l < s → ∃ q, Tendsto (fun h => κ h q l / h ^ (2 * s)) (𝓝[>] 0) atTop := by
  have hpos : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < h := self_mem_nhdsWithin
  refine ⟨fun l hl q => ?_, fun l hl => ?_⟩
  · by_cases hcq : c q l = 0
    · have h0 : (fun h => κ h q l / h ^ (2 * s)) = fun _ => 0 := by
        funext h; rw [hvis q l hcq h, zero_div]
      rw [h0]
      split_ifs
      · rw [hcq]; exact tendsto_const_nhds
      · exact tendsto_const_nhds
    · have hcp : 0 < c q l := lt_of_le_of_ne (hc0 q l) (Ne.symm hcq)
      have hge : s ≤ sq q l := hl ▸ hmin l q hcp
      have hsplit : ∀ᶠ h in 𝓝[>] (0 : ℝ), κ h q l / h ^ (2 * s)
          = κ h q l / h ^ (2 * sq q l) * h ^ (2 * (sq q l - s)) := by
        filter_upwards [hpos] with h hh
        have : h ^ (2 * sq q l) = h ^ (2 * s) * h ^ (2 * (sq q l - s)) := by
          rw [← pow_add]; congr 1; omega
        rw [this]
        have : h ^ (2 * (sq q l - s)) ≠ 0 := pow_ne_zero _ hh.ne'
        field_simp
      refine Tendsto.congr' (EventuallyEq.symm hsplit) ?_
      split_ifs with heq
      · refine (hexp q l).congr fun x => ?_
        rw [show sq q l - s = 0 by omega, mul_zero, pow_zero, mul_one]
      · have hk : 1 ≤ 2 * (sq q l - s) := by omega
        simpa using (hexp q l).mul (pow_tendsto_zero _ hk)
  · obtain ⟨q, hcq, hsq⟩ := hbest l
    refine ⟨q, ?_⟩
    have hsplit : ∀ᶠ h in 𝓝[>] (0 : ℝ), κ h q l / h ^ (2 * s)
        = κ h q l / h ^ (2 * sq q l) * (h ^ (2 * (s - sq q l)))⁻¹ := by
      filter_upwards [hpos] with h hh
      have : h ^ (2 * s) = h ^ (2 * sq q l) * h ^ (2 * (s - sq q l)) := by
        rw [← pow_add]; congr 1; omega
      rw [this]
      have : h ^ (2 * (s - sq q l)) ≠ 0 := pow_ne_zero _ hh.ne'
      have : h ^ (2 * sq q l) ≠ 0 := pow_ne_zero _ hh.ne'
      field_simp
    refine Tendsto.congr' (EventuallyEq.symm hsplit) ?_
    exact (hexp q l).pos_mul_atTop hcq (inv_pow_tendsto_atTop _ (by omega))

/-! ## 3. Several safe answers: the decision layer -/

theorem gval_le_sum_at (S : Finset L) (hS : S.Nonempty) (f : Q → L → ℝ) (hf : ∀ q l, 0 ≤ f q l)
    (l : L) (hl : l ∈ S) : gval S hS f ≤ ∑ q, f q l := by
  refine gval_le S hS f _ fun α hα => (inner_le_at S hS f α l hl).trans ?_
  refine Finset.sum_le_sum fun q _ => ?_
  calc α q * f q l ≤ 1 * f q l := mul_le_mul_of_nonneg_right (alloc_le_one hα q) (hf q l)
    _ = f q l := one_mul _

/-- **The decision limit.**  The safe answers split into critical ones (their games converge to
`gval (Crit a) c`) and slow ones (some alternative where the answer is unsafe has all its
rescaled information vanishing). The rescaled decision value, the best answer's game, converges
to the best critical game. -/
theorem decision_limit {Ans : Type*} {ι : Type*} {F : Filter ι} [F.NeBot]
    (safeA : Finset Ans) (critA : Finset Ans) (hcA : critA.Nonempty) (hsub : critA ⊆ safeA)
    (Alt : Ans → Finset L) (hAlt : ∀ a, (Alt a).Nonempty)
    (Crit : Ans → Finset L) (hCrit : ∀ a, (Crit a).Nonempty)
    (f : ι → Q → L → ℝ) (hf : ∀ i q l, 0 ≤ f i q l) (c : Q → L → ℝ) (hc : ∀ q l, 0 ≤ c q l)
    (hlim : ∀ a ∈ critA,
      Tendsto (fun i => gval (Alt a) (hAlt a) (f i)) F (𝓝 (gval (Crit a) (hCrit a) c)))
    (hslow : ∀ a ∈ safeA, a ∉ critA →
      ∃ l ∈ Alt a, ∀ q, Tendsto (fun i => f i q l) F (𝓝 0)) :
    Tendsto (fun i => safeA.sup' (hcA.mono hsub) (fun a => gval (Alt a) (hAlt a) (f i))) F
      (𝓝 (critA.sup' hcA (fun a => gval (Crit a) (hCrit a) c))) := by
  classical
  set Gd := critA.sup' hcA (fun a => gval (Crit a) (hCrit a) c) with hGd
  have hGd0 : 0 ≤ Gd := by
    obtain ⟨a, ha⟩ := hcA
    exact (gval_nonneg _ _ c hc).trans
      (Finset.le_sup' (f := fun a => gval (Crit a) (hCrit a) c) ha)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hcrit : ∀ᶠ i in F, ∀ a ∈ critA,
      |gval (Alt a) (hAlt a) (f i) - gval (Crit a) (hCrit a) c| < ε := by
    rw [Filter.eventually_all_finset]
    intro a ha
    have := (hlim a ha)
    rw [Metric.tendsto_nhds] at this
    filter_upwards [this ε hε] with i hi
    simpa [Real.dist_eq] using hi
  have hsl : ∀ᶠ i in F, ∀ a ∈ safeA, a ∉ critA → gval (Alt a) (hAlt a) (f i) < Gd + ε := by
    rw [Filter.eventually_all_finset]
    intro a ha
    by_cases hac : a ∈ critA
    · exact Filter.Eventually.of_forall fun i h => absurd hac h
    · obtain ⟨l, hl, hl0⟩ := hslow a ha hac
      have ht : Tendsto (fun i => ∑ q, f i q l) F (𝓝 0) := by
        simpa using tendsto_finsetSum (Finset.univ : Finset Q) fun q _ => hl0 q
      filter_upwards [ht.eventually (gt_mem_nhds (show (0 : ℝ) < Gd + ε by linarith))] with i hi
      exact fun _ => (gval_le_sum_at (Alt a) (hAlt a) (f i) (hf i) l hl).trans_lt hi
  filter_upwards [hcrit, hsl] with i hi hj
  obtain ⟨a0, ha0, hmax⟩ := Finset.exists_mem_eq_sup' hcA (fun a => gval (Crit a) (hCrit a) c)
  have hlow : Gd - ε < safeA.sup' (hcA.mono hsub) (fun a => gval (Alt a) (hAlt a) (f i)) := by
    have h1 := hi a0 ha0
    rw [abs_lt] at h1
    refine lt_of_lt_of_le ?_ (Finset.le_sup' (f := fun a => gval (Alt a) (hAlt a) (f i))
      (hsub ha0))
    rw [hGd, hmax]; linarith
  have hup : safeA.sup' (hcA.mono hsub) (fun a => gval (Alt a) (hAlt a) (f i)) < Gd + ε := by
    rw [Finset.sup'_lt_iff]
    intro a ha
    by_cases hac : a ∈ critA
    · have h1 := hi a hac
      rw [abs_lt] at h1
      have : gval (Crit a) (hCrit a) c ≤ Gd :=
        Finset.le_sup' (f := fun a => gval (Crit a) (hCrit a) c) hac
      linarith
    · exact hj a ha hac
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-! ## 4. The exponent does not fix the constant -/

theorem inner_smul (S : Finset L) (hS : S.Nonempty) (f : Q → L → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (α : Q → ℝ) : inner S hS (fun q l => t * f q l) α = t * inner S hS f α := by
  unfold inner
  apply le_antisymm
  · obtain ⟨l, hl, hle⟩ := Finset.exists_mem_eq_inf' hS (fun l => ∑ q, α q * f q l)
    refine (Finset.inf'_le _ hl).trans (le_of_eq ?_)
    rw [hle, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  · refine Finset.le_inf' _ _ fun l hl => ?_
    have : t * S.inf' hS (fun l => ∑ q, α q * f q l) ≤ t * ∑ q, α q * f q l :=
      mul_le_mul_of_nonneg_left (Finset.inf'_le _ hl) ht
    refine this.trans (le_of_eq ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring

/-- **The game is homogeneous.** -/
theorem gval_smul (S : Finset L) (hS : S.Nonempty) (f : Q → L → ℝ) (t : ℝ) (ht : 0 < t) :
    gval S hS (fun q l => t * f q l) = t * gval S hS f := by
  apply le_antisymm
  · refine gval_le S hS _ _ fun α hα => ?_
    rw [inner_smul S hS f t ht.le]
    exact mul_le_mul_of_nonneg_left (le_gval S hS f hα) ht.le
  · rw [← le_div_iff₀' ht]
    refine gval_le S hS f _ fun α hα => ?_
    rw [le_div_iff₀' ht, ← inner_smul S hS f t ht.le]
    exact le_gval S hS _ hα

variable (k : ℕ) [NeZero k]

/-- Private queries: query `q` sees only alternative `q`, with unit coefficient. -/
def privC : Fin k → Fin k → ℝ := fun q l => if q = l then 1 else 0

/-- Shared queries: every query sees every alternative, with unit coefficient. -/
def sharedC : Fin k → Fin k → ℝ := fun _ _ => 1

theorem inner_priv (α : Fin k → ℝ) (l : Fin k) : ∑ q, α q * privC k q l = α l := by
  unfold privC
  simp

/-- **The private critical game is `1/k`.** -/
theorem private_game :
    gval (Finset.univ : Finset (Fin k)) Finset.univ_nonempty (privC k) = 1 / k := by
  have hk : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  apply le_antisymm
  · refine gval_le _ _ _ _ fun α hα => ?_
    have hsum : ∑ l, α l ≤ ∑ _l : Fin k, (1 / (k : ℝ)) := by
      rw [hα.2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
      rfl
    obtain ⟨l, -, hl⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
    refine (inner_le_at _ _ _ α l (Finset.mem_univ l)).trans ?_
    rw [inner_priv]
    exact hl
  · refine le_trans (le_of_eq ?_) (le_gval _ _ (privC k) (unif_alloc (Q := Fin k)))
    unfold inner
    apply le_antisymm
    · refine Finset.le_inf' _ _ fun l _ => ?_
      rw [inner_priv]; unfold unif; simp
    · obtain ⟨l⟩ := (inferInstance : Nonempty (Fin k))
      refine (Finset.inf'_le _ (Finset.mem_univ l)).trans (le_of_eq ?_)
      rw [inner_priv]; unfold unif; simp

/-- **The shared critical game is `1`.** -/
theorem shared_game :
    gval (Finset.univ : Finset (Fin k)) Finset.univ_nonempty (sharedC k) = 1 := by
  have hin : ∀ α : Fin k → ℝ, Alloc α →
      inner (Finset.univ : Finset (Fin k)) Finset.univ_nonempty (sharedC k) α = 1 := by
    intro α hα
    unfold inner sharedC
    simp only [mul_one, hα.2]
    exact Finset.inf'_const _ _
  apply le_antisymm
  · exact gval_le _ _ _ _ fun α hα => (hin α hα).le
  · rw [← hin unif unif_alloc]; exact le_gval _ _ _ unif_alloc

/-- **Same order, constants a factor `k` apart.**  Both channels put every alternative at order
`s` exactly, with unit coefficient on the queries that see it:
`κ^priv_h(q,l) = h^{2s} [q = l]` and `κ^sh_h(q,l) = h^{2s}`. For every `h > 0` the shared game is
`h^{2s}`, the private one `h^{2s}/k`. -/
theorem same_order_ratio (s : ℕ) (h : ℝ) (hh : 0 < h) :
    gval (Finset.univ : Finset (Fin k)) Finset.univ_nonempty
        (fun q l => h ^ (2 * s) * privC k q l) = h ^ (2 * s) / k
      ∧ gval (Finset.univ : Finset (Fin k)) Finset.univ_nonempty
        (fun q l => h ^ (2 * s) * sharedC k q l) = h ^ (2 * s)
      ∧ gval (Finset.univ : Finset (Fin k)) Finset.univ_nonempty
        (fun q l => h ^ (2 * s) * sharedC k q l)
        = k * gval (Finset.univ : Finset (Fin k)) Finset.univ_nonempty
          (fun q l => h ^ (2 * s) * privC k q l) := by
  have hk : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  have hp : 0 < h ^ (2 * s) := pow_pos hh _
  rw [gval_smul _ _ _ _ hp, gval_smul _ _ _ _ hp, private_game, shared_game]
  refine ⟨by ring, by ring, ?_⟩
  field_simp

#print axioms critical_limit
#print axioms expansion_hyps
#print axioms decision_limit
#print axioms gval_smul
#print axioms private_game
#print axioms shared_game
#print axioms same_order_ratio

end CIGAMF.P13.PaperBCriticalGame
