import «LeanPaperA7EtaV1»

/-!
# Paper A7: the accumulation chain, composed end to end

The five links of the A-END argument were each proved, and each was proved in isolation:
`stopping_subset_window_failure` (accumulation to inclusion), `sqrt_window_tail`
(inclusion to tail), `expected_stopping_bound_general` (tail to expectation) and
`rate_limsup_eta` (expectation to rate).  Nothing joined them, so the expected bound that
`rate_limsup_eta` consumes was an assumption of the development rather than a conclusion
of it.  This module supplies that bound from algorithm-level hypotheses.

Joining the links exposes a cost that isolation hid.  The inclusion needs the threshold to
sit strictly below `G t - 2 Gamma n - C` at the window `n = ceil(sqrt t)`, so the head of
the window has to be paid for; at budget `b` the crossing time is NOT `b/G + O(1)` but
`b/G + O(sqrt b)`.  Rather than hide that in an asymptotic, it is paid here with an
explicit split: for any `eps` in `(0,1)`,

    2 Gamma sqrt t  <=  eps G t + Gamma^2/(eps G),

so the window head costs a factor `(1 - eps)` of the rate and an additive
`Gamma^2/(eps G)` of the budget, both explicit.  `winBudget` collects the constant, and
the `14 (1-eps) G` summand inside it is what forces the crossing time past `16`, which is
where the `sqrt t` window is admissible at all.

The result is that the rate is `1/((1-eps) Gamma)` for every `eps > 0`, not `1/Gamma`;
combined with `eta_to_zero` this is the same `Gamma - eta` family the rest of A7 lives in.
The clean rate `1/Gamma` is still not proved, and this module does not claim it.
-/

namespace CIGAMF.P13.PaperA7Chain

open MeasureTheory
open CIGAMF.P13.PaperA7Tail
open CIGAMF.P13.PaperA7Eta

/-- The additive budget the window head costs, at splitting parameter `eps`. -/
noncomputable def winBudget (Γ G C ε : ℝ) : ℝ :=
  C + 2 * Γ + Γ ^ 2 / (ε * G) + 14 * ((1 - ε) * G)

theorem winBudget_nonneg (Γ G C ε : ℝ) (hG : 0 < G) (hε : 0 < ε) (hε1 : ε < 1)
    (hΓ : 0 ≤ Γ) (hC : 0 ≤ C) : 0 ≤ winBudget Γ G C ε := by
  unfold winBudget
  have h1 : 0 ≤ Γ ^ 2 / (ε * G) := by positivity
  have h2 : 0 ≤ 14 * ((1 - ε) * G) := by nlinarith
  linarith

/-- **The square-root split.**  The window head is linear in `t` at any rate `eps G`, at
the cost of an additive `Gamma^2/(eps G)`.  This is the only inequality in the chain that
was not already available, and it is where the `(1 - eps)` in the rate comes from. -/
theorem sqrt_head_split_aux (Γ G ε u : ℝ) (hG : 0 < G) (hε : 0 < ε) (hu : 0 ≤ u) :
    2 * Γ * u ≤ ε * G * u ^ 2 + Γ ^ 2 / (ε * G) := by
  have hεG : 0 < ε * G := mul_pos hε hG
  have hkey : ε * G * u ^ 2 + Γ ^ 2 / (ε * G) - 2 * Γ * u
      = (ε * G * u - Γ) ^ 2 / (ε * G) := by
    field_simp; ring
  have hnn : 0 ≤ (ε * G * u - Γ) ^ 2 / (ε * G) := by positivity
  linarith

theorem sqrt_head_split (Γ G ε : ℝ) (t : ℕ) (hG : 0 < G) (hε : 0 < ε) :
    2 * Γ * Real.sqrt t ≤ ε * G * t + Γ ^ 2 / (ε * G) := by
  have h := sqrt_head_split_aux Γ G ε (Real.sqrt t) hG hε (Real.sqrt_nonneg _)
  rwa [Real.sq_sqrt (by positivity : (0:ℝ) ≤ (t : ℝ))] at h

/-- **The crossing time.**  Past `ceil(b'/((1-eps) G)) + 2`, where `b'` is the budget plus
`winBudget`, the threshold is strictly below the accumulation floor at the `sqrt t` window.
This is the hypothesis `stopping_subset_window_failure` needs, now discharged. -/
theorem window_crossing (Γ G C b ε : ℝ) (t : ℕ)
    (hG : 0 < G) (hε : 0 < ε) (hε1 : ε < 1) (hΓ : 0 ≤ Γ) (hC : 0 ≤ C) (hb : 0 ≤ b)
    (ht : ⌈(b + winBudget Γ G C ε) / ((1 - ε) * G)⌉₊ + 2 ≤ t) :
    b < G * t - 2 * Γ * (⌈Real.sqrt t⌉₊ : ℝ) - C := by
  have hG' : 0 < (1 - ε) * G := mul_pos (by linarith) hG
  have hbk : 0 ≤ b + winBudget Γ G C ε :=
    add_nonneg hb (winBudget_nonneg Γ G C ε hG hε hε1 hΓ hC)
  have hceil : ((b + winBudget Γ G C ε) / ((1 - ε) * G)) ≤ (⌈(b + winBudget Γ G C ε) / ((1 - ε) * G)⌉₊ : ℝ) :=
    Nat.le_ceil _
  have htR : ((⌈(b + winBudget Γ G C ε) / ((1 - ε) * G)⌉₊ : ℝ)) + 2 ≤ (t : ℝ) := by
    have : ((⌈(b + winBudget Γ G C ε) / ((1 - ε) * G)⌉₊ + 2 : ℕ) : ℝ) ≤ (t : ℝ) := by
      exact_mod_cast ht
    push_cast at this; linarith
  have hlin : b + winBudget Γ G C ε + 2 * ((1 - ε) * G) ≤ (1 - ε) * G * t := by
    have h1 : (b + winBudget Γ G C ε) / ((1 - ε) * G) + 2 ≤ (t : ℝ) := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hG'.le
    rw [mul_add, mul_div_cancel₀ _ (ne_of_gt hG')] at h2
    linarith
  have hsq : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
  have hcl : (⌈Real.sqrt t⌉₊ : ℝ) ≤ Real.sqrt t + 1 :=
    le_of_lt (Nat.ceil_lt_add_one hsq)
  have hhead : 2 * Γ * (⌈Real.sqrt t⌉₊ : ℝ) ≤ ε * G * t + Γ ^ 2 / (ε * G) + 2 * Γ := by
    have h1 : 2 * Γ * (⌈Real.sqrt t⌉₊ : ℝ) ≤ 2 * Γ * (Real.sqrt t + 1) := by nlinarith
    have h2 := sqrt_head_split Γ G ε t hG hε
    nlinarith
  have hG14 : 0 < 14 * ((1 - ε) * G) := by linarith
  unfold winBudget at hlin
  nlinarith [hlin, hhead]

/-- **The tail, from the algorithm's own hypotheses.**  Composing the crossing time with
`stopping_subset_window_failure` and `sqrt_window_tail`. -/
theorem chain_tail_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (good : ℕ → Set Ω) (z Z thr : Ω → ℕ → ℝ) (τ : Ω → ℕ)
    (Γ G C b ε : ℝ) (hG : 0 < G) (hε : 0 < ε) (hε1 : ε < 1)
    (hΓ : 0 ≤ Γ) (hGΓ : G ≤ Γ) (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hstep : ∀ s, (μ (good s)ᶜ).toReal ≤ 1 / (s : ℝ) ^ 4)
    (hτ : ∀ ω s, thr ω s < Z ω s → τ ω ≤ s)
    (hhead : ∀ ω s, -Γ ≤ z ω s)
    (hgood : ∀ ω s, ω ∈ good s → G ≤ z ω s)
    (hinit : ∀ ω t, (∑ s ∈ Finset.range t, z ω s) - C ≤ Z ω t)
    (hthr : ∀ ω t, thr ω t ≤ b)
    (t : ℕ) (ht16 : 16 ≤ t)
    (ht : ⌈(b + winBudget Γ G C ε) / ((1 - ε) * G)⌉₊ + 2 ≤ t) :
    (μ {ω | t < τ ω}).toReal ≤ 8 / (Real.sqrt t) ^ 3 := by
  obtain ⟨hn2, hnt, _⟩ := sqrt_window_admissible t ht16
  have hcross : b < G * t - 2 * Γ * (⌈Real.sqrt t⌉₊ : ℝ) - C :=
    window_crossing Γ G C b ε t hG hε hε1 hΓ hC hb ht
  have hsub : {ω | t < τ ω} ⊆ ⋃ s ∈ Finset.Ico ⌈Real.sqrt t⌉₊ t, (good s)ᶜ :=
    stopping_subset_window_failure good z Z thr τ t ⌈Real.sqrt t⌉₊ hnt (by omega) Γ G C
      hΓ hGΓ hC hτ (fun ω s _ => hhead ω s) (fun ω s _ _ hs => hgood ω s hs)
      (fun ω => hinit ω t) (fun ω => lt_of_le_of_lt (hthr ω t) hcross)
  exact sqrt_window_tail μ good τ t ht16 hsub hstep

/-- **The expectation bound, with the tail required only past the head.**  Identical to
`expected_stopping_bound_general` except that `p` is bounded only where the sum sees it;
the window bound is unavailable below `16`, so the `forall t` form cannot be used. -/
theorem expected_stopping_bound_window
    (Esum p : ℕ → ℝ) (G b : ℝ) (hG : 0 < G) (hb : 0 ≤ b)
    (hp : ∀ t, ⌈b / G⌉₊ + 2 ≤ t → p t ≤ 8 / (Real.sqrt t) ^ 3)
    (hEsum : ∀ M, Esum M ≤ ((⌈b / G⌉₊ + 2 : ℕ) : ℝ)
        + ∑ t ∈ Finset.Ico (⌈b / G⌉₊ + 2) M, p t) :
    ∀ M, Esum M ≤ b / G + 19 := by
  intro M
  set t0 : ℕ := ⌈b / G⌉₊ + 2 with ht0
  have ht02 : 2 ≤ t0 := by omega
  have hdiv : 0 ≤ b / G := div_nonneg hb (le_of_lt hG)
  have hceil : (⌈b / G⌉₊ : ℝ) ≤ b / G + 1 := le_of_lt (Nat.ceil_lt_add_one hdiv)
  have ht0R : (t0 : ℝ) ≤ b / G + 3 := by rw [ht0]; push_cast; linarith
  have hsum : ∑ t ∈ Finset.Ico t0 M, p t ≤ 16 / Real.sqrt ((t0 : ℝ) - 1) :=
    le_trans (Finset.sum_le_sum (fun t ht => hp t (Finset.mem_Ico.mp ht).1))
      (sqrt_tail_sum_le t0 M ht02)
  have ht01 : (1 : ℝ) ≤ (t0 : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (t0 : ℝ) := by exact_mod_cast ht02
    linarith
  have hs1 : (1 : ℝ) ≤ Real.sqrt ((t0 : ℝ) - 1) := by
    have h1 : Real.sqrt 1 ≤ Real.sqrt ((t0 : ℝ) - 1) := Real.sqrt_le_sqrt ht01
    rwa [Real.sqrt_one] at h1
  have h16 : 16 / Real.sqrt ((t0 : ℝ) - 1) ≤ 16 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  linarith [hEsum M, hsum, ht0R, h16]

/-- **The head is past 16.**  The `14 (1-eps) G` inside `winBudget` is exactly what makes
the `sqrt t` window admissible at every `t` the tail sum sees. -/
theorem crossing_past_sixteen (Γ G C b ε : ℝ) (hG : 0 < G) (hε : 0 < ε) (hε1 : ε < 1)
    (hΓ : 0 ≤ Γ) (hC : 0 ≤ C) (hb : 0 ≤ b) :
    16 ≤ ⌈(b + winBudget Γ G C ε) / ((1 - ε) * G)⌉₊ + 2 := by
  have hG' : 0 < (1 - ε) * G := mul_pos (by linarith) hG
  have h14 : 14 * ((1 - ε) * G) ≤ b + winBudget Γ G C ε := by
    unfold winBudget
    have h1 : 0 ≤ Γ ^ 2 / (ε * G) := by positivity
    linarith
  have hge : (14 : ℝ) ≤ (b + winBudget Γ G C ε) / ((1 - ε) * G) := by
    rw [le_div_iff₀ hG']; linarith
  have : (14 : ℝ) ≤ (⌈(b + winBudget Γ G C ε) / ((1 - ε) * G)⌉₊ : ℝ) :=
    le_trans hge (Nat.le_ceil _)
  have h14N : 14 ≤ ⌈(b + winBudget Γ G C ε) / ((1 - ε) * G)⌉₊ := by exact_mod_cast this
  omega

/-- **The chain, at one confidence level.**  From the tracking head bound, the per-round
gain on the confidence events, the `s^{-4}` confidence step and a threshold below `b`, the
truncated expectations obey `(b + winBudget)/((1-eps) Gamma) + 19`.  This is the bound
`rate_limsup_eta` asks for, now derived. -/
theorem chain_expected_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ]
    (good : ℕ → Set Ω) (z Z thr : Ω → ℕ → ℝ) (τ : Ω → ℕ) (Esum : ℕ → ℝ)
    (Γ G C b ε : ℝ) (hG : 0 < G) (hε : 0 < ε) (hε1 : ε < 1)
    (hΓ : 0 ≤ Γ) (hGΓ : G ≤ Γ) (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hstep : ∀ s, (μ (good s)ᶜ).toReal ≤ 1 / (s : ℝ) ^ 4)
    (hτ : ∀ ω s, thr ω s < Z ω s → τ ω ≤ s)
    (hhead : ∀ ω s, -Γ ≤ z ω s)
    (hgood : ∀ ω s, ω ∈ good s → G ≤ z ω s)
    (hinit : ∀ ω t, (∑ s ∈ Finset.range t, z ω s) - C ≤ Z ω t)
    (hthr : ∀ ω t, thr ω t ≤ b)
    (hEsum : ∀ M, Esum M
        ≤ ((⌈(b + winBudget Γ G C ε) / ((1 - ε) * G)⌉₊ + 2 : ℕ) : ℝ)
          + ∑ t ∈ Finset.Ico (⌈(b + winBudget Γ G C ε) / ((1 - ε) * G)⌉₊ + 2) M,
              (μ {ω | t < τ ω}).toReal) :
    ∀ M, Esum M ≤ (b + winBudget Γ G C ε) / ((1 - ε) * G) + 19 := by
  have hG' : 0 < (1 - ε) * G := mul_pos (by linarith) hG
  have hbk : 0 ≤ b + winBudget Γ G C ε :=
    add_nonneg hb (winBudget_nonneg Γ G C ε hG hε hε1 hΓ hC)
  have h16 := crossing_past_sixteen Γ G C b ε hG hε hε1 hΓ hC hb
  refine expected_stopping_bound_window Esum
    (fun t => (μ {ω | t < τ ω}).toReal) ((1 - ε) * G) (b + winBudget Γ G C ε)
    hG' hbk (fun t ht => ?_) hEsum
  exact chain_tail_bound μ good z Z thr τ Γ G C b ε hG hε hε1 hΓ hGΓ hC hb hstep hτ
    hhead hgood hinit hthr t (by omega) ht

/-- **The chain, all the way to the rate.**  With the threshold at `log(1/alpha) + s(alpha)`
and `s` small against `log(1/alpha)`, the expected stopping time divided by `log(1/alpha)`
is eventually within `epsr` of `1/((1-eps) Gamma)`.  Every constant is explicit and the
`(1-eps)` is the window head's price. -/
theorem a7_chain_rate {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (good : ℝ → ℕ → Set Ω) (z Z thr : ℝ → Ω → ℕ → ℝ) (τ : ℝ → Ω → ℕ)
    (Esum : ℝ → ℕ → ℝ) (Eτ s : ℝ → ℝ)
    (Γ G C ε : ℝ) (hG : 0 < G) (hε : 0 < ε) (hε1 : ε < 1)
    (hΓ : 0 ≤ Γ) (hGΓ : G ≤ Γ) (hC : 0 ≤ C)
    (hs : ∀ α, 0 ≤ s α)
    (hstep : ∀ α n, (μ (good α n)ᶜ).toReal ≤ 1 / (n : ℝ) ^ 4)
    (hτ : ∀ α ω n, thr α ω n < Z α ω n → τ α ω ≤ n)
    (hhead : ∀ α ω n, -Γ ≤ z α ω n)
    (hgood : ∀ α ω n, ω ∈ good α n → G ≤ z α ω n)
    (hinit : ∀ α ω n, (∑ r ∈ Finset.range n, z α ω r) - C ≤ Z α ω n)
    (hthr : ∀ α ω n, thr α ω n ≤ Real.log (1 / α) + s α)
    (hEsumα : ∀ α M, Esum α M
        ≤ ((⌈(Real.log (1 / α) + s α + winBudget Γ G C ε) / ((1 - ε) * G)⌉₊ + 2 : ℕ) : ℝ)
          + ∑ t ∈ Finset.Ico
              (⌈(Real.log (1 / α) + s α + winBudget Γ G C ε) / ((1 - ε) * G)⌉₊ + 2) M,
              (μ {ω | t < τ α ω}).toReal)
    (hsup : ∀ α y, (∀ M, Esum α M ≤ y) → Eτ α ≤ y)
    (εr α0 : ℝ) (hα0 : 0 < α0) (hα01 : α0 < 1)
    (hsmall : ∀ α, 0 < α → α < α0 →
        0 < Real.log (1 / α) ∧
        (s α + winBudget Γ G C ε) + 19 * ((1 - ε) * G)
          ≤ εr * ((1 - ε) * G) * Real.log (1 / α)) :
    ∀ α, 0 < α → α < α0 → Eτ α / Real.log (1 / α) ≤ 1 / ((1 - ε) * G) + εr := by
  have hG' : 0 < (1 - ε) * G := mul_pos (by linarith) hG
  have hbound : ∀ α, 0 < α → α < 1 →
      Eτ α ≤ (Real.log (1 / α) + (s α + winBudget Γ G C ε)) / ((1 - ε) * G) + 19 := by
    intro α hα hα1
    have hlog : 0 ≤ Real.log (1 / α) := by
      refine Real.log_nonneg ?_
      rw [le_div_iff₀ hα]; linarith
    have hb : 0 ≤ Real.log (1 / α) + s α := add_nonneg hlog (hs α)
    have hchain := chain_expected_bound μ (good α) (z α) (Z α) (thr α) (τ α) (Esum α)
      Γ G C (Real.log (1 / α) + s α) ε hG hε hε1 hΓ hGΓ hC hb (hstep α) (hτ α)
      (hhead α) (hgood α) (hinit α) (hthr α) (hEsumα α)
    refine hsup α _ (fun M => ?_)
    have := hchain M
    have harg : Real.log (1 / α) + s α + winBudget Γ G C ε
        = Real.log (1 / α) + (s α + winBudget Γ G C ε) := by ring
    rwa [harg] at this
  exact rate_limsup_eta Eτ (fun α => s α + winBudget Γ G C ε) ((1 - ε) * G) 19 hG'
    hbound εr α0 hα0 hα01 hsmall

/-- **What the chain does not give.**  The rate is `1/((1-eps) Gamma)`, and `eps` cannot be
set to zero inside the argument: at `eps = 0` the split `2 Gamma sqrt t <= eps G t + ...`
carries an infinite constant.  `eta_to_zero` converts the family into an arbitrarily small
loss, which is a statement about the family and not about any single run. -/
theorem chain_rate_is_deficient (Γ ε : ℝ) (hΓ : 0 < Γ) (hε : 0 < ε) (hε1 : ε < 1) :
    1 / Γ < 1 / ((1 - ε) * Γ) := by
  have h1 : 0 < (1 - ε) * Γ := mul_pos (by linarith) hΓ
  rw [div_lt_div_iff₀ hΓ h1]
  nlinarith

/-! ## Audit -/

#print axioms sqrt_head_split_aux
#print axioms sqrt_head_split
#print axioms window_crossing
#print axioms chain_tail_bound
#print axioms expected_stopping_bound_window
#print axioms crossing_past_sixteen
#print axioms chain_expected_bound
#print axioms a7_chain_rate
#print axioms chain_rate_is_deficient

end CIGAMF.P13.PaperA7Chain
