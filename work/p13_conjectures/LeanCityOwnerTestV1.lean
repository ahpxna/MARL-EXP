import Mathlib

/-!
# Owner-side tests of a learned signal's response, and why per-vehicle A/B tests mislead (city track, W22, 17/10/2026)

Companion of PROTOCOL_CITY_WAVE22_20261017 (ledger C-256 .. C-259).  Four small results used to read the W22 experiments.

## WHAT IS PROVED
1. **Length-biased pooling (the W22-A estimator artefact, C-259).**  Windows `i ∈ s` hold `n i > 0` greens of mean duration `m i`.
   * `pooled_le_winMean` — if `n` and `m` antivary (windows with longer greens hold fewer greens), the green-count-weighted mean
     `(∑ n m) / (∑ n)` is at most the window-weighted mean `(∑ m) / #s` (Chebyshev's sum inequality).
   * `tiling_antivary`, `length_biased` — this holds whenever greens tile a window of fixed length, `n i = L / (m i + c)` with `L, c > 0`.
   * `pooled_singleton`, `estimator_le_window_contrast` — a single control window's pooled mean is its own mean, so the registered
     per-signal-day contrast (pooled treated mean minus one control window) is at most the window-weighted contrast: it is biased
     downward exactly when control windows are rare (one per signal-day), as at a forgone share of 0.05.
   * `pooled_eq_of_const` — no bias when every window has the same mean.
2. **The A/B accounting identity.**  `ab_identity`: (treated − control, at share p) − (all treated − none treated) equals
   (treated at p − all treated) − (control at p − none treated).  `ab_understates_iff`, `ab_overstates_iff`: the per-vehicle test
   understates the global effect iff the treated vehicles' spillover is below the control vehicles' spillover, and overstates iff above.
3. **Design-dependence of a switchback under a concave exposure response.**  A window's response is `g` of its exposure; the own
   treatment contributes `a ∈ [0, 1]` and the background (others treated with probability p) contributes `(1 − a) p`.
   * `increment_antitone` — for `g` concave on `[0, 1]`, the increment `g (x + h) − g x` is antitone in `x`.
   * `delta_antitone` — the switchback contrast `Δ(p) = g (a + (1 − a) p) − g ((1 − a) p)` is antitone in p: a design with rarer control
     windows estimates a smaller effect; `delta_detect_mono`: what a design with share p fails to detect, no design with a larger share
     detects.
   * `bracket` — with `g 0 = 0`: `Δ(1) ≤ a · g 1 ≤ Δ(0)`.   `delta_linear` — an additive (linear) response gives `Δ(p) = κ a` at every p.
4. **Cost and time of the owner's switchback** (Bernoulli design, per-day information `p (1 − p)`, additive per-window benefit).
   * `total_cost_eq` — total benefit forgone until a fixed precision, `(1 − p) B · c / (p (1 − p)) = c B / p`;
     `total_cost_antitone` — it falls as the treated share rises, while `days_min` — the days needed are at least `4 c`, attained at 1/2.
5. `hyps_satisfiable` — every hypothesis set is met: a two-window tiling (pooled 55/4 < 15), `id` and `√` as concave responses with
   `g 0 = 0`, and A/B spillovers of both signs (the W22-B values for MPLight and AH).

## WHAT THIS DOES NOT ESTABLISH
* That SUMO windows tile exactly (`n = L / (m + c)` with a constant `c`): yellows, all-reds and window edges make it approximate; the
  inequality is applied as an explanation, checked numerically by the re-analysis (E1 vs E2 – E4), not proved for the simulator.
* Any statement in expectation: (1) is deterministic per window set.  That the expected per-day contrast is negative under no effect
  needs the control window to be a draw from the same window distribution, which the Bernoulli design provides but is not formalised.
* That the real exposure response is concave: the corrected estimates are nearly flat in p (C-259), consistent with (3) only in its
  additive case.  The variance model in (4) is the standard independent-window approximation, not derived for correlated windows.
-/

namespace CIGAMF.P13.CityOwnerTestV1

open Finset

/-! ## 1. Length-biased pooling -/

/-- Green-count-weighted mean duration over the windows `s`. -/
noncomputable def pooled {ι : Type*} (s : Finset ι) (n m : ι → ℝ) : ℝ := (∑ i ∈ s, n i * m i) / ∑ i ∈ s, n i

/-- Window-weighted mean duration over the windows `s`. -/
noncomputable def winMean {ι : Type*} (s : Finset ι) (m : ι → ℝ) : ℝ := (∑ i ∈ s, m i) / (s.card : ℝ)

theorem pooled_le_winMean {ι : Type*} {s : Finset ι} {n m : ι → ℝ} (hs : s.Nonempty)
    (hn : ∀ i ∈ s, 0 < n i) (hanti : AntivaryOn n m s) : pooled s n m ≤ winMean s m := by
  have hcard : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast hs.card_pos
  have hsum : 0 < ∑ i ∈ s, n i := Finset.sum_pos hn hs
  have hc := hanti.card_mul_sum_le_sum_mul_sum
  unfold pooled winMean
  rw [div_le_div_iff₀ hsum hcard]
  calc (∑ i ∈ s, n i * m i) * (s.card : ℝ) = (s.card : ℝ) * ∑ i ∈ s, n i * m i := mul_comm _ _
    _ ≤ (∑ i ∈ s, n i) * ∑ i ∈ s, m i := hc
    _ = (∑ i ∈ s, m i) * ∑ i ∈ s, n i := mul_comm _ _

theorem tiling_antivary {ι : Type*} {s : Finset ι} {m : ι → ℝ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (hm : ∀ i ∈ s, 0 ≤ m i) : AntivaryOn (fun i => L / (m i + c)) m s := by
  intro i hi j _hj hij
  have hi' : 0 < m i + c := by linarith [hm i (Finset.mem_coe.1 hi)]
  exact div_le_div_of_nonneg_left hL.le hi' (by linarith)

theorem length_biased {ι : Type*} {s : Finset ι} {m : ι → ℝ} {L c : ℝ} (hs : s.Nonempty) (hL : 0 < L) (hc : 0 < c)
    (hm : ∀ i ∈ s, 0 ≤ m i) : pooled s (fun i => L / (m i + c)) m ≤ winMean s m :=
  pooled_le_winMean hs (fun i hi => div_pos hL (by linarith [hm i hi])) (tiling_antivary hL hc hm)

theorem pooled_singleton {ι : Type*} (i0 : ι) {n m : ι → ℝ} (hn : n i0 ≠ 0) : pooled {i0} n m = m i0 := by
  unfold pooled; simp only [Finset.sum_singleton]; field_simp

theorem estimator_le_window_contrast {ι : Type*} {sT : Finset ι} {n m : ι → ℝ} (i0 : ι) (hs : sT.Nonempty)
    (hn : ∀ i ∈ sT, 0 < n i) (hanti : AntivaryOn n m sT) (hn0 : n i0 ≠ 0) :
    pooled sT n m - pooled {i0} n m ≤ winMean sT m - m i0 := by
  rw [pooled_singleton i0 hn0]; exact sub_le_sub_right (pooled_le_winMean hs hn hanti) _

theorem pooled_eq_of_const {ι : Type*} {s : Finset ι} {n m : ι → ℝ} {μ : ℝ} (hs : s.Nonempty)
    (hn : ∀ i ∈ s, 0 < n i) (hm : ∀ i ∈ s, m i = μ) : pooled s n m = μ ∧ winMean s m = μ := by
  have hsum : 0 < ∑ i ∈ s, n i := Finset.sum_pos hn hs
  have hcard : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast hs.card_pos
  constructor
  · unfold pooled
    rw [Finset.sum_congr rfl (fun i hi => by rw [hm i hi]), ← Finset.sum_mul]; field_simp
  · unfold winMean
    rw [Finset.sum_congr rfl hm, Finset.sum_const, nsmul_eq_mul]; field_simp

/-! ## 2. The A/B accounting identity -/

theorem ab_identity (Tp Cp T1 C0 : ℝ) : (Tp - Cp) - (T1 - C0) = (Tp - T1) - (Cp - C0) := by ring

theorem ab_understates_iff (Tp Cp T1 C0 : ℝ) : Tp - Cp < T1 - C0 ↔ Tp - T1 < Cp - C0 := by
  constructor <;> intro h <;> linarith

theorem ab_overstates_iff (Tp Cp T1 C0 : ℝ) : T1 - C0 < Tp - Cp ↔ Cp - C0 < Tp - T1 := by
  constructor <;> intro h <;> linarith

theorem ab_unbiased_of_no_spill {Tp Cp T1 C0 : ℝ} (hT : Tp = T1) (hC : Cp = C0) : Tp - Cp = T1 - C0 := by rw [hT, hC]

/-! ## 3. Design-dependence under a concave exposure response -/

theorem increment_antitone {g : ℝ → ℝ} (hg : ConcaveOn ℝ (Set.Icc 0 1) g) {x y h : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (hh : 0 ≤ h) (hyh : y + h ≤ 1) :
    g (y + h) - g y ≤ g (x + h) - g x := by
  rcases eq_or_lt_of_le hh with rfl | hh'
  · simp
  have hDpos : 0 < y + h - x := by linarith
  have hD : y + h - x ≠ 0 := hDpos.ne'
  have hl0 : 0 ≤ h / (y + h - x) := div_nonneg hh hDpos.le
  have hl1 : h / (y + h - x) ≤ 1 := by rw [div_le_one hDpos]; linarith
  have mx : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx, by linarith⟩
  have my : y + h ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, hyh⟩
  have e1 : (1 - h / (y + h - x)) * x + h / (y + h - x) * (y + h) = x + h := by field_simp; ring
  have e2 : h / (y + h - x) * x + (1 - h / (y + h - x)) * (y + h) = y := by field_simp; ring
  have c1 := hg.2 mx my (by linarith : (0 : ℝ) ≤ 1 - h / (y + h - x)) hl0 (by ring)
  have c2 := hg.2 mx my hl0 (by linarith : (0 : ℝ) ≤ 1 - h / (y + h - x)) (by ring)
  simp only [smul_eq_mul] at c1 c2
  rw [e1] at c1; rw [e2] at c2
  have h3 : (1 - h / (y + h - x)) * g x + h / (y + h - x) * g (y + h)
      + (h / (y + h - x) * g x + (1 - h / (y + h - x)) * g (y + h)) = g x + g (y + h) := by ring
  linarith [c1, c2, h3]

/-- The switchback contrast at treated share `p`: own weight `a`, background weight `1 - a`. -/
noncomputable def delta (g : ℝ → ℝ) (a p : ℝ) : ℝ := g (a + (1 - a) * p) - g ((1 - a) * p)

theorem delta_antitone {g : ℝ → ℝ} (hg : ConcaveOn ℝ (Set.Icc 0 1) g) {a p q : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1) : delta g a q ≤ delta g a p := by
  unfold delta
  have h1a : 0 ≤ 1 - a := by linarith
  have hx : 0 ≤ (1 - a) * p := mul_nonneg h1a hp
  have hxy : (1 - a) * p ≤ (1 - a) * q := mul_le_mul_of_nonneg_left hpq h1a
  have hq1 : (1 - a) * q ≤ (1 - a) * 1 := mul_le_mul_of_nonneg_left hq h1a
  have hyh : (1 - a) * q + a ≤ 1 := by linarith
  have key := increment_antitone hg hx hxy ha0 hyh
  rw [add_comm ((1 - a) * q) a, add_comm ((1 - a) * p) a] at key
  exact key

theorem delta_detect_mono {g : ℝ → ℝ} (hg : ConcaveOn ℝ (Set.Icc 0 1) g) {a p q δ : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1) (hmiss : delta g a p ≤ δ) : delta g a q ≤ δ :=
  le_trans (delta_antitone hg ha0 ha1 hp hpq hq) hmiss

theorem bracket {g : ℝ → ℝ} (hg : ConcaveOn ℝ (Set.Icc 0 1) g) (hg0 : g 0 = 0) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    delta g a 1 ≤ a * g 1 ∧ a * g 1 ≤ delta g a 0 := by
  unfold delta
  have m0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
  have m1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl _⟩
  have c1 := hg.2 m1 m0 ha0 (by linarith : (0 : ℝ) ≤ 1 - a) (by ring)
  have c2 := hg.2 m1 m0 (by linarith : (0 : ℝ) ≤ 1 - a) ha0 (by ring)
  simp only [smul_eq_mul, mul_one, mul_zero, add_zero, hg0] at c1 c2
  have e : (1 - a) * g 1 = g 1 - a * g 1 := by ring
  constructor
  · have e1 : a + (1 - a) * 1 = 1 := by ring
    rw [e1, mul_one]; linarith
  · rw [mul_zero, add_zero, hg0, sub_zero]; linarith

theorem delta_linear (κ a p : ℝ) : delta (fun x => κ * x) a p = κ * a := by unfold delta; ring

/-! ## 4. Cost and time of the owner's switchback -/

theorem total_cost_eq {p B c : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (1 - p) * B * (c / (p * (1 - p))) = c * B / p := by
  have h1 : (1 - p) ≠ 0 := by linarith
  have h2 : p ≠ 0 := hp.ne'
  field_simp

theorem total_cost_antitone {p q B c : ℝ} (hp : 0 < p) (hpq : p ≤ q) (hcB : 0 ≤ c * B) : c * B / q ≤ c * B / p :=
  div_le_div_of_nonneg_left hcB hp hpq

theorem info_max (p : ℝ) : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]

theorem days_min {p c : ℝ} (hc : 0 ≤ c) (hp : 0 < p) (hp1 : p < 1) : 4 * c ≤ c / (p * (1 - p)) := by
  have hpos : 0 < p * (1 - p) := mul_pos hp (by linarith)
  rw [le_div_iff₀ hpos]; nlinarith [info_max p]

theorem days_at_half (c : ℝ) : c / ((1 / 2 : ℝ) * (1 - 1 / 2)) = 4 * c := by ring

/-! ## 5. The hypotheses are satisfiable -/

theorem hyps_satisfiable :
    -- (1) two windows tiling 240 s with c = 5 s: greens of 10 s and 20 s
    pooled (Finset.univ : Finset (Fin 2)) ![240 / (10 + 5), 240 / (20 + 5)] ![10, 20] = 55 / 4 ∧
    winMean (Finset.univ : Finset (Fin 2)) ![(10 : ℝ), 20] = 15 ∧ (55 / 4 : ℝ) < 15 ∧
    -- (3) concave responses with g 0 = 0
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) id ∧ id (0 : ℝ) = 0 ∧
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun x : ℝ => √x) ∧ √(0 : ℝ) = 0 ∧
    -- (2) both signs of the A/B bias (W22-B at p 0.5: MPLight spillovers -1.34 / +0.63, AH +0.56 / -0.69)
    ((-1.34 : ℝ) < 0.63) ∧ ((-0.69 : ℝ) < 0.56) := by
  refine ⟨?_, ?_, by norm_num, concaveOn_id (convex_Icc 0 1), rfl, ?_, Real.sqrt_zero, by norm_num, by norm_num⟩
  · unfold pooled; simp [Fin.sum_univ_two]; norm_num
  · unfold winMean; simp [Fin.sum_univ_two]; norm_num
  · exact Real.strictConcaveOn_sqrt.concaveOn.subset Set.Icc_subset_Ici_self (convex_Icc 0 1)

end CIGAMF.P13.CityOwnerTestV1

#print axioms CIGAMF.P13.CityOwnerTestV1.pooled_le_winMean
#print axioms CIGAMF.P13.CityOwnerTestV1.tiling_antivary
#print axioms CIGAMF.P13.CityOwnerTestV1.length_biased
#print axioms CIGAMF.P13.CityOwnerTestV1.pooled_singleton
#print axioms CIGAMF.P13.CityOwnerTestV1.estimator_le_window_contrast
#print axioms CIGAMF.P13.CityOwnerTestV1.pooled_eq_of_const
#print axioms CIGAMF.P13.CityOwnerTestV1.ab_identity
#print axioms CIGAMF.P13.CityOwnerTestV1.ab_understates_iff
#print axioms CIGAMF.P13.CityOwnerTestV1.ab_overstates_iff
#print axioms CIGAMF.P13.CityOwnerTestV1.ab_unbiased_of_no_spill
#print axioms CIGAMF.P13.CityOwnerTestV1.increment_antitone
#print axioms CIGAMF.P13.CityOwnerTestV1.delta_antitone
#print axioms CIGAMF.P13.CityOwnerTestV1.delta_detect_mono
#print axioms CIGAMF.P13.CityOwnerTestV1.bracket
#print axioms CIGAMF.P13.CityOwnerTestV1.delta_linear
#print axioms CIGAMF.P13.CityOwnerTestV1.total_cost_eq
#print axioms CIGAMF.P13.CityOwnerTestV1.total_cost_antitone
#print axioms CIGAMF.P13.CityOwnerTestV1.info_max
#print axioms CIGAMF.P13.CityOwnerTestV1.days_min
#print axioms CIGAMF.P13.CityOwnerTestV1.days_at_half
#print axioms CIGAMF.P13.CityOwnerTestV1.hyps_satisfiable
