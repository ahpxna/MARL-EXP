import «LeanPaperA7StreamV1»

/-!
# Paper A7: the elementary asymptotics the rate needs, with explicit thresholds

Every error term of the ideal learner's analysis is a power of `t` below one times a
logarithm.  They are handled here with square roots only (no `rpow`) and explicit thresholds,
so that each "for `t` large enough" in the analysis is an actual `∃ T, ∀ t ≥ T`.

* `log_le_four_sqrt_sqrt` -- `log x <= 4 sqrt(sqrt x)` (from `log_le_two_sqrt` applied to
  `sqrt x`);
* `thr_le` -- the code's confidence level `4 log s + (K/2) log(1 + s/a)` is at most
  `C1 sqrt(sqrt s)` for `s >= 1`, with `C1 = 16 + 2K sqrt(sqrt(1 + 1/a))`;
* `eventually_inv_sqrt_sqrt` -- for every `c >= 0` and `eps > 0` there is a `T` with
  `c / sqrt(sqrt t) <= eps` for all `t >= T`; hence also for `c / sqrt t` and `c / t`.
-/

namespace CIGAMF.P13.PaperA7Asym

open CIGAMF.P13.PaperA7Stream

theorem log_le_four_sqrt_sqrt (x : ℝ) (hx : 0 < x) :
    Real.log x ≤ 4 * Real.sqrt (Real.sqrt x) := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h := log_le_two_sqrt (Real.sqrt x) hs
  have hlog : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt hx.le]; ring
  rw [hlog]
  linarith

theorem sqrt_sqrt_mono {x y : ℝ} (h : x ≤ y) : Real.sqrt (Real.sqrt x) ≤ Real.sqrt (Real.sqrt y) :=
  Real.sqrt_le_sqrt (Real.sqrt_le_sqrt h)

theorem sqrt_sqrt_mul (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (Real.sqrt (x * y)) = Real.sqrt (Real.sqrt x) * Real.sqrt (Real.sqrt y) := by
  rw [Real.sqrt_mul hx, Real.sqrt_mul (Real.sqrt_nonneg _)]

/-- The constant of the confidence level. -/
noncomputable def C1 (K a : ℝ) : ℝ := 16 + 2 * K * Real.sqrt (Real.sqrt (1 + 1 / a))

theorem C1_nonneg (K a : ℝ) (hK : 0 ≤ K) : 0 ≤ C1 K a := by
  unfold C1; positivity

/-- **The code's confidence level is at most `C1 sqrt(sqrt s)`.** -/
theorem thr_le (K a s : ℝ) (hK : 0 ≤ K) (ha : 0 < a) (hs : 1 ≤ s) :
    4 * Real.log s + (K / 2) * Real.log (1 + s / a) ≤ C1 K a * Real.sqrt (Real.sqrt s) := by
  have hs0 : 0 < s := by linarith
  have h1 := log_le_four_sqrt_sqrt s hs0
  have hy : 0 < 1 + s / a := by positivity
  have h2 := log_le_four_sqrt_sqrt (1 + s / a) hy
  have hle : 1 + s / a ≤ (1 + 1 / a) * s := by
    have : 1 ≤ s := hs
    have h' : s / a = (1 / a) * s := by ring
    rw [h']
    nlinarith [div_pos one_pos ha]
  have h3 : Real.sqrt (Real.sqrt (1 + s / a))
      ≤ Real.sqrt (Real.sqrt (1 + 1 / a)) * Real.sqrt (Real.sqrt s) := by
    rw [← sqrt_sqrt_mul _ _ (by positivity) hs0.le]
    exact sqrt_sqrt_mono hle
  have hK2 : 0 ≤ K / 2 := by positivity
  unfold C1
  have := mul_le_mul_of_nonneg_left h2 hK2
  have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ K / 2 * 4)
  nlinarith

/-- **Every `c / sqrt(sqrt t)` is eventually below `eps`.** -/
theorem eventually_inv_sqrt_sqrt (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ T : ℕ, ∀ t : ℕ, T ≤ t → c / Real.sqrt (Real.sqrt t) ≤ ε := by
  set q := c / ε with hq
  refine ⟨⌈q ^ 4⌉₊ + 1, fun t ht => ?_⟩
  have htR : q ^ 4 < t := by
    have := Nat.le_ceil (q ^ 4)
    have : (⌈q ^ 4⌉₊ : ℝ) + 1 ≤ t := by exact_mod_cast ht
    linarith
  have ht0 : (0 : ℝ) < t := lt_of_le_of_lt (by positivity) htR
  have hq0 : 0 ≤ q := div_nonneg hc hε.le
  have hss : q < Real.sqrt (Real.sqrt t) := by
    have h1 : q ^ 2 < Real.sqrt t := by
      rw [show (t : ℝ) = Real.sqrt t ^ 2 from (Real.sq_sqrt ht0.le).symm] at htR
      have : (q ^ 2) ^ 2 < (Real.sqrt t) ^ 2 := by rw [← pow_mul]; exact htR
      exact lt_of_pow_lt_pow_left₀ 2 (Real.sqrt_nonneg _) this
    have : q ^ 2 < (Real.sqrt (Real.sqrt t)) ^ 2 := by
      rw [Real.sq_sqrt (Real.sqrt_nonneg _)]; exact h1
    exact lt_of_pow_lt_pow_left₀ 2 (Real.sqrt_nonneg _) this
  have hpos : 0 < Real.sqrt (Real.sqrt t) := lt_of_le_of_lt hq0 hss
  rw [div_le_iff₀ hpos]
  have : c = q * ε := by rw [hq]; field_simp
  rw [this]
  nlinarith

theorem sqrt_sqrt_le_sqrt (t : ℝ) (ht : 1 ≤ t) : Real.sqrt (Real.sqrt t) ≤ Real.sqrt t := by
  have h1 : 1 ≤ Real.sqrt t := Real.one_le_sqrt.mpr ht
  calc Real.sqrt (Real.sqrt t) ≤ Real.sqrt t * 1 := by
        rw [mul_one]
        rw [Real.sqrt_le_left]
        · nlinarith
        · positivity
    _ = Real.sqrt t := mul_one _

theorem eventually_inv_sqrt (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ T : ℕ, ∀ t : ℕ, T ≤ t → c / Real.sqrt t ≤ ε := by
  obtain ⟨T, hT⟩ := eventually_inv_sqrt_sqrt c ε hc hε
  refine ⟨max T 1, fun t ht => ?_⟩
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast le_trans (le_max_right _ _) ht
  have h := hT t (le_trans (le_max_left _ _) ht)
  have hss := sqrt_sqrt_le_sqrt t ht1
  have hpos : 0 < Real.sqrt (Real.sqrt t) := by
    apply Real.sqrt_pos.mpr; apply Real.sqrt_pos.mpr; linarith
  exact le_trans (div_le_div_of_nonneg_left hc hpos hss) h

theorem eventually_inv (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ T : ℕ, ∀ t : ℕ, T ≤ t → c / t ≤ ε := by
  obtain ⟨T, hT⟩ := eventually_inv_sqrt c ε hc hε
  refine ⟨max T 1, fun t ht => ?_⟩
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast le_trans (le_max_right _ _) ht
  have h := hT t (le_trans (le_max_left _ _) ht)
  have hs : Real.sqrt t ≤ t := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hpos : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.mpr (by linarith)
  exact le_trans (div_le_div_of_nonneg_left hc hpos hs) h

#print axioms log_le_four_sqrt_sqrt
#print axioms thr_le
#print axioms eventually_inv_sqrt_sqrt
#print axioms eventually_inv_sqrt
#print axioms eventually_inv

end CIGAMF.P13.PaperA7Asym
