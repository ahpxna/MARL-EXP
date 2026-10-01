import «LeanPaperBHeadlineV1»

/-!
# Paper B: the lower bound's constant, kept exact

`cDelta K delta = (1-delta)/K * log(1/delta) - 2/e` is what `kl2_ge_log` produces after
replacing the second term of the binary divergence,

    (1-p) log((1-p)/(1-q)),

by its worst case `-2/e`.  That replacement is cheap to state and expensive to use: at
`K = 4` and `delta = 0.05` it drives the constant NEGATIVE, so the lower bound
`lowerBudget` certifies nothing at a configuration the experiments actually run, and the
condition `delta < 1/m` does not repair it.

Two things are proved here.

* `exact_dominates_loosened`: the exact constant `kl2((1-delta)/K, delta)` is never smaller
  than `cDelta K delta`.  This is `kl2_ge_log` read as what it is -- a loosening.
* `kl2_ge_of_ratio`: the exact constant is at least `delta`, hence strictly positive,
  whenever `e * delta <= (1-delta)/K`.  The proof keeps the second term instead of
  discarding it, bounding it by `q - p` through `log x >= 1 - 1/x`, and then uses
  `p log(p/q) >= p` on the ratio.  At `K = 4` the condition reads `delta <= 1/(1+4e)`,
  about `0.0842`, so `delta = 0.05` is inside it.

`lowerBudgetExact` is the lower budget with that constant, and `lower_budget_exact` is the
same derivation as `budget_lower` with the loosening not taken.
-/

namespace CIGAMF.P13.PaperBExactConst

open CIGAMF.P13.PaperBRates
open CIGAMF.P13.PaperBHeadline

/-! ## Keeping the second term -/

/-- `log x >= 1 - 1/x`, the other side of `log x <= x - 1`. -/
theorem log_ge_one_sub_inv (x : ℝ) (hx : 0 < x) : 1 - 1 / x ≤ Real.log x := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / x by positivity)
  rw [one_div, Real.log_inv] at h
  have hinv : (1 : ℝ) / x = x⁻¹ := one_div x
  rw [hinv]
  linarith

/-- **The exact divergence, with the second term kept.**  Bounding
`(1-p) log((1-p)/(1-q))` by `q - p` instead of by `-2/e`. -/
theorem kl2_ge_exact (p q : ℝ) (hp1 : p < 1) (hq1 : q < 1) :
    p * Real.log (p / q) + (q - p) ≤ kl2 p q := by
  have h1p : (0 : ℝ) < 1 - p := by linarith
  have h1q : (0 : ℝ) < 1 - q := by linarith
  have hratio : (0 : ℝ) < (1 - p) / (1 - q) := by positivity
  have hlog := log_ge_one_sub_inv ((1 - p) / (1 - q)) hratio
  have hinv : (1 : ℝ) / ((1 - p) / (1 - q)) = (1 - q) / (1 - p) := by
    field_simp
  rw [hinv] at hlog
  have hmul : (1 - p) * (1 - (1 - q) / (1 - p)) ≤ (1 - p) * Real.log ((1 - p) / (1 - q)) :=
    mul_le_mul_of_nonneg_left hlog h1p.le
  have hsimp : (1 - p) * (1 - (1 - q) / (1 - p)) = q - p := by
    field_simp
    ring
  rw [hsimp] at hmul
  unfold kl2
  linarith

/-- **The exact constant is at least `delta`.**  When the heavy answer's mass is at least
`e` times the confidence level, the binary divergence exceeds that level, so the lower
bound is non-vacuous. -/
theorem kl2_ge_of_ratio (p q : ℝ) (hq : 0 < q) (hp1 : p < 1) (hq1 : q < 1)
    (hpq : Real.exp 1 * q ≤ p) : q ≤ kl2 p q := by
  have hp : (0 : ℝ) < p := lt_of_lt_of_le (by positivity) hpq
  have hratio : Real.exp 1 ≤ p / q := by
    rw [le_div_iff₀ hq]
    linarith [hpq]
  have hlog : (1 : ℝ) ≤ Real.log (p / q) := by
    have h := Real.log_le_log (Real.exp_pos 1) hratio
    rwa [Real.log_exp] at h
  have hstep : p ≤ p * Real.log (p / q) := by
    nlinarith [hlog, hp]
  have hexact := kl2_ge_exact p q hp1 hq1
  linarith

/-- **The loosening really is a loosening.**  Whatever `cDelta` certifies, the exact
constant certifies too. -/
theorem exact_dominates_loosened (K : ℕ) (hK : 0 < K) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    cDelta K δ ≤ kl2 ((1 - δ) / (K : ℝ)) δ := by
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hp0 : (0 : ℝ) ≤ (1 - δ) / (K : ℝ) := by positivity
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hp1 : (1 - δ) / (K : ℝ) ≤ 1 := by
    rw [div_le_one hKR]
    linarith
  have h := kl2_ge_log ((1 - δ) / (K : ℝ)) δ hp0 hp1 hδ hδ1
  unfold cDelta
  linarith

/-! ## The lower budget with the exact constant -/

/-- The lower budget, with the binary divergence kept exact. -/
noncomputable def lowerBudgetExact (K : ℕ) (δ C h : ℝ) (s : ℕ) : ℝ :=
  kl2 ((1 - δ) / (K : ℝ)) δ / C / h ^ (2 * s)

/-- **The lower side with the exact constant.**  `hmono` is the monotonicity of the binary
divergence in its first argument above `delta`, which is what carries the pigeonhole answer
mass `p` down to the worst case `(1-delta)/K`; it is named rather than hidden. -/
theorem lower_budget_exact (K : ℕ) (δ C h N p : ℝ) (s : ℕ)
    (hC : 0 < C) (hh : 0 < h)
    (hmono : kl2 ((1 - δ) / (K : ℝ)) δ ≤ kl2 p δ)
    (hDP : kl2 p δ ≤ N * (C * h ^ (2 * s))) :
    lowerBudgetExact K δ C h s ≤ N := by
  have hpow : (0 : ℝ) < h ^ (2 * s) := pow_pos hh _
  have hCh : (0 : ℝ) < C * h ^ (2 * s) := by positivity
  have hle : kl2 ((1 - δ) / (K : ℝ)) δ ≤ N * (C * h ^ (2 * s)) := le_trans hmono hDP
  unfold lowerBudgetExact
  rw [div_div, div_le_iff₀ hCh]
  exact hle

/-- **And it is positive where `cDelta` is not.**  Under `e delta <= (1-delta)/K` the
budget is at least `delta / (C h^{2s})`, which is bounded away from zero. -/
theorem lower_budget_exact_positive (K : ℕ) (hK : 0 < K) (δ C h : ℝ) (s : ℕ)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hC : 0 < C) (hh : 0 < h)
    (hratio : Real.exp 1 * δ ≤ (1 - δ) / (K : ℝ)) :
    δ / C / h ^ (2 * s) ≤ lowerBudgetExact K δ C h s ∧ 0 < lowerBudgetExact K δ C h s := by
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hp1 : (1 - δ) / (K : ℝ) < 1 := by
    rw [div_lt_one hKR]
    nlinarith
  have hkey := kl2_ge_of_ratio ((1 - δ) / (K : ℝ)) δ hδ hp1 hδ1 hratio
  have hpow : (0 : ℝ) < h ^ (2 * s) := pow_pos hh _
  have hstep : δ / C / h ^ (2 * s) ≤ lowerBudgetExact K δ C h s := by
    unfold lowerBudgetExact
    rw [div_div, div_div]
    have hden : (0 : ℝ) < C * h ^ (2 * s) := by positivity
    have hdiff : 0 ≤ (kl2 ((1 - δ) / (K : ℝ)) δ - δ) / (C * h ^ (2 * s)) :=
      div_nonneg (by linarith) hden.le
    have hsplit : (kl2 ((1 - δ) / (K : ℝ)) δ - δ) / (C * h ^ (2 * s))
        = kl2 ((1 - δ) / (K : ℝ)) δ / (C * h ^ (2 * s)) - δ / (C * h ^ (2 * s)) := by ring
    linarith [hdiff, hsplit]
  exact ⟨hstep, lt_of_lt_of_le (by positivity) hstep⟩

/-! ## The monotonicity, proved rather than named -/

/-- **Gibbs.**  The binary divergence is nonnegative: `log_sum_two` at the two cells of the
partition, where the collapsed term is `1 * log (1/1) = 0`. -/
theorem kl2_nonneg (p q : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 < q) (hq1 : q < 1) :
    0 ≤ kl2 p q := by
  have h := log_sum_two p (1 - p) q (1 - q) hp (by linarith) hq (by linarith)
  have hc : p + (1 - p) = 1 := by ring
  have hd : q + (1 - q) = 1 := by ring
  rw [hc, hd] at h
  simpa [kl2] using h

/-- The divergence vanishes at the diagonal. -/
theorem kl2_self (q : ℝ) (hq : 0 < q) (hq1 : q < 1) : kl2 q q = 0 := by
  unfold kl2
  rw [div_self (ne_of_gt hq), div_self (by linarith : (1 : ℝ) - q ≠ 0), Real.log_one]
  ring

/-- **Convexity in the first argument**, at two points: two applications of `log_sum_two`,
one per cell of the partition. -/
theorem kl2_convex_first (p₁ p₂ q lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1)
    (hp1 : 0 ≤ p₁) (hp1' : p₁ ≤ 1) (hp2 : 0 ≤ p₂) (hp2' : p₂ ≤ 1)
    (hq : 0 < q) (hq1 : q < 1) :
    kl2 (lam * p₁ + (1 - lam) * p₂) q ≤ lam * kl2 p₁ q + (1 - lam) * kl2 p₂ q := by
  have hl1 : (0 : ℝ) < 1 - lam := by linarith
  have hq1' : (0 : ℝ) < 1 - q := by linarith
  -- first cell
  have hA := log_sum_two (lam * p₁) ((1 - lam) * p₂) (lam * q) ((1 - lam) * q)
    (by positivity) (by positivity) (by positivity) (by positivity)
  have hAden : lam * q + (1 - lam) * q = q := by ring
  have hA1 : lam * p₁ / (lam * q) = p₁ / q := by
    rw [mul_div_mul_left _ _ (ne_of_gt h0)]
  have hA2 : (1 - lam) * p₂ / ((1 - lam) * q) = p₂ / q := by
    rw [mul_div_mul_left _ _ (ne_of_gt hl1)]
  rw [hAden, hA1, hA2] at hA
  -- second cell
  have hB := log_sum_two (lam * (1 - p₁)) ((1 - lam) * (1 - p₂))
    (lam * (1 - q)) ((1 - lam) * (1 - q))
    (by positivity) (by positivity) (by positivity) (by positivity)
  have hBden : lam * (1 - q) + (1 - lam) * (1 - q) = 1 - q := by ring
  have hB1 : lam * (1 - p₁) / (lam * (1 - q)) = (1 - p₁) / (1 - q) := by
    rw [mul_div_mul_left _ _ (ne_of_gt h0)]
  have hB2 : (1 - lam) * (1 - p₂) / ((1 - lam) * (1 - q)) = (1 - p₂) / (1 - q) := by
    rw [mul_div_mul_left _ _ (ne_of_gt hl1)]
  rw [hBden, hB1, hB2] at hB
  have hnum : lam * (1 - p₁) + (1 - lam) * (1 - p₂) = 1 - (lam * p₁ + (1 - lam) * p₂) := by
    ring
  rw [hnum] at hB
  unfold kl2
  nlinarith [hA, hB]

/-- **(#11) The divergence increases in its first argument above `delta`.**  This is what
`lower_budget_exact` named as `hmono`; it is now a theorem.  The route is the mixture
identity `p' = lam p + (1-lam) q` with `lam = (p'-q)/(p-q)`, convexity, and `kl2 q q = 0`. -/
theorem kl2_mono_first (p p' q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (hqp : q ≤ p') (hpp : p' ≤ p) (hp1 : p ≤ 1) :
    kl2 p' q ≤ kl2 p q := by
  have hp0 : 0 ≤ p := by linarith
  have hnn := kl2_nonneg p q hp0 hp1 hq hq1
  rcases eq_or_lt_of_le hqp with hqp' | hqp'
  · rw [← hqp', kl2_self q hq hq1]
    exact hnn
  rcases eq_or_lt_of_le hpp with hpp' | hpp'
  · rw [hpp']
  -- now q < p' < p
  have hgap : (0 : ℝ) < p - q := by linarith
  set lam := (p' - q) / (p - q) with hlam
  have hl0 : (0 : ℝ) < lam := by
    rw [hlam]; exact div_pos (by linarith) hgap
  have hl1 : lam < 1 := by
    rw [hlam, div_lt_one hgap]; linarith
  have hmix : lam * p + (1 - lam) * q = p' := by
    rw [hlam]
    field_simp
    ring
  have hconv := kl2_convex_first p q q lam hl0 hl1 hp0 hp1 hq.le hq1.le hq hq1
  rw [hmix, kl2_self q hq hq1] at hconv
  nlinarith [hconv, hnn, hl1, hl0]

/-- **The lower budget with the exact constant, with `hmono` discharged.**  The pigeonhole
answer mass `p` is at least `(1-delta)/K`, and the divergence is monotone there, so nothing
is assumed about how the two compare. -/
theorem lower_budget_exact_closed (K : ℕ) (hK : 0 < K) (δ C h N p : ℝ) (s : ℕ)
    (hC : 0 < C) (hh : 0 < h) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hp1 : p ≤ 1) (hqp : δ ≤ (1 - δ) / (K : ℝ)) (hpp : (1 - δ) / (K : ℝ) ≤ p)
    (hDP : kl2 p δ ≤ N * (C * h ^ (2 * s))) :
    lowerBudgetExact K δ C h s ≤ N :=
  lower_budget_exact K δ C h N p s hC hh
    (kl2_mono_first p ((1 - δ) / (K : ℝ)) δ hδ hδ1 hqp hpp hp1) hDP

/-! ## Audit -/

#print axioms kl2_nonneg
#print axioms kl2_self
#print axioms kl2_convex_first
#print axioms kl2_mono_first
#print axioms lower_budget_exact_closed
#print axioms log_ge_one_sub_inv
#print axioms kl2_ge_exact
#print axioms kl2_ge_of_ratio
#print axioms exact_dominates_loosened
#print axioms lower_budget_exact
#print axioms lower_budget_exact_positive

end CIGAMF.P13.PaperBExactConst
