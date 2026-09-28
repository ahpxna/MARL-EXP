import «LeanPaperBRatesV1»

/-!
# Paper B: the headline, assembled

The two exponents were proved separately and the headline was left in prose.  It is an
assembly, and writing it out is what makes visible which half is a theorem and which is not.

**The lower side is `Omega(h^{-2s} log(1/delta))` and is a theorem.**  `lowerBudget` names
the bound `decision_budget_two_parameter` produces: with a per-step divergence at most
`C h^{2s}`, any rule that answers correctly with probability `1 - delta` needs

    N  >=  ( (1-delta)/K * log(1/delta) - 2/e ) / C / h^{2s}.

The constant depends on the family and on the number of answers `K`, never on `h` or on
`delta`.  It is applied at `s = s_safe` and at `s = s_id`, and nothing about the two
applications differs except the exponent.

**The upper side is `O(h^{-2}/alpha)` and carries `1/alpha`, not `log(1/alpha)`.**
`safeSufficient` names the Chebyshev budget of `decision_sample_budget`.  So the two sides
do NOT match in the confidence parameter, and this module does not pretend otherwise: there
is no theorem here of the form `N* = Theta(h^{-2s} log(1/delta))`.  Closing that gap needs a
test whose error decays exponentially in `N`, which is `PROOFS.md` §B2c's route and is not
formalised.

**The separation between the exponents is exact.**  `separation_ratio` is an identity, not
an estimate: the identification lower bound is the safe sufficient budget multiplied by
`(36 alpha c_delta)/(C V) / h^{2t}` at `s_id = t+1`, `s_safe = 1`.  `separation_unbounded`
then says that factor exceeds any `M` once `h` is small enough, with the threshold written
down.
-/

namespace CIGAMF.P13.PaperBHeadline

open CIGAMF.P13.PaperBRates

/-- The `delta`-dependent constant in the lower budget. -/
noncomputable def cDelta (K : ℕ) (δ : ℝ) : ℝ :=
  (1 - δ) / (K : ℝ) * Real.log (1 / δ) - 2 * (Real.exp 1)⁻¹

/-- The lower budget at exponent `s`. -/
noncomputable def lowerBudget (K : ℕ) (δ C h : ℝ) (s : ℕ) : ℝ :=
  cDelta K δ / C / h ^ (2 * s)

/-- The Chebyshev-sufficient budget on the decision side. -/
noncomputable def safeSufficient (V α h : ℝ) : ℝ := V / (36 * α * h ^ 2)

/-- **The lower side, at any exponent.**  A restatement of
`decision_budget_two_parameter` in the headline's own vocabulary. -/
theorem budget_lower (K : ℕ) (hK : 0 < K) (δ C h N p : ℝ) (s : ℕ)
    (hδ : 0 < δ) (hδ2 : δ < 1) (hC : 0 < C) (hh : 0 < h)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp : (1 - δ) / (K : ℝ) ≤ p)
    (hDP : kl2 p δ ≤ N * (C * h ^ (2 * s))) :
    lowerBudget K δ C h s ≤ N :=
  decision_budget_two_parameter K hK δ C h N p s hδ hδ2 hC hh hp0 hp1 hp hDP

/-- **The upper side, on the decision problem.**  A restatement of
`decision_sample_budget`: the Chebyshev budget suffices, and it scales as `1/alpha`. -/
theorem safe_upper (V h α : ℝ) (hV : 0 ≤ V) (hh : 0 < h) (hα : 0 < α)
    (N : ℝ) (hNpos : 0 < N) (hN : safeSufficient V α h ≤ N) :
    V / N / (6 * h) ^ 2 ≤ α :=
  decision_sample_budget V h α hV hh hα N hNpos hN

/-- **The separation, as an identity.**  At `s_safe = 1` and `s_id = t+1`, the
identification lower bound is the safe sufficient budget times an explicit factor
`h^{-2t}`. -/
theorem separation_ratio (K : ℕ) (δ C h V α : ℝ) (t : ℕ)
    (hh : 0 < h) (hC : 0 < C) (hV : 0 < V) (hα : 0 < α) :
    lowerBudget K δ C h (t + 1)
      = (36 * α * cDelta K δ / (C * V)) / h ^ (2 * t) * safeSufficient V α h := by
  unfold lowerBudget safeSufficient
  have hpow : (0 : ℝ) < h ^ (2 * t) := pow_pos hh _
  have h2 : (0 : ℝ) < h ^ 2 := pow_pos hh 2
  have hexp : h ^ (2 * (t + 1)) = h ^ (2 * t) * h ^ 2 := by
    rw [← pow_add]
    congr 1
  rw [hexp]
  field_simp

/-- **The factor is unbounded.**  For `t >= 1` and `0 < h <= 1` the separation factor is at
least `A/h^2`, and that exceeds any `M > 0` once `h < sqrt(A/M)`. -/
theorem separation_unbounded (A M h : ℝ) (t : ℕ) (ht : 1 ≤ t)
    (hA : 0 < A) (hM : 0 < M) (hh : 0 < h) (hh1 : h ≤ 1)
    (hsmall : h < Real.sqrt (A / M)) :
    M < A / h ^ (2 * t) := by
  have h2 : (0 : ℝ) < h ^ 2 := pow_pos hh 2
  have hpow : (0 : ℝ) < h ^ (2 * t) := pow_pos hh _
  have hmono : h ^ (2 * t) ≤ h ^ 2 := by
    refine pow_le_pow_of_le_one hh.le hh1 ?_
    omega
  have hstep : A / h ^ 2 ≤ A / h ^ (2 * t) :=
    div_le_div_of_nonneg_left hA.le hpow hmono
  have hsq : h ^ 2 < A / M := by
    have hAM : (0 : ℝ) ≤ A / M := le_of_lt (div_pos hA hM)
    have := Real.sq_sqrt hAM
    nlinarith [Real.sqrt_nonneg (A / M), hsmall, hh]
  have hlt : M < A / h ^ 2 := by
    rw [lt_div_iff₀ h2]
    have hMlt : M * h ^ 2 < M * (A / M) := mul_lt_mul_of_pos_left hsq hM
    rwa [mul_div_cancel₀ _ (ne_of_gt hM)] at hMlt
  linarith

/-- **What the two sides do and do not give.**  The lower bound carries `log(1/delta)`; the
Chebyshev upper bound carries `1/alpha`.  At the same confidence level the upper bound is
therefore larger than the lower bound by a factor that itself grows as the level tightens —
so the pair is not a `Theta`, and recording the ratio is the honest form. -/
theorem sides_do_not_match (V C α : ℝ) (K : ℕ) (h : ℝ)
    (hV : 0 < V) (hC : 0 < C) (hα : 0 < α) (hh : 0 < h) :
    safeSufficient V α h / lowerBudget K α C h 1
      = (V * C) / (36 * α * cDelta K α) := by
  unfold safeSufficient lowerBudget
  have h2 : (0 : ℝ) < h ^ 2 := pow_pos hh 2
  have hpow : h ^ (2 * 1) = h ^ 2 := by norm_num
  rw [hpow]
  field_simp

/-! ## Audit -/

#print axioms budget_lower
#print axioms safe_upper
#print axioms separation_ratio
#print axioms separation_unbounded
#print axioms sides_do_not_match

end CIGAMF.P13.PaperBHeadline
