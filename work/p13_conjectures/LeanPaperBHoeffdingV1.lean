import «LeanPaperBAttainV1»
import «LeanPaperBHeadlineV1»
import Mathlib.Probability.Moments.SubGaussian

/-!
# Paper B: the `log(1/delta)` upper side

`LeanPaperBHeadlineV1.sides_do_not_match` recorded an honest gap: the lower budget carries
`log(1/delta)` and the Chebyshev upper budget of `budget_from_gap` carries `1/alpha`, so the
pair was not a `Theta` in the confidence parameter.  The note there said closing it needs a
test whose error decays exponentially in `N`, and that no such inequality was available.

It is available.  Mathlib carries Hoeffding's lemma
(`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`) and the Hoeffding inequality for
independent sub-Gaussian summands
(`ProbabilityTheory.measure_sum_range_ge_le_of_iIndepFun`).  Paper B's decoder reads a
statistic bounded in `[-1,1]` -- the parity mask itself is `+-1` -- so the hypotheses are
met by the construction and not assumed.

The chain is: bounded statistic `=>` sub-Gaussian with proxy `1` after centring `=>` the
centred sum has an exponential tail `=>` the midpoint threshold errs with probability at
most `exp(-N g^2/8)` `=>` `N >= 8 log(1/delta)/g^2` suffices.  With `g = Theta(h^r)` from
`gap_at_scale` this is `N = O(h^{-2r} log(1/delta))`, the same shape as the lower bound, and
`sides_match_in_delta` bounds the ratio of the two sides by a constant free of `delta`.
-/

namespace CIGAMF.P13.PaperBHoeffding

open MeasureTheory ProbabilityTheory
open CIGAMF.P13.PaperBHeadline

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## A bounded statistic is sub-Gaussian -/

/-- **A statistic bounded by `1` is sub-Gaussian with proxy `1` once centred.**  This is
Hoeffding's lemma at `[a,b] = [-1,1]`, where `((b-a)/2)^2 = 1`. -/
theorem bounded_subgaussian [IsProbabilityMeasure μ] (Z : Ω → ℝ) (hm : AEMeasurable Z μ)
    (hb : ∀ᵐ ω ∂μ, |Z ω| ≤ 1) :
    HasSubgaussianMGF (fun ω => Z ω - μ[Z]) 1 μ := by
  have hb' : ∀ᵐ ω ∂μ, Z ω ∈ Set.Icc (-1 : ℝ) 1 := by
    filter_upwards [hb] with ω h
    exact abs_le.mp h
  have h := hasSubgaussianMGF_of_mem_Icc hm hb'
  have hc : ((‖(1 : ℝ) - (-1 : ℝ)‖₊ / 2) ^ 2) = (1 : NNReal) := by
    norm_num
  rwa [hc] at h

/-! ## The exponential tail of the centred sum -/

/-- **Hoeffding's inequality in the form the decoder uses.**  Independent observations,
each bounded by `1` and each with mean `c`, have a centred sum with a Gaussian tail of
proxy `n`. -/
theorem tail_centred_sum [IsProbabilityMeasure μ] (Z : ℕ → Ω → ℝ)
    (hindep : iIndepFun Z μ) (hmeas : ∀ i, AEMeasurable (Z i) μ)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |Z i ω| ≤ 1) (c : ℝ) (hc : ∀ i, μ[Z i] = c)
    (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, (Z i ω - c)}
      ≤ Real.exp (-ε ^ 2 / (2 * n * 1)) := by
  have hindep' : iIndepFun (fun i => fun ω => Z i ω - c) μ := by
    have h := hindep.comp (fun _ => fun x : ℝ => x - c) (fun _ => measurable_id.sub_const c)
    exact h
  refine HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hindep' (c := 1)
    (fun i _ => ?_) hε
  have h := bounded_subgaussian (μ := μ) (Z i) (hmeas i) (hb i)
  rwa [hc i] at h

/-! ## The decoder's error probability -/

/-- The sum of a centred block, rewritten. -/
theorem sum_centred (Z : ℕ → Ω → ℝ) (c : ℝ) (n : ℕ) (ω : Ω) :
    ∑ i ∈ Finset.range n, (Z i ω - c) = (∑ i ∈ Finset.range n, Z i ω) - (n : ℝ) * c := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **The midpoint threshold errs with an exponentially small probability.**  Under the
world whose mean is the lower one, the empirical sum crosses the midpoint threshold with
probability at most `exp(-n g^2/8)`. -/
theorem decoder_error_le_exp [IsProbabilityMeasure μ] (Z : ℕ → Ω → ℝ)
    (hindep : iIndepFun Z μ) (hmeas : ∀ i, AEMeasurable (Z i) μ)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |Z i ω| ≤ 1)
    (μplus μminus g : ℝ) (hg : 0 < g) (hgap : μminus + g ≤ μplus)
    (hc : ∀ i, μ[Z i] = μminus) (n : ℕ) (hn : 0 < n) :
    μ.real {ω | (n : ℝ) * ((μplus + μminus) / 2) ≤ ∑ i ∈ Finset.range n, Z i ω}
      ≤ Real.exp (-(n : ℝ) * g ^ 2 / 8) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hεnn : (0 : ℝ) ≤ (n : ℝ) * g / 2 := by positivity
  have hsub : {ω : Ω | (n : ℝ) * ((μplus + μminus) / 2) ≤ ∑ i ∈ Finset.range n, Z i ω}
      ⊆ {ω : Ω | (n : ℝ) * g / 2 ≤ ∑ i ∈ Finset.range n, (Z i ω - μminus)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [sum_centred Z μminus n ω]
    nlinarith [hω, hnR, hgap]
  have hmono := measureReal_mono (μ := μ) hsub
  refine le_trans hmono (le_trans (tail_centred_sum Z hindep hmeas hb μminus hc n _ hεnn) ?_)
  have hval : -((n : ℝ) * g / 2) ^ 2 / (2 * (n : ℝ) * 1) = -(n : ℝ) * g ^ 2 / 8 := by
    field_simp
    ring
  rw [hval]

/-! ## The budget -/

/-- The Hoeffding-sufficient budget: `8 log(1/delta)/g^2`. -/
noncomputable def hoeffdingSufficient (g δ : ℝ) : ℝ := 8 * Real.log (1 / δ) / g ^ 2

/-- **At that budget the exponential tail is below `delta`.** -/
theorem exp_bound_at_budget (g δ : ℝ) (hg : 0 < g) (hδ : 0 < δ) (n : ℕ)
    (hn : hoeffdingSufficient g δ ≤ (n : ℝ)) :
    Real.exp (-(n : ℝ) * g ^ 2 / 8) ≤ δ := by
  have hg2 : (0 : ℝ) < g ^ 2 := by positivity
  have hstep : Real.log (1 / δ) ≤ (n : ℝ) * g ^ 2 / 8 := by
    unfold hoeffdingSufficient at hn
    rw [div_le_iff₀ hg2] at hn
    linarith
  have hlog : Real.log (1 / δ) = -Real.log δ := by
    rw [one_div, Real.log_inv]
  have hexp : -(n : ℝ) * g ^ 2 / 8 ≤ Real.log δ := by
    rw [hlog] at hstep
    linarith
  calc Real.exp (-(n : ℝ) * g ^ 2 / 8) ≤ Real.exp (Real.log δ) := Real.exp_le_exp.mpr hexp
    _ = δ := Real.exp_log hδ

/-- **The `log(1/delta)` upper side, assembled.**  A statistic bounded by `1`, independent
across queries, with a mean gap `g` between the two worlds: at `N >= 8 log(1/delta)/g^2` the
midpoint decoder errs with probability at most `delta`. -/
theorem log_budget_suffices [IsProbabilityMeasure μ] (Z : ℕ → Ω → ℝ)
    (hindep : iIndepFun Z μ) (hmeas : ∀ i, AEMeasurable (Z i) μ)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |Z i ω| ≤ 1)
    (μplus μminus g δ : ℝ) (hg : 0 < g) (hδ : 0 < δ) (hgap : μminus + g ≤ μplus)
    (hc : ∀ i, μ[Z i] = μminus) (n : ℕ) (hn0 : 0 < n)
    (hn : hoeffdingSufficient g δ ≤ (n : ℝ)) :
    μ.real {ω | (n : ℝ) * ((μplus + μminus) / 2) ≤ ∑ i ∈ Finset.range n, Z i ω} ≤ δ :=
  le_trans (decoder_error_le_exp Z hindep hmeas hb μplus μminus g hg hgap hc n hn0)
    (exp_bound_at_budget g δ hg hδ n hn)

/-! ## The budget at the perturbation scale -/

/-- **The budget at a gap of order `h^r`.**  With `g = kappa * h^r`, which is what
`gap_at_scale` delivers, the sufficient budget is `8 log(1/delta) / kappa^2 * h^{-2r}`:
the same exponent as the lower bound, and the same `log(1/delta)`. -/
theorem budget_at_scale (κ h δ : ℝ) (r : ℕ) (hκ : 0 < κ) (hh : 0 < h) :
    hoeffdingSufficient (κ * h ^ r) δ
      = (8 * Real.log (1 / δ) / κ ^ 2) / h ^ (2 * r) := by
  unfold hoeffdingSufficient
  have hpow : (κ * h ^ r) ^ 2 = κ ^ 2 * h ^ (2 * r) := by
    rw [mul_pow, ← pow_mul, mul_comm r 2]
  rw [hpow]
  field_simp

/-- **The `delta`-dependence of the upper side is exactly `log(1/delta)`.** -/
theorem upper_over_log_is_constant (g δ : ℝ) (hg : 0 < g) (hlog : Real.log (1 / δ) ≠ 0) :
    hoeffdingSufficient g δ / Real.log (1 / δ) = 8 / g ^ 2 := by
  unfold hoeffdingSufficient
  have hg2 : (g : ℝ) ^ 2 ≠ 0 := by positivity
  field_simp

/-! ## The two sides now match in `delta` -/

/-- **The ratio of the two sides is free of `delta`.**  `sides_do_not_match` computed the
Chebyshev ratio and found it growing as the level tightens.  With the Hoeffding budget in
place of the Chebyshev one the ratio is bounded by `32 K C h^{2s}/g^2`, in which `delta`
does not appear.  The hypothesis `8K <= log(1/delta)` is the regime in which the lower
bound's additive `-2/e` is dominated; it is a statement about the confidence level alone. -/
theorem sides_match_in_delta (K : ℕ) (hK : 0 < K) (g C h δ : ℝ) (s : ℕ)
    (hg : 0 < g) (hC : 0 < C) (hh : 0 < h) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hlog : 8 * (K : ℝ) ≤ Real.log (1 / δ)) :
    hoeffdingSufficient g δ / lowerBudget K δ C h s
      ≤ 32 * (K : ℝ) * C * h ^ (2 * s) / g ^ 2 := by
  set Λ := Real.log (1 / δ) with hΛ
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hΛpos : (0 : ℝ) < Λ := by nlinarith
  have hg2 : (0 : ℝ) < g ^ 2 := by positivity
  have hpow : (0 : ℝ) < h ^ (2 * s) := pow_pos hh _
  -- the lower bound's constant is at least `Λ/(4K)`
  have he : (2 : ℝ) * (Real.exp 1)⁻¹ ≤ 1 := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    have h2 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    rw [mul_inv_le_iff₀ h2]
    linarith
  have hu : (0 : ℝ) < Λ / (K : ℝ) := by positivity
  have hu8 : (8 : ℝ) ≤ Λ / (K : ℝ) := by
    rw [le_div_iff₀ hKR]
    linarith
  have hcd : Λ / (4 * (K : ℝ)) ≤ cDelta K δ := by
    unfold cDelta
    have hsplit : (1 - δ) / (K : ℝ) * Λ = (1 - δ) * (Λ / (K : ℝ)) := by
      field_simp
    have hq : Λ / (4 * (K : ℝ)) = (Λ / (K : ℝ)) / 4 := by
      field_simp
    rw [hsplit, hq]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 2 - δ) hu.le, hu8, he]
  have hcdpos : (0 : ℝ) < cDelta K δ := by
    have hqp : (0 : ℝ) < Λ / (4 * (K : ℝ)) := by positivity
    linarith
  have hlbpos : (0 : ℝ) < lowerBudget K δ C h s := by
    unfold lowerBudget
    positivity
  have hnum : 8 * Λ ≤ 32 * (K : ℝ) * cDelta K δ := by
    have hscale : 32 * (K : ℝ) * (Λ / (4 * (K : ℝ))) = 8 * Λ := by
      field_simp
      ring
    nlinarith [mul_le_mul_of_nonneg_left hcd (by positivity : (0 : ℝ) ≤ 32 * (K : ℝ))]
  rw [div_le_iff₀ hlbpos]
  unfold hoeffdingSufficient lowerBudget
  rw [← hΛ]
  have hrhs : 32 * (K : ℝ) * C * h ^ (2 * s) / g ^ 2 * (cDelta K δ / C / h ^ (2 * s))
      = 32 * (K : ℝ) * cDelta K δ / g ^ 2 := by
    field_simp
  rw [hrhs]
  have hdiff : 0 ≤ (32 * (K : ℝ) * cDelta K δ - 8 * Λ) / g ^ 2 :=
    div_nonneg (by linarith) (le_of_lt hg2)
  have hsplit2 : (32 * (K : ℝ) * cDelta K δ - 8 * Λ) / g ^ 2
      = 32 * (K : ℝ) * cDelta K δ / g ^ 2 - 8 * Λ / g ^ 2 := by ring
  linarith [hdiff, hsplit2]

/-! ## Audit -/

#print axioms bounded_subgaussian
#print axioms tail_centred_sum
#print axioms decoder_error_le_exp
#print axioms exp_bound_at_budget
#print axioms log_budget_suffices
#print axioms budget_at_scale
#print axioms upper_over_log_is_constant
#print axioms sides_match_in_delta

end CIGAMF.P13.PaperBHoeffding
