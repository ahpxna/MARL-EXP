import «LeanPaperAEndgameV1»

/-!
# Paper A: discharging `GaussianKLIdentification`

`LeanPaperAEndgameV1` states `GaussianKLIdentification` as an explicit OPEN interface and
its headline theorems -- `actual_kl_separation`, `proxy_optimizer_misses_actual_information`,
`family_operational_finish` -- consume it as a hypothesis.  Until something instantiates it
those theorems are conditionals: they say the separation holds *if* the observation model's
divergence is the Gaussian one, and nothing in the corpus said that it is.

This module supplies the instance.  Nothing here rebuilds the Gaussian integral: the corpus
already proves `gaussKL_eq_integral` (the affine log-ratio integrates to `(θ-λ)²/(2σ²)`) and
`logratio_affine` (the algebraic identity behind it).  What was missing was the join to
Mathlib's `klDiv`, which is defined through `llr` and the Radon-Nikodym derivative, not
through an integral of a log-ratio.  The three steps are:

* `log_pdf_ratio` -- the normalising constants cancel, so the log of the density ratio is the
  affine function, with NO integral yet;
* `llr_gaussianReal` -- `llr` of the two laws IS that function, almost everywhere.  Both
  directions of absolute continuity are needed: `rnDeriv_eq_div` gives an identity almost
  everywhere for the SECOND measure, while `llr` is integrated against the FIRST;
* `toReal_klDiv_gaussianReal` and `klDiv_gaussianReal_ne_top` -- the two halves the interface
  asks for.  Finiteness is not a formality: `toReal` of `⊤` is `0`, so a module that proved
  only the `toReal` half would be satisfied by a divergence that is identically infinite.

The variance is COMMON to the two laws.  That is what makes the normalising constants cancel
and the log-ratio affine; the family's `pairVar` is a function of the cell alone and not of
the world, so this is the case that arises, but the restriction is real and is not hidden.
-/

namespace CIGAMF.P13.PaperAGaussianKL

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped NNReal ENNReal
open CIGAMF.P13.PaperARPair CIGAMF.P13.PaperACentred
open CIGAMF.P13.PaperAStrict CIGAMF.P13.PaperAActualDecisionBridge
open CIGAMF.P13.PaperAEndgame

/-! ## 1. The log density ratio, with no integral -/

/-- **The normalising constants cancel.**  Two Gaussians of a COMMON variance have a log
density ratio that is affine in the observation -- this is the whole reason the divergence
needs only the first moment, and it is an identity at every point, not almost everywhere. -/
theorem log_pdf_ratio (a b : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (y : ℝ) :
    Real.log (gaussianPDFReal a v y / gaussianPDFReal b v y)
      = (a - b) * (2 * y - a - b) / (2 * (v : ℝ)) := by
  have hv0 : (0 : ℝ≥0) < v := pos_iff_ne_zero.mpr hv
  have hvR : (0 : ℝ) < (v : ℝ) := NNReal.coe_pos.mpr hv0
  have hs : (0 : ℝ) < Real.sqrt (2 * π * (v : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have hs' : Real.sqrt (2 * π * (v : ℝ)) ≠ 0 := ne_of_gt hs
  have he1 : Real.exp (-(y - a) ^ 2 / (2 * (v : ℝ))) ≠ 0 := Real.exp_ne_zero _
  have he2 : Real.exp (-(y - b) ^ 2 / (2 * (v : ℝ))) ≠ 0 := Real.exp_ne_zero _
  have hratio : gaussianPDFReal a v y / gaussianPDFReal b v y
      = Real.exp (-(y - a) ^ 2 / (2 * (v : ℝ)) - -(y - b) ^ 2 / (2 * (v : ℝ))) := by
    simp only [gaussianPDFReal]
    rw [Real.exp_sub]
    field_simp
  rw [hratio, Real.log_exp, ← logratio_affine a b (v : ℝ) y]
  ring

/-! ## 2. The log-likelihood ratio of the two laws -/

/-- **`llr` IS that affine function**, almost everywhere under the first law.

`Measure.rnDeriv_eq_div` returns an identity that holds almost everywhere for the SECOND
measure, but `llr` is integrated against the FIRST, so the statement has to be transported.
That is legitimate here only because a non-degenerate Gaussian and Lebesgue measure are
mutually absolutely continuous, which is recorded rather than assumed. -/
theorem llr_gaussianReal (a b : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    llr (gaussianReal a v) (gaussianReal b v)
      =ᵐ[gaussianReal a v] fun y => (a - b) * (2 * y - a - b) / (2 * (v : ℝ)) := by
  have hav : gaussianReal a v ≪ volume := gaussianReal_absolutelyContinuous a hv
  have hbv : gaussianReal b v ≪ volume := gaussianReal_absolutelyContinuous b hv
  have hvb : volume ≪ gaussianReal b v := gaussianReal_absolutelyContinuous' b hv
  have hab : gaussianReal a v ≪ gaussianReal b v := hav.trans hvb
  have h1 : (gaussianReal a v).rnDeriv (gaussianReal b v)
      =ᵐ[gaussianReal a v] fun y => (gaussianReal a v).rnDeriv volume y
        / (gaussianReal b v).rnDeriv volume y :=
    (Measure.rnDeriv_eq_div hav hbv).filter_mono hab.ae_le
  have h2 : (gaussianReal a v).rnDeriv volume =ᵐ[gaussianReal a v] gaussianPDF a v :=
    (rnDeriv_gaussianReal a v).filter_mono hav.ae_le
  have h3 : (gaussianReal b v).rnDeriv volume =ᵐ[gaussianReal a v] gaussianPDF b v :=
    (rnDeriv_gaussianReal b v).filter_mono hav.ae_le
  filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
  simp only [llr, hy1, hy2, hy3]
  rw [ENNReal.toReal_div, toReal_gaussianPDF, toReal_gaussianPDF]
  exact log_pdf_ratio a b v hv y

/-- The affine log-ratio is integrable, because a Gaussian has a first moment. -/
theorem integrable_llr_gaussianReal (a b : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    Integrable (llr (gaussianReal a v) (gaussianReal b v)) (gaussianReal a v) := by
  have hv0 : (0 : ℝ≥0) < v := pos_iff_ne_zero.mpr hv
  have hvR : (0 : ℝ) < (v : ℝ) := NNReal.coe_pos.mpr hv0
  have hfun : (fun y : ℝ => (a - b) * (2 * y - a - b) / (2 * (v : ℝ)))
      = fun y : ℝ => ((a - b) / (v : ℝ)) * y + (-((a - b) * (a + b)) / (2 * (v : ℝ))) := by
    funext y
    field_simp
    ring
  have hint : Integrable (fun y : ℝ => ((a - b) / (v : ℝ)) * y) (gaussianReal a v) :=
    (IsGaussian.integrable_fun_id).const_mul _
  have haff : Integrable (fun y : ℝ => (a - b) * (2 * y - a - b) / (2 * (v : ℝ)))
      (gaussianReal a v) := by
    rw [hfun]
    exact hint.add (integrable_const _)
  exact haff.congr (llr_gaussianReal a b v hv).symm

/-! ## 3. The two halves the interface asks for -/

/-- **The divergence is FINITE.**  Stated separately because `toReal ⊤ = 0`: a module that
proved only the value would be satisfied by a divergence that is identically infinite. -/
theorem klDiv_gaussianReal_ne_top (a b : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    klDiv (gaussianReal a v) (gaussianReal b v) ≠ ⊤ := by
  have hav : gaussianReal a v ≪ volume := gaussianReal_absolutelyContinuous a hv
  have hvb : volume ≪ gaussianReal b v := gaussianReal_absolutelyContinuous' b hv
  exact klDiv_ne_top (hav.trans hvb) (integrable_llr_gaussianReal a b v hv)

/-- **And its value is the corpus's `gaussKL`.**  The integral was already proved
(`gaussKL_eq_integral`); what is added is that Mathlib's `klDiv` computes it. -/
theorem toReal_klDiv_gaussianReal (a b : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    (klDiv (gaussianReal a v) (gaussianReal b v)).toReal = gaussKL a b (v : ℝ) := by
  have hv0 : (0 : ℝ≥0) < v := pos_iff_ne_zero.mpr hv
  have hvR : (0 : ℝ) < (v : ℝ) := NNReal.coe_pos.mpr hv0
  have hav : gaussianReal a v ≪ volume := gaussianReal_absolutelyContinuous a hv
  have hvb : volume ≪ gaussianReal b v := gaussianReal_absolutelyContinuous' b hv
  rw [toReal_klDiv_of_measure_eq (hav.trans hvb) (by simp),
    integral_congr_ae (llr_gaussianReal a b v hv)]
  exact gaussKL_eq_integral a b v hvR

/-! ## 4. The instance -/

/-- **The open interface of `LeanPaperAEndgameV1`, discharged.**  The family's own
observation law really does have the Gaussian divergence, finite and with the stated value,
for every centred pair and every cell.  After this, `actual_kl_separation` and
`proxy_optimizer_misses_actual_information` carry no model hypothesis (their
`_unconditional` forms are below).  `family_operational_finish` is NOT closed by this: it
still takes `hfinite`, `hUpper` and `hLower`, the learner's operational obligations, and this
module removes only its `hKL` argument. -/
theorem gaussianKLIdentification_holds (r : ℕ) (M : ℝ) (hM : 0 < M) :
    GaussianKLIdentification r M hM := by
  intro θ lam hθ hlam e
  dsimp only
  have hpos : (0 : ℝ) < ((familyVariance r M hM e : NNReal) : ℝ) := pairVarC_pos M hM e
  have hvne : familyVariance r M hM e ≠ 0 := by
    intro hc
    rw [hc] at hpos
    simp at hpos
  simp only [observationLaw, queryMean_eq θ hθ, queryMean_eq lam hlam]
  refine ⟨klDiv_gaussianReal_ne_top _ _ _ hvne, ?_⟩
  rw [toReal_klDiv_gaussianReal _ _ _ hvne]
  rfl

/-- The unconditional form of the separation at the actual observation model. -/
theorem actual_kl_separation_unconditional {r : ℕ} (M : ℝ) (hM : 0 < M) (hr : 0 < r)
    [NeZero r] :
    4 / (4 + 2 * (r : ℝ) * M) ≤ actualKLGame r M hM / frozenGameC₀ r M ∧
    actualKLGame r M hM / frozenGameC₀ r M ≤ 64 / (9 * M * (r : ℝ)) :=
  actual_kl_separation M hM hr (gaussianKLIdentification_holds r M hM)

/-- The starvation statement, likewise with no model hypothesis left. -/
theorem proxy_optimizer_misses_actual_information_unconditional {r : ℕ} (M : ℝ) (hM : 0 < M)
    (hr : 0 < r) [NeZero r] :
    0 < actualKLGame r M hM ∧ ∀ w : Cell r → ℝ, IsAlloc w →
      frozenValueC₀ M w = frozenGameC₀ r M → actualKLValue M hM w = 0 :=
  proxy_optimizer_misses_actual_information M hM hr (gaussianKLIdentification_holds r M hM)

/-! ## Audit -/

#print axioms log_pdf_ratio
#print axioms llr_gaussianReal
#print axioms integrable_llr_gaussianReal
#print axioms klDiv_gaussianReal_ne_top
#print axioms toReal_klDiv_gaussianReal
#print axioms gaussianKLIdentification_holds
#print axioms actual_kl_separation_unconditional
#print axioms proxy_optimizer_misses_actual_information_unconditional

end CIGAMF.P13.PaperAGaussianKL
