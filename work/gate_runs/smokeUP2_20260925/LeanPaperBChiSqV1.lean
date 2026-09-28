import Mathlib

/-!
# Paper B: KL is bounded by chi-square, for laws given by densities -- joint form included

The adaptive lower bound needs, at every round, an UPPER bound on the conditional divergence

    klDiv (mu ⊗ₘ O_theta) (mu ⊗ₘ O_lambda),

where `mu` is the law of the history-and-query and `O` the observation kernel.  Mathlib's
chain rule (`klDiv_compProd_eq_add`) isolates this term but does not evaluate it: the integral
form of the conditional divergence is not in the library.  An upper bound is all the lower
bound needs, and it can be had without that integral form, by going through chi-square and
staying in `lintegral`, where no integrability hypothesis is ever required:

* `klFun_le_sq` -- `klFun x <= (x - 1)^2` for `x >= 0`, i.e. `log x <= x - 1`;
* `klDiv_withDensity_le_chiSq` -- for two laws with densities `p, q > 0` against a common
  sigma-finite base,  `klDiv (nu.withDensity p) (nu.withDensity q) <= ∫⁻ (p - q)^2 / q dnu`;
* `klDiv_compProd_le_chiSq` -- the joint form: when the observation kernel has density
  `p x` against a fixed base `ref`, the joint law is `(mu.prod ref).withDensity p`, and
  Tonelli turns the joint chi-square into an average over `x` of per-`x` chi-squares.  A
  per-`x` bound `C x` therefore gives `klDiv <= ∫⁻ C x dmu` -- which is what makes the killed
  protocol work: after stopping, the two worlds' kernels coincide, `C x = 0` there, and the
  round costs only the mass of the histories that are still active.

This is the "workaround #7" of the B blueprint: the policy term is cancelled by
`round_kl_eq` (`LeanPaperBKernelV1`), and this module bounds what remains.
-/

namespace CIGAMF.P13.PaperBChiSq

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

/-! ## 1. The pointwise inequality -/

/-- `x log x + 1 - x <= (x - 1)^2` on `x >= 0`: it is `log x <= x - 1`, multiplied by `x`. -/
theorem klFun_le_sq (x : ℝ) (hx : 0 ≤ x) : klFun x ≤ (x - 1) ^ 2 := by
  unfold klFun
  rcases hx.eq_or_lt with rfl | hpos
  · simp
  · have hlog := Real.log_le_sub_one_of_pos hpos
    have := mul_le_mul_of_nonneg_left hlog hpos.le
    nlinarith

theorem measurable_klFun : Measurable klFun := by
  have : Continuous klFun := by
    unfold klFun
    exact (Real.continuous_mul_log.add continuous_const).sub continuous_id
  exact this.measurable

/-- The per-point bound after multiplying by the reference density `b = q > 0`. -/
theorem mul_klFun_div_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    b * klFun (a / b) ≤ (a - b) ^ 2 / b := by
  have h := klFun_le_sq (a / b) (div_nonneg ha hb.le)
  have hid : b * (a / b - 1) ^ 2 = (a - b) ^ 2 / b := by
    field_simp
    try ring
  calc b * klFun (a / b) ≤ b * (a / b - 1) ^ 2 := mul_le_mul_of_nonneg_left h hb.le
    _ = (a - b) ^ 2 / b := hid

/-! ## 2. KL <= chi-square for two densities -/

variable {α : Type*} [MeasurableSpace α]

/-- **KL is at most chi-square**, for two laws with densities against a common base.  The
right-hand side is a `lintegral`, so the statement needs no integrability hypothesis; it is
`∞` exactly when the chi-square is. -/
theorem klDiv_withDensity_le_chiSq (ν : Measure α) [SigmaFinite ν] {p q : α → ℝ≥0∞}
    (hp : Measurable p) (hq : Measurable q) (hpt : ∀ x, p x ≠ ∞) (hq0 : ∀ x, q x ≠ 0)
    (hqt : ∀ x, q x ≠ ∞) [IsFiniteMeasure (ν.withDensity p)]
    [IsFiniteMeasure (ν.withDensity q)] :
    klDiv (ν.withDensity p) (ν.withDensity q)
      ≤ ∫⁻ x, ENNReal.ofReal (((p x).toReal - (q x).toReal) ^ 2 / (q x).toReal) ∂ν := by
  have hPν : ν.withDensity p ≪ ν := withDensity_absolutelyContinuous ν p
  have hνQ : ν ≪ ν.withDensity q :=
    withDensity_absolutelyContinuous' hq.aemeasurable (Filter.Eventually.of_forall hq0)
  have hQν : ν.withDensity q ≪ ν := withDensity_absolutelyContinuous ν q
  have hac : ν.withDensity p ≪ ν.withDensity q := hPν.trans hνQ
  -- the Radon-Nikodym derivative is p / q, nu-almost everywhere, hence Q-almost everywhere
  have hrn : (ν.withDensity p).rnDeriv (ν.withDensity q) =ᵐ[ν] fun x => (q x)⁻¹ * p x := by
    have h1 := Measure.rnDeriv_withDensity_right (ν.withDensity p) ν hq.aemeasurable
      (Filter.Eventually.of_forall hq0) (Filter.Eventually.of_forall hqt)
    have h2 := Measure.rnDeriv_withDensity ν hp
    filter_upwards [h1, h2] with x hx1 hx2
    rw [hx1, hx2]
  have hrnQ := hQν.ae_le hrn
  rw [klDiv_eq_lintegral_klFun_of_ac hac]
  have hmeas : Measurable fun x => ENNReal.ofReal (klFun (((q x)⁻¹ * p x).toReal)) :=
    ENNReal.measurable_ofReal.comp
      (measurable_klFun.comp ((hq.inv.mul hp).ennreal_toReal))
  calc ∫⁻ x, ENNReal.ofReal (klFun ((ν.withDensity p).rnDeriv (ν.withDensity q) x).toReal)
          ∂(ν.withDensity q)
      = ∫⁻ x, ENNReal.ofReal (klFun (((q x)⁻¹ * p x).toReal)) ∂(ν.withDensity q) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hrnQ] with x hx
        rw [hx]
    _ = ∫⁻ x, q x * ENNReal.ofReal (klFun (((q x)⁻¹ * p x).toReal)) ∂ν :=
        lintegral_withDensity_eq_lintegral_mul ν hq hmeas
    _ ≤ ∫⁻ x, ENNReal.ofReal (((p x).toReal - (q x).toReal) ^ 2 / (q x).toReal) ∂ν := by
        refine lintegral_mono fun x => ?_
        have hb : 0 < (q x).toReal := ENNReal.toReal_pos (hq0 x) (hqt x)
        have hratio : ((q x)⁻¹ * p x).toReal = (p x).toReal / (q x).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_inv_mul]
        have hmul : q x * ENNReal.ofReal (klFun ((p x).toReal / (q x).toReal))
            = ENNReal.ofReal ((q x).toReal * klFun ((p x).toReal / (q x).toReal)) := by
          rw [ENNReal.ofReal_mul hb.le, ENNReal.ofReal_toReal (hqt x)]
        rw [hratio, hmul]
        exact ENNReal.ofReal_le_ofReal
          (mul_klFun_div_le _ _ ENNReal.toReal_nonneg hb)

/-! ## 3. The joint form, for an observation kernel with a density -/

variable {X : Type*} [MeasurableSpace X]

/-- The observation kernel with density `p x` against a fixed base law `ref`. -/
noncomputable def densKernel (ref : Measure ℝ) [SFinite ref] (p : X → ℝ → ℝ≥0∞) : Kernel X ℝ :=
  (Kernel.const X ref).withDensity p

/-- **The joint law is a density against the product base.** -/
theorem densKernel_sfinite (ref : Measure ℝ) [SFinite ref] (p : X → ℝ → ℝ≥0∞)
    (hpt : ∀ x y, p x y ≠ ∞) : IsSFiniteKernel (densKernel ref p) :=
  Kernel.IsSFiniteKernel.withDensity _ hpt

theorem compProd_densKernel (μ : Measure X) [SFinite μ] (ref : Measure ℝ) [SFinite ref]
    (p : X → ℝ → ℝ≥0∞) (hp : Measurable (Function.uncurry p)) (hpt : ∀ x y, p x y ≠ ∞) :
    μ ⊗ₘ densKernel ref p = (μ.prod ref).withDensity (fun z => p z.1 z.2) := by
  haveI : IsSFiniteKernel ((Kernel.const X ref).withDensity p) := densKernel_sfinite ref p hpt
  unfold densKernel
  rw [Measure.compProd_withDensity hp, Measure.compProd_const]

/-- The mass of the joint density law is the average of the per-`x` masses. -/
theorem joint_mass (μ : Measure X) [SFinite μ] (ref : Measure ℝ) [SFinite ref]
    (p : X → ℝ → ℝ≥0∞) (hp : Measurable (Function.uncurry p)) :
    (μ.prod ref).withDensity (fun z => p z.1 z.2) Set.univ = ∫⁻ x, ∫⁻ y, p x y ∂ref ∂μ := by
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact lintegral_prod (Function.uncurry p) hp.aemeasurable

/-- **The conditional divergence is at most the average per-`x` chi-square.** -/
theorem klDiv_compProd_le_chiSq (μ : Measure X) [IsFiniteMeasure μ] (ref : Measure ℝ)
    [SigmaFinite ref] (p q : X → ℝ → ℝ≥0∞)
    (hp : Measurable (Function.uncurry p)) (hq : Measurable (Function.uncurry q))
    (hpt : ∀ x y, p x y ≠ ∞) (hq0 : ∀ x y, q x y ≠ 0) (hqt : ∀ x y, q x y ≠ ∞)
    (hpm : ∀ x, ∫⁻ y, p x y ∂ref = 1) (hqm : ∀ x, ∫⁻ y, q x y ∂ref = 1) :
    klDiv (μ ⊗ₘ densKernel ref p) (μ ⊗ₘ densKernel ref q)
      ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal
          (((p x y).toReal - (q x y).toReal) ^ 2 / (q x y).toReal) ∂ref ∂μ := by
  rw [compProd_densKernel μ ref p hp hpt, compProd_densKernel μ ref q hq hqt]
  have : IsFiniteMeasure ((μ.prod ref).withDensity (fun z => p z.1 z.2)) := by
    refine ⟨?_⟩
    rw [joint_mass μ ref p hp]
    simp only [hpm, lintegral_const, one_mul]
    exact measure_lt_top μ Set.univ
  have : IsFiniteMeasure ((μ.prod ref).withDensity (fun z => q z.1 z.2)) := by
    refine ⟨?_⟩
    rw [joint_mass μ ref q hq]
    simp only [hqm, lintegral_const, one_mul]
    exact measure_lt_top μ Set.univ
  have h := klDiv_withDensity_le_chiSq (μ.prod ref) (p := fun z => p z.1 z.2)
    (q := fun z => q z.1 z.2) hp hq (fun z => hpt z.1 z.2) (fun z => hq0 z.1 z.2)
    (fun z => hqt z.1 z.2)
  refine h.trans (le_of_eq ?_)
  have hmeas : Measurable fun z : X × ℝ =>
      ENNReal.ofReal (((p z.1 z.2).toReal - (q z.1 z.2).toReal) ^ 2 / (q z.1 z.2).toReal) :=
    ENNReal.measurable_ofReal.comp
      (((hp.ennreal_toReal.sub hq.ennreal_toReal).pow_const 2).div hq.ennreal_toReal)
  exact lintegral_prod _ hmeas.aemeasurable

/-- **With a per-`x` bound**: if the chi-square at `x` is at most `C x`, the conditional
divergence is at most `∫⁻ C dmu`. -/
theorem klDiv_compProd_le_of_pointwise (μ : Measure X) [IsFiniteMeasure μ] (ref : Measure ℝ)
    [SigmaFinite ref] (p q : X → ℝ → ℝ≥0∞)
    (hp : Measurable (Function.uncurry p)) (hq : Measurable (Function.uncurry q))
    (hpt : ∀ x y, p x y ≠ ∞) (hq0 : ∀ x y, q x y ≠ 0) (hqt : ∀ x y, q x y ≠ ∞)
    (hpm : ∀ x, ∫⁻ y, p x y ∂ref = 1) (hqm : ∀ x, ∫⁻ y, q x y ∂ref = 1)
    (C : X → ℝ≥0∞)
    (hC : ∀ x, ∫⁻ y, ENNReal.ofReal
        (((p x y).toReal - (q x y).toReal) ^ 2 / (q x y).toReal) ∂ref ≤ C x) :
    klDiv (μ ⊗ₘ densKernel ref p) (μ ⊗ₘ densKernel ref q) ≤ ∫⁻ x, C x ∂μ :=
  (klDiv_compProd_le_chiSq μ ref p q hp hq hpt hq0 hqt hpm hqm).trans (lintegral_mono hC)

#print axioms klFun_le_sq
#print axioms mul_klFun_div_le
#print axioms klDiv_withDensity_le_chiSq
#print axioms compProd_densKernel
#print axioms klDiv_compProd_le_chiSq
#print axioms klDiv_compProd_le_of_pointwise

end CIGAMF.P13.PaperBChiSq
