import «LeanPaperBConcentrationV1»
import «LeanPaperBObstructionV1»

/-!
# Paper A: the exact transcript divergence of an adaptive protocol, and the change of measure

Paper B's lower bound (`LeanPaperBProtocolV1.transcript_kl_le`) bounds each round's
conditional divergence by a chi-square, which is enough for an ORDER.  Paper A needs the exact
constant `1/Gamma`, so the per-round divergence must be the per-query KL itself.  This module
proves, on the same adaptive protocol (history law `hist`, any randomised policy):

* `klDiv_withDensity_eq` -- `KL(nu p ‖ nu q) = ∫⁻ q klFun(p/q) dnu`, an equality in
  `lintegral` form (no integrability hypothesis);
* `klDiv_compProd_densKernel_eq` -- the conditional divergence of two density kernels is the
  AVERAGE of the per-`x` divergences (Tonelli), the integral form Mathlib's chain rule leaves
  implicit;
* `transcript_kl_le_qsum` -- `KL(hist_theta,n ‖ hist_lambda,n) <= E_theta sum_{i<n} KL_{q_i}`,
  the per-query divergence of the query actually issued at each round;
* `qsum_eq_count`, `lintegral_qsum_eq` -- that sum is `sum_q E_theta[N_q] KL_q`;
* `change_of_measure` -- an event of probability `>= 1 - delta` under `theta` and `<= delta`
  under `lambda` forces `sum_q E_theta[N_q] KL_q(theta ‖ lambda) >= (1-delta) log(1/delta) - log 2`.
-/

namespace CIGAMF.P13.PaperALowerKL

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBChiSq CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperBConcentration
open CIGAMF.P13.PaperBKernel CIGAMF.P13.PaperBObstruction

/-! ## 1. The divergence of two density laws, and of two density kernels -/

section Density

variable {α : Type*} [MeasurableSpace α]

/-- **KL of two density laws, exactly.** -/
theorem klDiv_withDensity_eq (ν : Measure α) [SigmaFinite ν] {p q : α → ℝ≥0∞}
    (hp : Measurable p) (hq : Measurable q) (hq0 : ∀ x, q x ≠ 0) (hqt : ∀ x, q x ≠ ∞)
    [IsFiniteMeasure (ν.withDensity p)] [IsFiniteMeasure (ν.withDensity q)] :
    klDiv (ν.withDensity p) (ν.withDensity q)
      = ∫⁻ x, ENNReal.ofReal ((q x).toReal * klFun ((p x).toReal / (q x).toReal)) ∂ν := by
  have hPν : ν.withDensity p ≪ ν := withDensity_absolutelyContinuous ν p
  have hνQ : ν ≪ ν.withDensity q :=
    withDensity_absolutelyContinuous' hq.aemeasurable (Filter.Eventually.of_forall hq0)
  have hQν : ν.withDensity q ≪ ν := withDensity_absolutelyContinuous ν q
  have hac : ν.withDensity p ≪ ν.withDensity q := hPν.trans hνQ
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
      (InformationTheory.measurable_klFun.comp ((hq.inv.mul hp).ennreal_toReal))
  calc ∫⁻ x, ENNReal.ofReal (klFun ((ν.withDensity p).rnDeriv (ν.withDensity q) x).toReal)
          ∂(ν.withDensity q)
      = ∫⁻ x, ENNReal.ofReal (klFun (((q x)⁻¹ * p x).toReal)) ∂(ν.withDensity q) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hrnQ] with x hx
        rw [hx]
    _ = ∫⁻ x, q x * ENNReal.ofReal (klFun (((q x)⁻¹ * p x).toReal)) ∂ν :=
        lintegral_withDensity_eq_lintegral_mul ν hq hmeas
    _ = ∫⁻ x, ENNReal.ofReal ((q x).toReal * klFun ((p x).toReal / (q x).toReal)) ∂ν := by
        refine lintegral_congr fun x => ?_
        have hb : 0 < (q x).toReal := ENNReal.toReal_pos (hq0 x) (hqt x)
        have hratio : ((q x)⁻¹ * p x).toReal = (p x).toReal / (q x).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_inv_mul]
        rw [hratio, ENNReal.ofReal_mul hb.le, ENNReal.ofReal_toReal (hqt x)]

end Density

section Kernel

variable {X : Type*} [MeasurableSpace X]

/-- **The conditional divergence of two density kernels is the average divergence.** -/
theorem klDiv_compProd_densKernel_eq (μ : Measure X) [IsFiniteMeasure μ] (ref : Measure ℝ)
    [SigmaFinite ref] (p q : X → ℝ → ℝ≥0∞)
    (hp : Measurable (Function.uncurry p)) (hq : Measurable (Function.uncurry q))
    (hpt : ∀ x y, p x y ≠ ∞) (hq0 : ∀ x y, q x y ≠ 0) (hqt : ∀ x y, q x y ≠ ∞)
    (hpm : ∀ x, ∫⁻ y, p x y ∂ref = 1) (hqm : ∀ x, ∫⁻ y, q x y ∂ref = 1) :
    klDiv (μ ⊗ₘ densKernel ref p) (μ ⊗ₘ densKernel ref q)
      = ∫⁻ x, klDiv (ref.withDensity (p x)) (ref.withDensity (q x)) ∂μ := by
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
  rw [klDiv_withDensity_eq (μ.prod ref) (p := fun z => p z.1 z.2) (q := fun z => q z.1 z.2)
    hp hq (fun z => hq0 z.1 z.2) (fun z => hqt z.1 z.2)]
  have hmeas : Measurable fun z : X × ℝ =>
      ENNReal.ofReal ((q z.1 z.2).toReal * klFun ((p z.1 z.2).toReal / (q z.1 z.2).toReal)) :=
    ENNReal.measurable_ofReal.comp (hq.ennreal_toReal.mul
      (InformationTheory.measurable_klFun.comp (hp.ennreal_toReal.div hq.ennreal_toReal)))
  rw [lintegral_prod _ hmeas.aemeasurable]
  refine lintegral_congr fun x => ?_
  have hpx : Measurable (p x) := hp.comp measurable_prodMk_left
  have hqx : Measurable (q x) := hq.comp measurable_prodMk_left
  haveI : IsFiniteMeasure (ref.withDensity (p x)) := ⟨by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hpm x]
    exact ENNReal.one_lt_top⟩
  haveI : IsFiniteMeasure (ref.withDensity (q x)) := ⟨by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hqm x]
    exact ENNReal.one_lt_top⟩
  rw [klDiv_withDensity_eq ref hpx hqx (hq0 x) (hqt x)]

end Kernel

/-! ## 2. The transcript divergence on the adaptive protocol -/

variable {W Q : Type*} [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q]
  [DecidableEq Q]

/-- The per-query divergence between two worlds' observation laws. -/
noncomputable def klq (C : Channel W Q) (θ l : W) (q : Q) : ℝ≥0∞ :=
  klDiv (obsLawC C θ q) (obsLawC C l q)

theorem obsLawC_eq (C : Channel W Q) (w : W) (n : ℕ) (x : Hist Q n × Q) :
    volume.withDensity (obsDens C w n x) = obsLawC C w x.2 := rfl

/-- **One round of the protocol costs the divergence of the query issued.** -/
theorem kl_succ_exact (C : Channel W Q) (π : Policy Q) (θ l : W) (n : ℕ) :
    klDiv (hist C π θ (n + 1)) (hist C π l (n + 1))
      ≤ klDiv (hist C π θ n) (hist C π l n)
        + ∫⁻ x, klq C θ l x.2 ∂((hist C π θ n) ⊗ₘ π.step n) := by
  haveI := hist_prob C π θ n
  haveI := hist_prob C π l n
  haveI := π.markov n
  haveI := obsKernel_markov C θ n
  haveI := obsKernel_markov C l n
  simp only [hist]
  calc klDiv ((((hist C π θ n) ⊗ₘ π.step n) ⊗ₘ obsKernel C θ n).map (snocMap n))
        ((((hist C π l n) ⊗ₘ π.step n) ⊗ₘ obsKernel C l n).map (snocMap n))
      ≤ klDiv (((hist C π θ n) ⊗ₘ π.step n) ⊗ₘ obsKernel C θ n)
          (((hist C π l n) ⊗ₘ π.step n) ⊗ₘ obsKernel C l n) :=
        klDiv_map_le _ _ (measurable_snocMap n)
    _ = klDiv (hist C π θ n) (hist C π l n)
          + klDiv (((hist C π θ n) ⊗ₘ π.step n) ⊗ₘ obsKernel C θ n)
              (((hist C π θ n) ⊗ₘ π.step n) ⊗ₘ obsKernel C l n) :=
        round_kl_eq _ _ _ _ _
    _ = klDiv (hist C π θ n) (hist C π l n)
          + ∫⁻ x, klq C θ l x.2 ∂((hist C π θ n) ⊗ₘ π.step n) := by
        congr 1
        exact klDiv_compProd_densKernel_eq _ volume (obsDens C θ n) (obsDens C l n)
          (measurable_obsDens C θ n) (measurable_obsDens C l n)
          (fun _ _ => ENNReal.ofReal_ne_top)
          (fun x y => (ENNReal.ofReal_pos.mpr (C.pos l x.2 y)).ne')
          (fun _ _ => ENNReal.ofReal_ne_top)
          (fun x => C.mass θ x.2) (fun x => C.mass l x.2)
    _ ≤ _ := le_rfl

/-- The accumulated per-query quantity along a history. -/
noncomputable def qsum (f : Q → ℝ≥0∞) (n : ℕ) (ω : Hist Q n) : ℝ≥0∞ :=
  ∑ i : Fin n, f (ω i).1

theorem qsum_snoc (f : Q → ℝ≥0∞) (n : ℕ) (p : (Hist Q n × Q) × ℝ) :
    qsum f (n + 1) (snocMap n p) = qsum f n p.1.1 + f p.1.2 := by
  unfold qsum snocMap
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem measurable_qsum (f : Q → ℝ≥0∞) (n : ℕ) : Measurable (qsum f n) := by
  unfold qsum
  refine Finset.measurable_sum _ fun i _ => ?_
  exact (Measurable.of_discrete (f := f)).comp (measurable_fst.comp (measurable_pi_apply i))

/-- The recursion of the accumulated quantity. -/
theorem lintegral_qsum_succ (C : Channel W Q) (π : Policy Q) (w : W) (f : Q → ℝ≥0∞) (n : ℕ) :
    ∫⁻ ω, qsum f (n + 1) ω ∂hist C π w (n + 1)
      = ∫⁻ ω, qsum f n ω ∂hist C π w n + ∫⁻ x, f x.2 ∂((hist C π w n) ⊗ₘ π.step n) := by
  haveI := hist_prob C π w n
  haveI := π.markov n
  haveI := obsKernel_markov C w n
  have hf : Measurable f := Measurable.of_discrete
  have hmf : Measurable fun x : Hist Q n × Q => qsum f n x.1 + f x.2 :=
    ((measurable_qsum f n).comp measurable_fst).add (hf.comp measurable_snd)
  simp only [hist]
  rw [lintegral_map (measurable_qsum f (n + 1)) (measurable_snocMap n)]
  simp_rw [qsum_snoc]
  rw [lintegral_compProd_fst _ _ hmf,
    lintegral_add_left (f := fun x : Hist Q n × Q => qsum f n x.1)
      ((measurable_qsum f n).comp measurable_fst),
    lintegral_compProd_fst _ _ (measurable_qsum f n)]

/-- **The transcript divergence is at most the expected accumulated per-query divergence.** -/
theorem transcript_kl_le_qsum (C : Channel W Q) (π : Policy Q) (θ l : W) :
    ∀ n, klDiv (hist C π θ n) (hist C π l n) ≤ ∫⁻ ω, qsum (klq C θ l) n ω ∂hist C π θ n
  | 0 => by
      haveI := hist_prob C π l 0
      have : hist C π θ 0 = hist C π l 0 := rfl
      rw [this, klDiv_self]
      exact bot_le
  | n + 1 => by
      calc klDiv (hist C π θ (n + 1)) (hist C π l (n + 1))
          ≤ klDiv (hist C π θ n) (hist C π l n)
              + ∫⁻ x, klq C θ l x.2 ∂((hist C π θ n) ⊗ₘ π.step n) := kl_succ_exact C π θ l n
        _ ≤ ∫⁻ ω, qsum (klq C θ l) n ω ∂hist C π θ n
              + ∫⁻ x, klq C θ l x.2 ∂((hist C π θ n) ⊗ₘ π.step n) :=
            add_le_add (transcript_kl_le_qsum C π θ l n) le_rfl
        _ = ∫⁻ ω, qsum (klq C θ l) (n + 1) ω ∂hist C π θ (n + 1) :=
            (lintegral_qsum_succ C π θ (klq C θ l) n).symm

/-! ## 3. Counts -/

/-- The number of rounds of a history that issued query `q`. -/
noncomputable def cntQ (q : Q) (n : ℕ) (ω : Hist Q n) : ℝ≥0∞ :=
  ∑ i : Fin n, if (ω i).1 = q then 1 else 0

theorem qsum_eq_count [Fintype Q] (f : Q → ℝ≥0∞) (n : ℕ) (ω : Hist Q n) :
    qsum f n ω = ∑ q, cntQ q n ω * f q := by
  unfold qsum cntQ
  have : ∀ i : Fin n, f (ω i).1 = ∑ q, (if (ω i).1 = q then 1 else 0) * f q := by
    intro i
    rw [Finset.sum_eq_single (ω i).1]
    · simp
    · intro b _ hb; rw [if_neg (Ne.symm hb), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_mul]

theorem measurable_cntQ (q : Q) (n : ℕ) : Measurable (cntQ q n) := by
  unfold cntQ
  refine Finset.measurable_sum _ fun i _ => ?_
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (measurable_fst.comp (measurable_pi_apply i)) (measurableSet_singleton q)

/-- **The expected accumulated divergence is `sum_q E[N_q] KL_q`.** -/
theorem lintegral_qsum_eq [Fintype Q] (μ : Measure (Hist Q n)) (f : Q → ℝ≥0∞) :
    ∫⁻ ω, qsum f n ω ∂μ = ∑ q, (∫⁻ ω, cntQ q n ω ∂μ) * f q := by
  simp_rw [qsum_eq_count]
  rw [lintegral_finset_sum _ fun q _ => (measurable_cntQ q n).mul_const _]
  refine Finset.sum_congr rfl fun q _ => ?_
  exact lintegral_mul_const _ (measurable_cntQ q n)

/-! ## 4. The change of measure -/

/-- **The change of measure for any randomised adaptive policy.**  An event that has
probability at least `1 - delta` in world `theta` and at most `delta` in world `lambda`
forces the expected counts to carry divergence `(1 - delta) log(1/delta) - log 2`. -/
theorem change_of_measure [Fintype Q] (C : Channel W Q) (π : Policy Q) (θ l : W) (n : ℕ)
    (S : Set (Hist Q n)) (hS : MeasurableSet S) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hθ : 1 - δ ≤ (hist C π θ n).real S) (hl : (hist C π l n).real S ≤ δ) :
    ENNReal.ofReal ((1 - δ) * Real.log (1 / δ) - Real.log 2)
      ≤ ∑ q, (∫⁻ ω, cntQ q n ω ∂hist C π θ n) * klq C θ l q := by
  haveI := hist_prob C π θ n
  haveI := hist_prob C π l n
  have hev := event_klDiv_ge (hist C π θ n) (hist C π l n) S hS δ hδ hl
  have hlog : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  calc ENNReal.ofReal ((1 - δ) * Real.log (1 / δ) - Real.log 2)
      ≤ ENNReal.ofReal ((hist C π θ n).real S * Real.log (1 / δ) - Real.log 2) := by
        apply ENNReal.ofReal_le_ofReal
        have := mul_le_mul_of_nonneg_right hθ hlog
        linarith
    _ ≤ klDiv (hist C π θ n) (hist C π l n) := hev
    _ ≤ ∫⁻ ω, qsum (klq C θ l) n ω ∂hist C π θ n := transcript_kl_le_qsum C π θ l n
    _ = ∑ q, (∫⁻ ω, cntQ q n ω ∂hist C π θ n) * klq C θ l q := lintegral_qsum_eq _ _

#print axioms klDiv_withDensity_eq
#print axioms klDiv_compProd_densKernel_eq
#print axioms kl_succ_exact
#print axioms transcript_kl_le_qsum
#print axioms lintegral_qsum_eq
#print axioms change_of_measure

end CIGAMF.P13.PaperALowerKL
