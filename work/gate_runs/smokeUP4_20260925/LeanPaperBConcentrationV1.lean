import «LeanPaperBProtocolV1»

/-!
# Paper B: concentration on the protocol's own history law

The decoder's error bound needs Hoeffding for the running sum of a bounded feature of the
observations.  `LeanPaperBHoeffdingV1` states Hoeffding for INDEPENDENT summands; the history
law of `LeanPaperBProtocolV1` is not presented as a product, it is a recursion of
compositions.  Rather than prove an independence statement about that recursion, this module
proves the bound directly on it, round by round, which also covers adaptive query choices:

* `step_mgf_le` -- Hoeffding's lemma (`hasSubgaussianMGF_of_mem_Icc`) for ONE round: a
  feature with values in `[-1,1]`, centred at its mean under the round's observation law,
  has `E exp(l (phi - m)) <= exp(l^2/2)`;
* `mgf_hist_le` -- by induction along `hist`, the centred running sum `centredSum` has
  `E exp(l S_n) <= exp(n l^2/2)`.  The centring uses the mean of the query ACTUALLY ISSUED,
  so an adaptive policy is allowed;
* `tail_hist_le` -- Chernoff: `P(S_n >= eps) <= exp(-eps^2/(2n))`.

All integrals are `lintegral`s of `ofReal exp`, so no integrability side condition appears.
-/

namespace CIGAMF.P13.PaperBConcentration

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBChiSq CIGAMF.P13.PaperBProtocol

variable {W Q : Type*} [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q]
  [DecidableEq Q]

/-- The observation law of query `q` in world `w`. -/
noncomputable def obsLawC (C : Channel W Q) (w : W) (q : Q) : Measure ℝ :=
  volume.withDensity (fun y => ENNReal.ofReal (C.dens w q y))

instance obsLawC_prob (C : Channel W Q) (w : W) (q : Q) : IsProbabilityMeasure (obsLawC C w q) :=
  ⟨by rw [obsLawC, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      exact C.mass w q⟩

/-- A feature of the observation, bounded by one, per query. -/
structure Feature (Q : Type*) where
  φ : Q → ℝ → ℝ
  meas : ∀ q, Measurable (φ q)
  bdd : ∀ q y, |φ q y| ≤ 1

/-- The feature's mean under the query's observation law in world `w`. -/
noncomputable def fmean (C : Channel W Q) (w : W) (F : Feature Q) (q : Q) : ℝ :=
  ∫ y, F.φ q y ∂obsLawC C w q

/-- The centred running sum of the feature along a history. -/
noncomputable def centredSum (C : Channel W Q) (w : W) (F : Feature Q) (n : ℕ)
    (ω : Hist Q n) : ℝ :=
  ∑ i : Fin n, (F.φ (ω i).1 (ω i).2 - fmean C w F (ω i).1)

theorem centredSum_snoc (C : Channel W Q) (w : W) (F : Feature Q) (n : ℕ)
    (p : (Hist Q n × Q) × ℝ) :
    centredSum C w F (n + 1) (snocMap n p)
      = centredSum C w F n p.1.1 + (F.φ p.1.2 p.2 - fmean C w F p.1.2) := by
  unfold centredSum snocMap
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem measurable_centredSum (C : Channel W Q) (w : W) (F : Feature Q) (n : ℕ) :
    Measurable (centredSum C w F n) := by
  unfold centredSum
  refine Finset.measurable_sum _ (fun i _ => ?_)
  have hφ : Measurable fun p : Q × ℝ => F.φ p.1 p.2 :=
    measurable_from_prod_countable_right fun q => F.meas q
  have hm : Measurable fun p : Q × ℝ => fmean C w F p.1 :=
    (Measurable.of_discrete (f := fmean C w F)).comp measurable_fst
  exact (hφ.sub hm).comp (measurable_pi_apply i)

/-- **One round of Hoeffding's lemma**, as a `lintegral`. -/
theorem step_mgf_le (C : Channel W Q) (w : W) (F : Feature Q) (q : Q) (l : ℝ) :
    ∫⁻ y, ENNReal.ofReal (exp (l * (F.φ q y - fmean C w F q))) ∂obsLawC C w q
      ≤ ENNReal.ofReal (exp (l ^ 2 / 2)) := by
  have hb : ∀ᵐ y ∂obsLawC C w q, F.φ q y ∈ Set.Icc (-1 : ℝ) 1 :=
    Filter.Eventually.of_forall fun y => abs_le.mp (F.bdd q y)
  have hsg := hasSubgaussianMGF_of_mem_Icc (F.meas q).aemeasurable hb
  have hc : ((‖(1 : ℝ) - (-1 : ℝ)‖₊ / 2) ^ 2) = (1 : ℝ≥0) := by norm_num
  rw [hc] at hsg
  have hmgf := hsg.mgf_le l
  have hint : Integrable (fun y => exp (l * (F.φ q y - fmean C w F q))) (obsLawC C w q) :=
    hsg.integrable_exp_mul l
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun y => (exp_pos _).le)]
  refine ENNReal.ofReal_le_ofReal ?_
  have : mgf (fun y => F.φ q y - ∫ z, F.φ q z ∂obsLawC C w q) (obsLawC C w q) l
      = ∫ y, exp (l * (F.φ q y - fmean C w F q)) ∂obsLawC C w q := rfl
  rw [← this]
  simpa using hmgf

/-- The observation kernel is the query's observation law. -/
theorem obsKernel_apply (C : Channel W Q) (w : W) (n : ℕ) (x : Hist Q n × Q) :
    obsKernel C w n x = obsLawC C w x.2 := by
  haveI : IsSFiniteKernel (obsKernel C w n) :=
    densKernel_sfinite volume _ (fun x y => ENNReal.ofReal_ne_top)
  unfold obsKernel densKernel obsLawC
  rw [Kernel.withDensity_apply _ (measurable_obsDens C w n), Kernel.const_apply]
  rfl

/-- **The running sum's MGF, along the actual recursion.** -/
theorem mgf_hist_le (C : Channel W Q) (pol : Policy Q) (w : W) (F : Feature Q) (l : ℝ) :
    ∀ n, ∫⁻ ω, ENNReal.ofReal (exp (l * centredSum C w F n ω)) ∂hist C pol w n
      ≤ ENNReal.ofReal (exp (n * (l ^ 2 / 2)))
  | 0 => by
      haveI := hist_prob C pol w 0
      simp [centredSum]
  | n + 1 => by
      haveI := hist_prob C pol w n
      haveI := pol.markov n
      haveI := obsKernel_markov C w n
      have hmS : Measurable fun ω : Hist Q (n + 1) =>
          ENNReal.ofReal (exp (l * centredSum C w F (n + 1) ω)) :=
        ENNReal.measurable_ofReal.comp
          (measurable_exp.comp (measurable_const.mul (measurable_centredSum C w F (n + 1))))
      have hmn : Measurable fun ω : Hist Q n =>
          ENNReal.ofReal (exp (l * centredSum C w F n ω)) :=
        ENNReal.measurable_ofReal.comp
          (measurable_exp.comp (measurable_const.mul (measurable_centredSum C w F n)))
      have hφ : Measurable fun p : Q × ℝ => F.φ p.1 p.2 :=
        measurable_from_prod_countable_right fun q => F.meas q
      have hmstep : Measurable fun p : (Hist Q n × Q) × ℝ =>
          ENNReal.ofReal (exp (l * centredSum C w F n p.1.1))
            * ENNReal.ofReal (exp (l * (F.φ p.1.2 p.2 - fmean C w F p.1.2))) := by
        refine (hmn.comp measurable_fst.fst).mul ?_
        refine ENNReal.measurable_ofReal.comp (measurable_exp.comp (measurable_const.mul ?_))
        exact (hφ.comp ((measurable_fst.snd).prodMk measurable_snd)).sub
          ((Measurable.of_discrete (f := fmean C w F)).comp measurable_fst.snd)
      simp only [hist]
      rw [lintegral_map hmS (measurable_snocMap n)]
      have hsplit : ∀ p : (Hist Q n × Q) × ℝ,
          ENNReal.ofReal (exp (l * centredSum C w F (n + 1) (snocMap n p)))
            = ENNReal.ofReal (exp (l * centredSum C w F n p.1.1))
              * ENNReal.ofReal (exp (l * (F.φ p.1.2 p.2 - fmean C w F p.1.2))) := by
        intro p
        rw [centredSum_snoc, mul_add, exp_add,
          ENNReal.ofReal_mul (exp_pos _).le]
      simp_rw [hsplit]
      rw [Measure.lintegral_compProd hmstep]
      calc ∫⁻ x, ∫⁻ y, ENNReal.ofReal (exp (l * centredSum C w F n x.1))
              * ENNReal.ofReal (exp (l * (F.φ x.2 y - fmean C w F x.2)))
              ∂(obsKernel C w n x) ∂((hist C pol w n) ⊗ₘ pol.step n)
          ≤ ∫⁻ x, ENNReal.ofReal (exp (l * centredSum C w F n x.1))
              * ENNReal.ofReal (exp (l ^ 2 / 2)) ∂((hist C pol w n) ⊗ₘ pol.step n) := by
            refine lintegral_mono fun x => ?_
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, obsKernel_apply]
            exact mul_le_mul_right (step_mgf_le C w F x.2 l) _
        _ = ENNReal.ofReal (exp (l ^ 2 / 2))
              * ∫⁻ x, ENNReal.ofReal (exp (l * centredSum C w F n x)) ∂hist C pol w n := by
            rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm]
            congr 1
            exact lintegral_compProd_fst _ _ hmn
        _ ≤ ENNReal.ofReal (exp (l ^ 2 / 2)) * ENNReal.ofReal (exp (n * (l ^ 2 / 2))) :=
            mul_le_mul_right (mgf_hist_le C pol w F l n) _
        _ = ENNReal.ofReal (exp (((n + 1 : ℕ) : ℝ) * (l ^ 2 / 2))) := by
            rw [← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add]
            congr 2
            push_cast
            ring

/-- **Chernoff on the history law**: `P(S_n >= eps) <= exp(-eps^2/(2n))`. -/
theorem tail_hist_le (C : Channel W Q) (pol : Policy Q) (w : W) (F : Feature Q) (n : ℕ)
    (hn : 0 < n) (ε : ℝ) (hε : 0 ≤ ε) :
    hist C pol w n {ω | ε ≤ centredSum C w F n ω}
      ≤ ENNReal.ofReal (exp (-(ε ^ 2) / (2 * n))) := by
  haveI := hist_prob C pol w n
  set l : ℝ := ε / n with hl
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmeas : Measurable fun ω : Hist Q n => ENNReal.ofReal (exp (l * centredSum C w F n ω)) :=
    ENNReal.measurable_ofReal.comp
      (measurable_exp.comp (measurable_const.mul (measurable_centredSum C w F n)))
  have hsub : {ω | ε ≤ centredSum C w F n ω}
      ⊆ {ω | ENNReal.ofReal (exp (l * ε)) ≤ ENNReal.ofReal (exp (l * centredSum C w F n ω))} := by
    intro ω hω
    have hl0 : 0 ≤ l := div_nonneg hε hnR.le
    exact ENNReal.ofReal_le_ofReal (exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω hl0))
  have hmarkov := mul_meas_ge_le_lintegral (μ := hist C pol w n) hmeas (ENNReal.ofReal (exp (l * ε)))
  have hmgf := mgf_hist_le C pol w F l n
  have hpos : ENNReal.ofReal (exp (l * ε)) ≠ 0 := (ENNReal.ofReal_pos.mpr (exp_pos _)).ne'
  calc hist C pol w n {ω | ε ≤ centredSum C w F n ω}
      ≤ hist C pol w n {ω | ENNReal.ofReal (exp (l * ε))
          ≤ ENNReal.ofReal (exp (l * centredSum C w F n ω))} := measure_mono hsub
    _ ≤ ENNReal.ofReal (exp (n * (l ^ 2 / 2))) / ENNReal.ofReal (exp (l * ε)) := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
        exact hmarkov.trans hmgf
    _ = ENNReal.ofReal (exp (-(ε ^ 2) / (2 * n))) := by
        rw [← ENNReal.ofReal_div_of_pos (exp_pos _), ← exp_sub]
        congr 2
        rw [hl]
        field_simp
        ring

#print axioms step_mgf_le
#print axioms mgf_hist_le
#print axioms tail_hist_le

end CIGAMF.P13.PaperBConcentration
