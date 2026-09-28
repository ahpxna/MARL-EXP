import «LeanPaperAFreezeV1»
import «LeanPaperAMartingaleV1»

/-!
# Paper A7: the closed-form process is a martingale at a random past

`LeanPaperAMartingaleV1` proves the one-step identity at a FIXED past and lists five
obligations it does not discharge.  This module discharges the first four.

* **(1) measurability.**  The algorithm's bookkeeping is taken in its factorised form: the
  counts `Nf`, the sums `Sf` and the query `qf` are measurable functions OF THE PAST `X`.
  That is what "measurable with respect to the filtration" says, written the way an
  algorithm is written; the process is then `Mval` composed with `X`.
* **(2) the next innovation.**  `Y` is independent of `X` with law `gaussianReal 0 1`.  On
  the observation stream this is the product structure, nothing more.
* **(3) the identity at a random past.**  This is the freezing lemma of
  `LeanPaperAFreezeV1`, NOT the false claim that `S_e` given `N_e` is Gaussian.  The inner
  integral is evaluated by `one_step_mean` pointwise in the frozen past, which is exactly
  the substitution the fixed-past identity licenses.
* **(4) mean one and integrability.**  Both by induction, and integrability is DERIVED
  rather than assumed: Tonelli on the product turns the joint integral into the inner one,
  the inner one is evaluated by the same identity, and the finiteness propagates.

Only the fifth obligation --- joining `log M_t` to the implementation's own statistic and
threshold, and then Ville --- is left, and it is taken up in the next module.

The regularisation constant `a` is fixed throughout and the process is at a fixed true
parameter; substituting a time-varying estimate does not preserve any of this.
-/

namespace CIGAMF.P13.PaperAAdaptMart

open MeasureTheory
open CIGAMF.P13.PaperAFreeze
open CIGAMF.P13.PaperAMartingale
open CIGAMF.P13.PaperA7Confidence

variable {E : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace E]
  [MeasurableSingletonClass E]
variable {β : Type*} [MeasurableSpace β]

/-- The closed-form process, as a function of the past. -/
noncomputable def Mval (a : ℝ) (Nf : β → E → ℕ) (Sf : β → E → ℝ) (x : β) : ℝ :=
  ∏ e, mgfFactor a (Nf x e) (Sf x e)

/-- The process after one more observation: the queried arm's count and sum advance, and
nothing else moves. -/
noncomputable def Mstep (a : ℝ) (Nf : β → E → ℕ) (Sf : β → E → ℝ) (qf : β → E)
    (p : β × ℝ) : ℝ :=
  ∏ e, mgfFactor a ((Nf p.1 e : ℝ) + (if qf p.1 = e then 1 else 0))
                   (Sf p.1 e + (if qf p.1 = e then p.2 else 0))

theorem mgfFactor_pos (a n s : ℝ) (ha : 0 < a) (hn : 0 ≤ n) : 0 < mgfFactor a n s := by
  unfold mgfFactor
  have h1 : (0 : ℝ) < a / (a + n) := by positivity
  exact mul_pos (Real.sqrt_pos.mpr h1) (Real.exp_pos _)

theorem Mval_pos (a : ℝ) (ha : 0 < a) (Nf : β → E → ℕ) (Sf : β → E → ℝ) (x : β) :
    0 < Mval a Nf Sf x :=
  Finset.prod_pos (fun e _ => mgfFactor_pos a _ _ ha (by positivity))

/-- **The step factorises**: only the queried arm changes. -/
theorem Mstep_eq (a : ℝ) (Nf : β → E → ℕ) (Sf : β → E → ℝ) (qf : β → E) (x : β) (z : ℝ) :
    Mstep a Nf Sf qf (x, z)
      = mgfFactor a ((Nf x (qf x) : ℝ) + 1) (Sf x (qf x) + z)
        * ∏ e ∈ Finset.univ.erase (qf x), mgfFactor a (Nf x e) (Sf x e) := by
  classical
  unfold Mstep
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (qf x))]
  have hhead : mgfFactor a ((Nf x (qf x) : ℝ) + (if qf x = qf x then 1 else 0))
      (Sf x (qf x) + (if qf x = qf x then z else 0))
      = mgfFactor a ((Nf x (qf x) : ℝ) + 1) (Sf x (qf x) + z) := by
    rw [if_pos rfl, if_pos rfl]
  have htail : ∀ e ∈ Finset.univ.erase (qf x),
      mgfFactor a ((Nf x e : ℝ) + (if qf x = e then 1 else 0))
        (Sf x e + (if qf x = e then z else 0))
      = mgfFactor a (Nf x e) (Sf x e) := by
    intro e he
    have hne : qf x ≠ e := fun h => (Finset.mem_erase.mp he).1 h.symm
    rw [if_neg hne, if_neg hne, add_zero, add_zero]
  rw [hhead, Finset.prod_congr rfl htail]

/-- **The head factor, completed square.**  The queried arm's factor against the Gaussian
density is a constant times a Gaussian in the innovation. -/
theorem head_pointwise (a n s z : ℝ) (ha : 0 < a) (hn : 0 ≤ n) :
    mgfFactor a (n + 1) (s + z) * gaussianPDF 0 1 z
      = (Real.sqrt (a / (a + (n + 1)))
          * (Real.exp (s ^ 2 / (2 * (a + n))) / Real.sqrt (2 * Real.pi)))
        * Real.exp (-((a + n) / (2 * (a + n + 1))) * (z - s / (a + n)) ^ 2) := by
  have hv : (0 : ℝ) < a + n := by linarith
  have hv1 : (0 : ℝ) < a + n + 1 := by linarith
  unfold mgfFactor gaussianPDF
  have hexp : (s + z) ^ 2 / (2 * (a + (n + 1))) + -((z - 0) ^ 2 / (2 * 1 ^ 2))
      = s ^ 2 / (2 * (a + n)) + -((a + n) / (2 * (a + n + 1))) * (z - s / (a + n)) ^ 2 := by
    have hrw : a + (n + 1) = a + n + 1 := by ring
    rw [hrw]
    field_simp
    ring
  rw [show Real.sqrt (a / (a + (n + 1))) * Real.exp ((s + z) ^ 2 / (2 * (a + (n + 1))))
        * (Real.exp (-((z - 0) ^ 2 / (2 * 1 ^ 2))) / (1 * Real.sqrt (2 * Real.pi)))
      = Real.sqrt (a / (a + (n + 1)))
          * ((Real.exp ((s + z) ^ 2 / (2 * (a + (n + 1))))
              * Real.exp (-((z - 0) ^ 2 / (2 * 1 ^ 2)))) / Real.sqrt (2 * Real.pi)) by ring]
  rw [← Real.exp_add, hexp, Real.exp_add]
  ring

/-- **The inner integrand is integrable**, by the same completion of the square that
evaluates it. -/
theorem step_inner_integrable (a : ℝ) (ha : 0 < a)
    (Nf : β → E → ℕ) (Sf : β → E → ℝ) (qf : β → E) (x : β) :
    Integrable (fun z : ℝ => Mstep a Nf Sf qf (x, z) * gaussianPDF 0 1 z) volume := by
  classical
  have hn0 : (0 : ℝ) ≤ (Nf x (qf x) : ℝ) := by positivity
  have hb : (0 : ℝ) < ((a + (Nf x (qf x) : ℝ)) / (2 * (a + (Nf x (qf x) : ℝ) + 1))) := by
    have h1 : (0 : ℝ) < a + (Nf x (qf x) : ℝ) := by linarith
    positivity
  have hpoint : ∀ z : ℝ, Mstep a Nf Sf qf (x, z) * gaussianPDF 0 1 z
      = ((∏ e ∈ Finset.univ.erase (qf x), mgfFactor a (Nf x e) (Sf x e))
          * (Real.sqrt (a / (a + ((Nf x (qf x) : ℝ) + 1)))
            * (Real.exp ((Sf x (qf x)) ^ 2 / (2 * (a + (Nf x (qf x) : ℝ))))
                / Real.sqrt (2 * Real.pi))))
        * Real.exp (-((a + (Nf x (qf x) : ℝ)) / (2 * (a + (Nf x (qf x) : ℝ) + 1)))
            * (z - (Sf x (qf x)) / (a + (Nf x (qf x) : ℝ))) ^ 2) := by
    intro z
    rw [Mstep_eq, show (mgfFactor a ((Nf x (qf x) : ℝ) + 1) (Sf x (qf x) + z)
          * ∏ e ∈ Finset.univ.erase (qf x), mgfFactor a (Nf x e) (Sf x e))
        * gaussianPDF 0 1 z
        = (∏ e ∈ Finset.univ.erase (qf x), mgfFactor a (Nf x e) (Sf x e))
          * (mgfFactor a ((Nf x (qf x) : ℝ) + 1) (Sf x (qf x) + z) * gaussianPDF 0 1 z)
        from by ring,
      head_pointwise a (Nf x (qf x) : ℝ) (Sf x (qf x)) z ha hn0]
    ring
  rw [show (fun z : ℝ => Mstep a Nf Sf qf (x, z) * gaussianPDF 0 1 z)
      = (fun z : ℝ => ((∏ e ∈ Finset.univ.erase (qf x), mgfFactor a (Nf x e) (Sf x e))
          * (Real.sqrt (a / (a + ((Nf x (qf x) : ℝ) + 1)))
            * (Real.exp ((Sf x (qf x)) ^ 2 / (2 * (a + (Nf x (qf x) : ℝ))))
                / Real.sqrt (2 * Real.pi))))
        * Real.exp (-((a + (Nf x (qf x) : ℝ)) / (2 * (a + (Nf x (qf x) : ℝ) + 1)))
            * (z - (Sf x (qf x)) / (a + (Nf x (qf x) : ℝ))) ^ 2)) from funext hpoint]
  exact Integrable.const_mul
    ((integrable_exp_neg_mul_sq hb).comp_sub_right ((Sf x (qf x)) / (a + (Nf x (qf x) : ℝ)))) _

/-- **The inner integral, evaluated.**  The queried arm's factor averages to its own
predecessor, and the rest of the product is untouched. -/
theorem step_inner_integral (a : ℝ) (ha : 0 < a)
    (Nf : β → E → ℕ) (Sf : β → E → ℝ) (qf : β → E) (x : β) :
    ∫ z : ℝ, Mstep a Nf Sf qf (x, z) * gaussianPDF 0 1 z = Mval a Nf Sf x := by
  classical
  have hn0 : (0 : ℝ) ≤ (Nf x (qf x) : ℝ) := by positivity
  have hrw : ∀ z : ℝ, Mstep a Nf Sf qf (x, z) * gaussianPDF 0 1 z
      = (∏ e ∈ Finset.univ.erase (qf x), mgfFactor a (Nf x e) (Sf x e))
        * (mgfFactor a ((Nf x (qf x) : ℝ) + 1) (Sf x (qf x) + z) * gaussianPDF 0 1 z) := by
    intro z
    rw [Mstep_eq]
    ring
  rw [show (fun z : ℝ => Mstep a Nf Sf qf (x, z) * gaussianPDF 0 1 z)
      = (fun z : ℝ => (∏ e ∈ Finset.univ.erase (qf x), mgfFactor a (Nf x e) (Sf x e))
        * (mgfFactor a ((Nf x (qf x) : ℝ) + 1) (Sf x (qf x) + z) * gaussianPDF 0 1 z))
      from funext hrw]
  rw [MeasureTheory.integral_const_mul,
    one_step_mean a (Nf x (qf x) : ℝ) (Sf x (qf x)) ha hn0]
  unfold Mval
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (qf x))]
  ring

/-! ## The martingale step, at a random past -/

theorem gaussianPDF_eq (y : ℝ) :
    ProbabilityTheory.gaussianPDFReal 0 1 y = gaussianPDF 0 1 y := by
  have h2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hp : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  unfold ProbabilityTheory.gaussianPDFReal gaussianPDF
  norm_num
  rw [show (-y ^ 2 / 2 : ℝ) = -(y ^ 2 / 2) from by ring]
  field_simp

/-- Integration against the standard Gaussian law is integration against its density. -/
theorem integral_gaussian_bridge (g : ℝ → ℝ) :
    ∫ z, g z ∂(ProbabilityTheory.gaussianReal 0 1) = ∫ z, g z * gaussianPDF 0 1 z := by
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul (by norm_num)]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  show ProbabilityTheory.gaussianPDFReal 0 1 z • g z = g z * gaussianPDF 0 1 z
  rw [smul_eq_mul, gaussianPDF_eq]
  ring

/-- **The inner integral against the law.** -/
theorem step_inner_integral_law (a : ℝ) (ha : 0 < a)
    (Nf : β → E → ℕ) (Sf : β → E → ℝ) (qf : β → E) (x : β) :
    ∫ z, Mstep a Nf Sf qf (x, z) ∂(ProbabilityTheory.gaussianReal 0 1)
      = Mval a Nf Sf x := by
  rw [integral_gaussian_bridge (fun z => Mstep a Nf Sf qf (x, z))]
  exact step_inner_integral a ha Nf Sf qf x

/-- **The martingale step.**  The one-step identity, applied at a RANDOM past through the
freezing lemma.  `X` is the past, `Y` the fresh innovation; nothing here assumes anything
about the conditional law of `S_e` given `N_e`. -/
theorem martingale_step {α : Type*} {mα : MeasurableSpace α} (μ : Measure α)
    [IsFiniteMeasure μ] (a : ℝ) (ha : 0 < a)
    (X : α → β) (Y : α → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hlaw : μ.map Y = ProbabilityTheory.gaussianReal 0 1)
    (hindep : ProbabilityTheory.IndepFun X Y μ)
    (Nf : β → E → ℕ) (Sf : β → E → ℝ) (qf : β → E)
    (hint : Integrable (Mstep a Nf Sf qf) (μ.map (fun ω => (X ω, Y ω)))) :
    μ[fun ω => Mstep a Nf Sf qf (X ω, Y ω) | MeasurableSpace.comap X inferInstance]
      =ᵐ[μ] fun ω => Mval a Nf Sf (X ω) := by
  have : IsFiniteMeasure (μ.map Y) := by rw [hlaw]; infer_instance
  refine condExp_freeze_apply X Y hX hY hindep (Mstep a Nf Sf qf) hint (Mval a Nf Sf)
    (fun b => ?_)
  rw [hlaw]
  exact step_inner_integral_law a ha Nf Sf qf b

/-- **The mean is preserved.**  The conditional statement integrated. -/
theorem mean_step {α : Type*} {mα : MeasurableSpace α} (μ : Measure α)
    [IsFiniteMeasure μ] (a : ℝ) (ha : 0 < a)
    (X : α → β) (Y : α → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hlaw : μ.map Y = ProbabilityTheory.gaussianReal 0 1)
    (hindep : ProbabilityTheory.IndepFun X Y μ)
    (Nf : β → E → ℕ) (Sf : β → E → ℝ) (qf : β → E)
    (hint : Integrable (Mstep a Nf Sf qf) (μ.map (fun ω => (X ω, Y ω)))) :
    ∫ ω, Mstep a Nf Sf qf (X ω, Y ω) ∂μ = ∫ ω, Mval a Nf Sf (X ω) ∂μ := by
  have hcond := martingale_step μ a ha X Y hX hY hlaw hindep Nf Sf qf hint
  have hle : MeasurableSpace.comap X (inferInstance : MeasurableSpace β) ≤ mα :=
    hX.comap_le
  calc ∫ ω, Mstep a Nf Sf qf (X ω, Y ω) ∂μ
      = ∫ ω, (μ[fun ω => Mstep a Nf Sf qf (X ω, Y ω)
          | MeasurableSpace.comap X inferInstance]) ω ∂μ :=
        (integral_condExp hle).symm
    _ = ∫ ω, Mval a Nf Sf (X ω) ∂μ := integral_congr_ae hcond

/-- **The process starts at one.** -/
theorem Mval_init (a : ℝ) (ha : 0 < a) (x : β) :
    Mval (E := E) a (fun _ _ => (0 : ℕ)) (fun _ _ => (0 : ℝ)) x = 1 := by
  unfold Mval mgfFactor
  refine Finset.prod_eq_one (fun e _ => ?_)
  have h1 : a + (((0 : ℕ) : ℝ)) = a := by norm_num
  rw [h1, div_self (ne_of_gt ha), Real.sqrt_one, one_mul]
  norm_num

/-! ## Integrability, derived rather than assumed -/

theorem Mstep_nonneg (a : ℝ) (ha : 0 < a) (Nf : β → E → ℕ) (Sf : β → E → ℝ) (qf : β → E)
    (p : β × ℝ) : 0 ≤ Mstep a Nf Sf qf p := by
  classical
  refine Finset.prod_nonneg (fun e _ => ?_)
  refine le_of_lt (mgfFactor_pos a _ _ ha ?_)
  by_cases h : qf p.1 = e
  · rw [if_pos h]; positivity
  · rw [if_neg h]; positivity

theorem Mstep_measurable (a : ℝ) (Nf : β → E → ℕ) (Sf : β → E → ℝ) (qf : β → E)
    (hN : ∀ e, Measurable fun x => Nf x e) (hS : ∀ e, Measurable fun x => Sf x e)
    (hq : Measurable qf) : Measurable (Mstep a Nf Sf qf) := by
  classical
  unfold Mstep mgfFactor
  refine Finset.measurable_prod _ (fun e _ => ?_)
  have hset : MeasurableSet {p : β × ℝ | qf p.1 = e} :=
    (hq.comp measurable_fst) (measurableSet_singleton e)
  have hind : Measurable (fun p : β × ℝ => if qf p.1 = e then (1 : ℝ) else 0) :=
    Measurable.ite hset measurable_const measurable_const
  have hindz : Measurable (fun p : β × ℝ => if qf p.1 = e then p.2 else 0) :=
    Measurable.ite hset measurable_snd measurable_const
  have hn : Measurable (fun p : β × ℝ =>
      a + ((Nf p.1 e : ℝ) + if qf p.1 = e then (1 : ℝ) else 0)) :=
    measurable_const.add ((((measurable_from_top : Measurable (fun n : ℕ => (n : ℝ))).comp
      ((hN e).comp measurable_fst))).add hind)
  have hs : Measurable (fun p : β × ℝ =>
      Sf p.1 e + if qf p.1 = e then p.2 else 0) :=
    (((hS e).comp measurable_fst)).add hindz
  exact (Real.continuous_sqrt.measurable.comp (measurable_const.div hn)).mul
    (Real.continuous_exp.measurable.comp ((hs.pow_const 2).div (measurable_const.mul hn)))

/-- **The inner integrand is integrable against the law**, not merely against the density. -/
theorem inner_integrable_law (a : ℝ) (ha : 0 < a)
    (Nf : β → E → ℕ) (Sf : β → E → ℝ) (qf : β → E) (x : β) :
    Integrable (fun z => Mstep a Nf Sf qf (x, z)) (ProbabilityTheory.gaussianReal 0 1) := by
  rw [ProbabilityTheory.gaussianReal_of_var_ne_zero 0 (by norm_num),
    integrable_withDensity_iff (ProbabilityTheory.measurable_gaussianPDF 0 1)
      (Filter.Eventually.of_forall (fun z => ENNReal.ofReal_lt_top))]
  have hrw : ∀ z : ℝ,
      Mstep a Nf Sf qf (x, z) * (ProbabilityTheory.gaussianPDF 0 1 z).toReal
        = Mstep a Nf Sf qf (x, z) * gaussianPDF 0 1 z := by
    intro z
    rw [ProbabilityTheory.gaussianPDF, ENNReal.toReal_ofReal
      (ProbabilityTheory.gaussianPDFReal_nonneg 0 1 z), gaussianPDF_eq]
  rw [show (fun z => Mstep a Nf Sf qf (x, z) * (ProbabilityTheory.gaussianPDF 0 1 z).toReal)
      = (fun z => Mstep a Nf Sf qf (x, z) * gaussianPDF 0 1 z) from funext hrw]
  exact step_inner_integrable a ha Nf Sf qf x

/-- **The induction step for integrability.**  Tonelli's criterion on the product: the
inner integrals are finite by `inner_integrable_law`, and their values are the process at
the previous step, so the joint is integrable exactly when the previous step is. -/
theorem joint_integrable {α : Type*} {mα : MeasurableSpace α} (μ : Measure α)
    [IsFiniteMeasure μ] (a : ℝ) (ha : 0 < a)
    (X : α → β) (Y : α → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hlaw : μ.map Y = ProbabilityTheory.gaussianReal 0 1)
    (hindep : ProbabilityTheory.IndepFun X Y μ)
    (Nf : β → E → ℕ) (Sf : β → E → ℝ) (qf : β → E)
    (hN : ∀ e, Measurable fun x => Nf x e) (hS : ∀ e, Measurable fun x => Sf x e)
    (hq : Measurable qf)
    (hMval : Integrable (fun ω => Mval a Nf Sf (X ω)) μ) :
    Integrable (Mstep a Nf Sf qf) (μ.map (fun ω => (X ω, Y ω))) := by
  classical
  have hmeas := Mstep_measurable a Nf Sf qf hN hS hq
  have hprod : μ.map (fun ω => (X ω, Y ω)) = (μ.map X).prod (μ.map Y) :=
    (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      hX.aemeasurable hY.aemeasurable).mp hindep
  rw [hprod]
  have : IsFiniteMeasure (μ.map Y) := by rw [hlaw]; infer_instance
  refine (integrable_prod_iff hmeas.aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · refine Filter.Eventually.of_forall (fun x => ?_)
    rw [hlaw]
    exact inner_integrable_law a ha Nf Sf qf x
  · have hval : ∀ x : β, ∫ z, ‖Mstep a Nf Sf qf (x, z)‖ ∂(μ.map Y) = Mval a Nf Sf x := by
      intro x
      have hnorm : ∀ z : ℝ, ‖Mstep a Nf Sf qf (x, z)‖ = Mstep a Nf Sf qf (x, z) :=
        fun z => Real.norm_of_nonneg (Mstep_nonneg a ha Nf Sf qf (x, z))
      rw [show (fun z => ‖Mstep a Nf Sf qf (x, z)‖)
          = (fun z => Mstep a Nf Sf qf (x, z)) from funext hnorm, hlaw]
      exact step_inner_integral_law a ha Nf Sf qf x
    rw [show (fun x => ∫ z, ‖Mstep a Nf Sf qf (x, z)‖ ∂(μ.map Y))
        = Mval a Nf Sf from funext hval]
    refine (integrable_map_measure ?_ hX.aemeasurable).mpr hMval
    have hMvalmeas : Measurable (Mval (E := E) a Nf Sf) := by
      unfold Mval mgfFactor
      refine Finset.measurable_prod _ (fun e _ => ?_)
      have hn : Measurable (fun x : β => a + (Nf x e : ℝ)) :=
        measurable_const.add ((measurable_from_top : Measurable (fun n : ℕ => (n : ℝ))).comp
          (hN e))
      exact (Real.continuous_sqrt.measurable.comp (measurable_const.div hn)).mul
        (Real.continuous_exp.measurable.comp (((hS e).pow_const 2).div
          (measurable_const.mul hn)))
    exact hMvalmeas.aestronglyMeasurable

/-! ## Audit -/

#print axioms Mval_pos
#print axioms Mstep_eq
#print axioms head_pointwise
#print axioms step_inner_integrable
#print axioms step_inner_integral
#print axioms integral_gaussian_bridge
#print axioms step_inner_integral_law
#print axioms martingale_step
#print axioms mean_step
#print axioms Mval_init
#print axioms Mstep_nonneg
#print axioms Mstep_measurable
#print axioms inner_integrable_law
#print axioms joint_integrable

end CIGAMF.P13.PaperAAdaptMart
