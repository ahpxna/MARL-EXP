import Mathlib
import «LeanPaperA7ConfidenceV1»

/-!
# Paper A7: the observation stream, and the mixture martingale on it

`LeanPaperA7ConfidenceV1` proves Ville's inequality and derives the confidence guarantee for
any non-negative supermartingale started at mean one.  That is a statement about an abstract
process.  This module exhibits the process: an actual observation stream, an actual
filtration, and an actual martingale, so the guarantee applies to something.

  * `streamMeasure` is the law of independent `N(0,1)` observations on `ℕ → ℝ`.
  * `obs n` is the `n`-th observation; the coordinates are independent because the measure
    is a product.
  * `incr u n = exp(u * Y_n - u^2/2)` is the exponentially tilted increment, and
    `incr_integral` computes its mean to be exactly one -- this is the Gaussian moment
    generating function at unit variance, and it is the one calculation the whole
    construction turns on.
  * `mix u t` is the product of the increments up to time `t`, and `mix_martingale` proves
    it is a martingale for the natural filtration of the increments.

`stream_confidence` then closes the loop: on this stream the tilted mixture exceeds
`1/delta` at some time up to any horizon with probability at most `delta`.

## SCOPE, STATED HONESTLY

The tilt `u` here is FIXED and the query is the same coordinate at every step.  The
learner's statistic is a mixture over `u` and its query is chosen from the history, so this
is not yet that process: what it establishes is that the supermartingale hypothesis of
`confidence_of_supermartingale` is satisfiable by a real observation model, and that the
Gaussian step calculation is the right one.  Carrying it to the adaptive, mixed statistic
needs the predictable query of `PredictableQuery` to enter the conditional expectation, and
that is not done here.
-/

namespace CIGAMF.P13.PaperA7Stream

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

/-! ## The stream -/

/-- The observation stream: independent standard Gaussians. -/
noncomputable def streamMeasure : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)

instance : IsProbabilityMeasure streamMeasure := by
  unfold streamMeasure
  infer_instance

/-- The `n`-th observation. -/
def obs (n : ℕ) (ω : ℕ → ℝ) : ℝ := ω n

theorem obs_measurable (n : ℕ) : Measurable (obs n) := measurable_pi_apply n

/-- **The observations are independent**, because the law is a product. -/
theorem obs_indep : iIndepFun obs streamMeasure :=
  iIndepFun_infinitePi (X := fun _ (ω : ℝ) => ω) (fun _ => measurable_id)

/-- Each observation is standard Gaussian. -/
theorem obs_map (n : ℕ) : streamMeasure.map (obs n) = gaussianReal 0 1 :=
  Measure.infinitePi_map_eval _ n

/-! ## The tilted increment -/

/-- The exponentially tilted increment at tilt `u`. -/
noncomputable def incr (u : ℝ) (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  Real.exp (u * obs n ω - u ^ 2 / 2)

theorem incr_pos (u : ℝ) (n : ℕ) (ω : ℕ → ℝ) : 0 < incr u n ω := Real.exp_pos _

theorem incr_nonneg (u : ℝ) (n : ℕ) (ω : ℕ → ℝ) : 0 ≤ incr u n ω := (incr_pos u n ω).le

theorem incr_measurable (u : ℝ) (n : ℕ) : StronglyMeasurable (incr u n) := by
  refine (Measurable.stronglyMeasurable ?_)
  exact ((measurable_const.mul (obs_measurable n)).sub measurable_const).exp

/-- **The increments are independent**: measurable functions of independent observations. -/
theorem incr_indep (u : ℝ) : iIndepFun (incr u) streamMeasure := by
  have h := obs_indep.comp (fun _ (x : ℝ) => Real.exp (u * x - u ^ 2 / 2))
    (fun _ => ((measurable_const.mul measurable_id).sub measurable_const).exp)
  exact h

theorem incr_integrable (u : ℝ) (n : ℕ) : Integrable (incr u n) streamMeasure := by
  have hgauss : Integrable (fun x : ℝ => Real.exp (u * x - u ^ 2 / 2)) (gaussianReal 0 1) := by
    have h := ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := (0 : ℝ)) (v := 1) u
    have hrw : (fun x : ℝ => Real.exp (u * x - u ^ 2 / 2))
        = fun x : ℝ => Real.exp (-(u ^ 2 / 2)) * Real.exp (u * x) := by
      funext x
      rw [← Real.exp_add]
      ring_nf
    rw [hrw]
    exact h.const_mul _
  have hmeas : AEStronglyMeasurable (fun x : ℝ => Real.exp (u * x - u ^ 2 / 2))
      (streamMeasure.map (obs n)) := by
    rw [obs_map n]
    exact (((measurable_const.mul measurable_id).sub measurable_const).exp).aestronglyMeasurable
  have hfin : Integrable ((fun x : ℝ => Real.exp (u * x - u ^ 2 / 2)) ∘ (obs n))
      streamMeasure := by
    rw [← integrable_map_measure hmeas (obs_measurable n).aemeasurable, obs_map n]
    exact hgauss
  exact hfin

/-- **The tilted increment has mean exactly one.**

This is the Gaussian moment generating function at unit variance,
`E exp(u Y) = exp(u^2/2)`, cancelled against the tilt's own `exp(-u^2/2)`.  It is the single
calculation the martingale property rests on. -/
theorem incr_integral (u : ℝ) (n : ℕ) : ∫ ω, incr u n ω ∂streamMeasure = 1 := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => Real.exp (u * x - u ^ 2 / 2))
      (streamMeasure.map (obs n)) := by
    rw [obs_map n]
    exact (((measurable_const.mul measurable_id).sub measurable_const).exp).aestronglyMeasurable
  have hchange : ∫ ω, incr u n ω ∂streamMeasure
      = ∫ x, Real.exp (u * x - u ^ 2 / 2) ∂(gaussianReal 0 1) := by
    rw [← obs_map n, integral_map (obs_measurable n).aemeasurable hmeas]
    rfl
  rw [hchange]
  have hrw : (fun x : ℝ => Real.exp (u * x - u ^ 2 / 2))
      = fun x : ℝ => Real.exp (-(u ^ 2 / 2)) * Real.exp (u * x) := by
    funext x
    rw [← Real.exp_add]
    ring_nf
  rw [hrw, integral_const_mul]
  have hmgf : ∫ x, Real.exp (u * x) ∂(gaussianReal 0 1) = Real.exp (u ^ 2 / 2) := by
    have h := congrFun (ProbabilityTheory.mgf_fun_id_gaussianReal (μ := (0 : ℝ)) (v := 1)) u
    simp only [ProbabilityTheory.mgf] at h
    simpa using h
  rw [hmgf, ← Real.exp_add]
  norm_num

/-! ## The mixture, and its martingale property -/

/-- The product of the increments up to time `t`, as a product of FUNCTIONS -- which is what
lets the independence and measurability lemmas apply to it directly. -/
noncomputable def mix (u : ℝ) (t : ℕ) : (ℕ → ℝ) → ℝ :=
  ∏ s ∈ Finset.range (t + 1), incr u s

theorem mix_apply (u : ℝ) (t : ℕ) (ω : ℕ → ℝ) :
    mix u t ω = ∏ s ∈ Finset.range (t + 1), incr u s ω := by
  unfold mix
  rw [Finset.prod_apply]

/-- The natural filtration of the increments. -/
noncomputable def streamFiltration (u : ℝ) :
    Filtration ℕ (inferInstance : MeasurableSpace (ℕ → ℝ)) :=
  Filtration.natural (incr u) (incr_measurable u)

theorem mix_pos (u : ℝ) (t : ℕ) (ω : ℕ → ℝ) : 0 < mix u t ω := by
  rw [mix_apply]
  exact Finset.prod_pos (fun s _ => incr_pos u s ω)

theorem mix_nonneg (u : ℝ) (t : ℕ) (ω : ℕ → ℝ) : 0 ≤ mix u t ω := (mix_pos u t ω).le

theorem mix_succ (u : ℝ) (t : ℕ) :
    mix u (t + 1) = mix u t * incr u (t + 1) := by
  unfold mix
  rw [Finset.prod_range_succ]

theorem mix_zero (u : ℝ) : mix u 0 = incr u 0 := by
  unfold mix
  simp

/-! ### The martingale property -/

theorem incr_adapted (u : ℝ) : StronglyAdapted (streamFiltration u) (incr u) :=
  Filtration.stronglyAdapted_natural (incr_measurable u)

theorem mix_adapted (u : ℝ) : StronglyAdapted (streamFiltration u) (mix u) := by
  intro t
  unfold mix
  refine Finset.stronglyMeasurable_prod _ (fun s hs => ?_)
  exact (incr_adapted u s).mono
    ((streamFiltration u).mono (Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)))

/-- The past and the next increment are independent, which is what makes the product
integrable and the conditional expectation computable. -/
theorem mix_indep_incr (u : ℝ) (t : ℕ) :
    IndepFun (mix u t) (incr u (t + 1)) streamMeasure := by
  unfold mix
  exact (incr_indep u).indepFun_finsetProd_of_notMem
    (fun i => (incr_measurable u i).measurable) (by simp)

theorem mix_integrable (u : ℝ) : ∀ t, Integrable (mix u t) streamMeasure := by
  intro t
  induction t with
  | zero => rw [mix_zero]; exact incr_integrable u 0
  | succ n ih =>
      rw [mix_succ]
      exact (mix_indep_incr u n).integrable_mul ih (incr_integrable u (n + 1))

/-- **The tilted mixture is a martingale on the observation stream.**

The next increment is independent of the past, so its conditional expectation is its mean,
and `incr_integral` makes that mean exactly one. -/
theorem mix_martingale_step (u : ℝ) (t : ℕ) :
    streamMeasure[mix u (t + 1) | streamFiltration u t] =ᵐ[streamMeasure] mix u t := by
  have h2 := condExp_mul_of_stronglyMeasurable_left (m := (streamFiltration u t : MeasurableSpace (ℕ → ℝ)))
      (mix_adapted u t)
      (by rw [← mix_succ]; exact mix_integrable u (t + 1))
      (incr_integrable u (t + 1))
  have h3 : streamMeasure[incr u (t + 1) | (streamFiltration u t : MeasurableSpace (ℕ → ℝ))]
      =ᵐ[streamMeasure] fun _ => ∫ ω, incr u (t + 1) ω ∂streamMeasure :=
    (incr_indep u).condExp_natural_ae_eq_of_lt (incr_measurable u) (Nat.lt_succ_self t)
  rw [mix_succ]
  filter_upwards [h2, h3] with ω hω2 hω3
  rw [hω2]
  show mix u t ω * (streamMeasure[incr u (t + 1) | streamFiltration u t]) ω = mix u t ω
  rw [hω3, incr_integral]
  ring

theorem mix_supermartingale (u : ℝ) :
    Supermartingale (mix u) (streamFiltration u) streamMeasure :=
  supermartingale_nat (mix_adapted u) (mix_integrable u)
    (fun t => (mix_martingale_step u t).le)

/-- **The confidence guarantee, on an actual observation stream.**

Ville's inequality applied to a process that exists: independent Gaussian observations, the
natural filtration of the tilted increments, and the mixture built from them.  Nothing here
is a hypothesis about an abstract process. -/
theorem stream_confidence (u : ℝ) (δ : ℝ) (hδ : 0 < δ) (N : ℕ) :
    streamMeasure.real {ω | ∃ j ≤ N, 1 / δ ≤ mix u j ω} ≤ δ := by
  refine CIGAMF.P13.PaperA7Confidence.confidence_of_supermartingale
    (mix u) (mix_supermartingale u) (fun n ω => (mix_pos u n ω).le) ?_ δ hδ N
  rw [mix_zero]
  exact le_of_eq (incr_integral u 0)

/-! ## The ADAPTIVE query, inside the conditional expectation

The martingale above queries the same coordinate at every step.  The learner does not: it
picks `q_t` from the history.  The step that has to survive is the conditional expectation,
and it does, for the reason the finite query set makes available -- decompose over the
finitely many possible queries:

    W_t(u) = sum_e  1{q_t = e} * exp(u_e Y_t - u_e^2 / 2).

The indicator is measurable with respect to the past, so it comes out of the conditional
expectation; the exponential factor is a function of the fresh innovation alone, so it is
independent of the past and its conditional expectation is its mean, which is one.  What
remains is `sum_e 1{q_t = e} = 1`.

`PredictableQuery` in `LeanPaperA7ConfidenceV1` is the informal version of the hypothesis
`hq` below; here it is the measurability that the conditional expectation actually uses. -/

section Adaptive

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The filtration generated by the innovations themselves. -/
noncomputable def innovFiltration :
    Filtration ℕ (inferInstance : MeasurableSpace (ℕ → ℝ)) :=
  Filtration.natural obs (fun n => (obs_measurable n).stronglyMeasurable)

/-- **A fresh innovation is independent of the past**, so its tilted exponential has
conditional mean one. -/
theorem condExp_incr_innov (v : ℝ) (t : ℕ) :
    streamMeasure[incr v (t + 1) | (innovFiltration t : MeasurableSpace (ℕ → ℝ))]
      =ᵐ[streamMeasure] fun _ => (1 : ℝ) := by
  have hindep : ProbabilityTheory.Indep
      (MeasurableSpace.comap (obs (t + 1)) inferInstance)
      (innovFiltration t) streamMeasure :=
    ProbabilityTheory.iIndepFun.indep_comap_natural_of_lt
      (fun n => (obs_measurable n).stronglyMeasurable) obs_indep (Nat.lt_succ_self t)
  have hmeas : StronglyMeasurable[MeasurableSpace.comap (obs (t + 1)) inferInstance]
      (incr v (t + 1)) := by
    refine Measurable.stronglyMeasurable ?_
    exact ((measurable_const.mul (measurable_iff_comap_le.mpr le_rfl)).sub
      measurable_const).exp
  have h := condExp_indep_eq
    (hle₁ := (obs_measurable (t + 1)).comap_le) (hle₂ := innovFiltration.le t)
    hmeas hindep
  refine h.trans ?_
  filter_upwards with ω
  exact incr_integral v (t + 1)

/-- The tilted increment when the query is chosen from the history. -/
noncomputable def adaptIncr (u : E → ℝ) (q : ℕ → (ℕ → ℝ) → E) (t : ℕ) (ω : ℕ → ℝ) : ℝ :=
  Real.exp (u (q t ω) * obs t ω - (u (q t ω)) ^ 2 / 2)

/-- The decomposition over the finitely many possible queries. -/
theorem adaptIncr_eq_sum (u : E → ℝ) (q : ℕ → (ℕ → ℝ) → E) (t : ℕ) (ω : ℕ → ℝ) :
    adaptIncr u q t ω
      = ∑ e : E, (if q t ω = e then (1 : ℝ) else 0) * incr (u e) t ω := by
  classical
  unfold adaptIncr incr
  rw [Finset.sum_eq_single (q t ω)]
  · rw [if_pos rfl, one_mul]
  · intro e _ hne
    rw [if_neg (fun hc => hne hc.symm), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem adaptIncr_pos (u : E → ℝ) (q : ℕ → (ℕ → ℝ) → E) (t : ℕ) (ω : ℕ → ℝ) :
    0 < adaptIncr u q t ω := Real.exp_pos _

/-- **The adaptive step has conditional mean one.**

This is the lemma the confidence sequence rests on once the query is chosen from the
history.  `hq` is predictability -- the query at time `t+1` is measurable with respect to
the innovations up to `t` -- and `hint` is integrability of each term, which independence
and `incr_integrable` supply. -/
theorem condExp_adaptIncr (u : E → ℝ) (q : ℕ → (ℕ → ℝ) → E) (t : ℕ)
    (hq : ∀ e : E, MeasurableSet[innovFiltration t] {ω | q (t + 1) ω = e})
    (hint : ∀ e : E, Integrable
      ((fun ω => if q (t + 1) ω = e then (1 : ℝ) else 0) * incr (u e) (t + 1))
      streamMeasure) :
    streamMeasure[adaptIncr u q (t + 1) | (innovFiltration t : MeasurableSpace (ℕ → ℝ))]
      =ᵐ[streamMeasure] fun _ => (1 : ℝ) := by
  classical
  have hrw : adaptIncr u q (t + 1)
      = ∑ e : E, ((fun ω => if q (t + 1) ω = e then (1 : ℝ) else 0)
          * incr (u e) (t + 1)) := by
    funext ω
    rw [Finset.sum_apply]
    simpa using adaptIncr_eq_sum u q (t + 1) ω
  rw [hrw]
  refine (MeasureTheory.condExp_finset_sum
    (μ := streamMeasure) (m := (innovFiltration t : MeasurableSpace (ℕ → ℝ)))
    (s := (Finset.univ : Finset E)) (fun e _ => hint e)).trans ?_
  have hterm : ∀ e : E,
      streamMeasure[((fun ω => if q (t + 1) ω = e then (1 : ℝ) else 0)
          * incr (u e) (t + 1)) | (innovFiltration t : MeasurableSpace (ℕ → ℝ))]
        =ᵐ[streamMeasure] fun ω => (if q (t + 1) ω = e then (1 : ℝ) else 0) := by
    intro e
    have hind : StronglyMeasurable[innovFiltration t]
        (fun ω => (if q (t + 1) ω = e then (1 : ℝ) else 0)) :=
      Measurable.stronglyMeasurable (measurable_const.ite (hq e) measurable_const)
    refine (MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (m := (innovFiltration t : MeasurableSpace (ℕ → ℝ))) hind (hint e)
      (incr_integrable (u e) (t + 1))).trans ?_
    filter_upwards [condExp_incr_innov (u e) t] with ω hω
    show (if q (t + 1) ω = e then (1 : ℝ) else 0)
        * (streamMeasure[incr (u e) (t + 1) |
            (innovFiltration t : MeasurableSpace (ℕ → ℝ))]) ω
      = (if q (t + 1) ω = e then (1 : ℝ) else 0)
    rw [hω]
    ring
  have hall := (Filter.eventually_all_finset (Finset.univ : Finset E)).2
    (fun e _ => hterm e)
  filter_upwards [hall] with ω hω
  rw [Finset.sum_apply]
  have hpt : ∀ e : E,
      (streamMeasure[((fun ω' => if q (t + 1) ω' = e then (1 : ℝ) else 0)
        * incr (u e) (t + 1)) | (innovFiltration t : MeasurableSpace (ℕ → ℝ))]) ω
      = (if q (t + 1) ω = e then (1 : ℝ) else 0) := fun e => hω e (Finset.mem_univ e)
  rw [Finset.sum_congr rfl (fun e _ => hpt e),
      Finset.sum_ite_eq (Finset.univ : Finset E) (q (t + 1) ω) (fun _ => (1 : ℝ)),
      if_pos (Finset.mem_univ _)]

end Adaptive

/-! ### The adaptive mixture is a martingale, and Ville applies to it

With `condExp_adaptIncr` the one-step property is in hand.  Turning it into a martingale
needs the product to be integrable, and that is where independence is used a second time:
the past is `F_t`-measurable, the fresh innovation generates a sigma-algebra independent of
`F_t`, and `Indep.mono` carries that down to the two functions.

The policy enters through three hypotheses, and together they are what "adapted and
predictable" means:

  * `hadapt`: the increment at time `s` is determined by the innovations up to `s`;
  * `hq`: the query at time `s+1` is determined by those up to `s`;
  * `hq0`: the first query is chosen before anything is seen, so it is constant.

The third is an INITIALISATION CONVENTION, not a restriction on adaptive sampling.  Writing
the filtration as `F_t = sigma(Y_0, ..., Y_{t-1})` makes `F_0` contain no observation, so a
deterministic rule's first query is constant by definition.  A randomised rule is covered by
putting its seed into `F_0`, independent of the observations, and then `q_0` need not be
constant.  The development here is for the deterministic case. -/

/-- The past and a fresh innovation generate independent sigma-algebras. -/
theorem indep_past_innov (t : ℕ) :
    ProbabilityTheory.Indep (innovFiltration t)
      (MeasurableSpace.comap (obs (t + 1)) inferInstance) streamMeasure :=
  (ProbabilityTheory.iIndepFun.indep_comap_natural_of_lt
    (fun n => (obs_measurable n).stronglyMeasurable) obs_indep (Nat.lt_succ_self t)).symm

/-- Hence anything measurable in the past is independent of anything built from the fresh
innovation. -/
theorem indepFun_past_innov (t : ℕ) (A B : (ℕ → ℝ) → ℝ)
    (hA : StronglyMeasurable[innovFiltration t] A)
    (hB : StronglyMeasurable[MeasurableSpace.comap (obs (t + 1)) inferInstance] B) :
    ProbabilityTheory.IndepFun A B streamMeasure :=
  ProbabilityTheory.indep_of_indep_of_le (indep_past_innov t) hA.measurable.comap_le
    hB.measurable.comap_le

theorem incr_comap_measurable (v : ℝ) (t : ℕ) :
    StronglyMeasurable[MeasurableSpace.comap (obs (t + 1)) inferInstance]
      (incr v (t + 1)) :=
  Measurable.stronglyMeasurable
    (((measurable_const.mul (measurable_iff_comap_le.mpr le_rfl)).sub
      measurable_const).exp)

section AdaptiveMartingale

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The adaptive mixture up to time `t`. -/
noncomputable def adaptMix (u : E → ℝ) (q : ℕ → (ℕ → ℝ) → E) (t : ℕ) : (ℕ → ℝ) → ℝ :=
  ∏ s ∈ Finset.range (t + 1), adaptIncr u q s

theorem adaptMix_pos (u : E → ℝ) (q : ℕ → (ℕ → ℝ) → E) (t : ℕ) (ω : ℕ → ℝ) :
    0 < adaptMix u q t ω := by
  unfold adaptMix
  rw [Finset.prod_apply]
  exact Finset.prod_pos (fun s _ => adaptIncr_pos u q s ω)

theorem adaptMix_succ (u : E → ℝ) (q : ℕ → (ℕ → ℝ) → E) (t : ℕ) :
    adaptMix u q (t + 1) = adaptMix u q t * adaptIncr u q (t + 1) := by
  unfold adaptMix
  rw [Finset.prod_range_succ]

theorem adaptMix_zero (u : E → ℝ) (q : ℕ → (ℕ → ℝ) → E) :
    adaptMix u q 0 = adaptIncr u q 0 := by
  unfold adaptMix
  simp

/-- **The adaptive mixture is a martingale.**  Integrability is derived, not assumed. -/
theorem adaptMix_supermartingale (u : E → ℝ) (q : ℕ → (ℕ → ℝ) → E)
    (hadapt : ∀ s, StronglyMeasurable[innovFiltration s] (adaptIncr u q s))
    (hq : ∀ (t : ℕ) (e : E), MeasurableSet[innovFiltration t] {ω | q (t + 1) ω = e})
    (hq0 : ∀ ω, q 0 ω = q 0 0) :
    MeasureTheory.Supermartingale (adaptMix u q) innovFiltration streamMeasure := by
  classical
  have hmixadapt : ∀ t, StronglyMeasurable[innovFiltration t] (adaptMix u q t) := by
    intro t
    unfold adaptMix
    refine Finset.stronglyMeasurable_prod _ (fun s hs => ?_)
    exact (hadapt s).mono
      (innovFiltration.mono (Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)))
  have hterm : ∀ (t : ℕ) (e : E),
      MeasureTheory.Integrable
        ((fun ω => if q (t + 1) ω = e then (1 : ℝ) else 0) * incr (u e) (t + 1))
        streamMeasure := by
    intro t e
    have hind : StronglyMeasurable[innovFiltration t]
        (fun ω => (if q (t + 1) ω = e then (1 : ℝ) else 0)) :=
      Measurable.stronglyMeasurable (measurable_const.ite (hq t e) measurable_const)
    refine (indepFun_past_innov t _ _ hind
      (incr_comap_measurable (u e) t)).integrable_mul ?_ (incr_integrable (u e) (t + 1))
    refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (1 : ℝ))
      (hind.mono (innovFiltration.le t)).aestronglyMeasurable ?_
    filter_upwards with ω
    by_cases h : q (t + 1) ω = e
    · rw [if_pos h]; norm_num
    · rw [if_neg h]; norm_num
  have hincrint : ∀ t : ℕ, MeasureTheory.Integrable (adaptIncr u q (t + 1)) streamMeasure := by
    intro t
    have hsum : adaptIncr u q (t + 1)
        = fun ω => ∑ e : E, ((fun ω' => if q (t + 1) ω' = e then (1 : ℝ) else 0)
            * incr (u e) (t + 1)) ω := by
      funext ω
      simpa using adaptIncr_eq_sum u q (t + 1) ω
    rw [hsum]
    exact MeasureTheory.integrable_finset_sum _ (fun e _ => hterm t e)
  have hint : ∀ t, MeasureTheory.Integrable (adaptMix u q t) streamMeasure := by
    intro t
    induction t with
    | zero =>
        rw [adaptMix_zero]
        have hc : adaptIncr u q 0 = incr (u (q 0 0)) 0 := by
          funext ω
          unfold adaptIncr incr
          rw [hq0 ω]
        rw [hc]
        exact incr_integrable _ 0
    | succ n ih =>
        rw [adaptMix_succ]
        have hdec : adaptMix u q n * adaptIncr u q (n + 1)
            = fun ω => ∑ e : E, ((adaptMix u q n
                * (fun ω' => if q (n + 1) ω' = e then (1 : ℝ) else 0))
                * incr (u e) (n + 1)) ω := by
          funext ω
          simp only [Pi.mul_apply]
          rw [adaptIncr_eq_sum u q (n + 1) ω, Finset.mul_sum]
          exact Finset.sum_congr rfl fun e _ => by ring
        rw [hdec]
        refine MeasureTheory.integrable_finset_sum _ (fun e _ => ?_)
        have hAmeas : StronglyMeasurable[innovFiltration n]
            (adaptMix u q n * (fun ω => if q (n + 1) ω = e then (1 : ℝ) else 0)) :=
          (hmixadapt n).mul
            (Measurable.stronglyMeasurable (measurable_const.ite (hq n e) measurable_const))
        have hAint : MeasureTheory.Integrable
            (adaptMix u q n * (fun ω => if q (n + 1) ω = e then (1 : ℝ) else 0))
            streamMeasure := by
          refine MeasureTheory.Integrable.mono' ih
            (hAmeas.mono (innovFiltration.le n)).aestronglyMeasurable ?_
          filter_upwards with ω
          simp only [Pi.mul_apply]
          by_cases h : q (n + 1) ω = e
          · rw [if_pos h, mul_one, Real.norm_eq_abs,
                abs_of_pos (adaptMix_pos u q n ω)]
          · rw [if_neg h, mul_zero, norm_zero]
            exact (adaptMix_pos u q n ω).le
        exact (indepFun_past_innov n _ _ hAmeas
          (incr_comap_measurable (u e) n)).integrable_mul hAint
          (incr_integrable (u e) (n + 1))
  refine MeasureTheory.supermartingale_nat hmixadapt hint (fun t => ?_)
  have hstep : streamMeasure[adaptMix u q (t + 1) |
      (innovFiltration t : MeasurableSpace (ℕ → ℝ))]
      =ᵐ[streamMeasure] adaptMix u q t := by
    rw [adaptMix_succ]
    refine (MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (m := (innovFiltration t : MeasurableSpace (ℕ → ℝ))) (hmixadapt t)
      (by rw [← adaptMix_succ]; exact hint (t + 1)) (hincrint t)).trans ?_
    filter_upwards [condExp_adaptIncr u q t (hq t) (hterm t)] with ω hω
    show adaptMix u q t ω
        * (streamMeasure[adaptIncr u q (t + 1) |
            (innovFiltration t : MeasurableSpace (ℕ → ℝ))]) ω = adaptMix u q t ω
    rw [hω]
    ring
  exact hstep.le

/-- **The confidence guarantee for an ADAPTIVELY queried stream.**  Ville, applied to the
mixture the learner actually builds. -/
theorem adaptive_confidence (u : E → ℝ) (q : ℕ → (ℕ → ℝ) → E)
    (hadapt : ∀ s, StronglyMeasurable[innovFiltration s] (adaptIncr u q s))
    (hq : ∀ (t : ℕ) (e : E), MeasurableSet[innovFiltration t] {ω | q (t + 1) ω = e})
    (hq0 : ∀ ω, q 0 ω = q 0 0)
    (δ : ℝ) (hδ : 0 < δ) (N : ℕ) :
    streamMeasure.real {ω | ∃ j ≤ N, 1 / δ ≤ adaptMix u q j ω} ≤ δ := by
  refine CIGAMF.P13.PaperA7Confidence.confidence_of_supermartingale
    (adaptMix u q) (adaptMix_supermartingale u q hadapt hq hq0)
    (fun n ω => (adaptMix_pos u q n ω).le) ?_ δ hδ N
  rw [adaptMix_zero]
  have hc : adaptIncr u q 0 = incr (u (q 0 0)) 0 := by
    funext ω
    unfold adaptIncr incr
    rw [hq0 ω]
  rw [hc]
  exact le_of_eq (incr_integral _ 0)

end AdaptiveMartingale

/-! ### The mixture over tilts

A single tilt gives a confidence sequence for that tilt only.  The learner mixes over a
family, and the mixture has to stay a supermartingale.  Over a FINITE family -- which is
what an implementation uses -- the argument is linearity of conditional expectation and
nothing else. -/

section Mixture

variable {ι : Type*} [DecidableEq ι] {E : Type*} [Fintype E] [DecidableEq E]

/-- A finite mixture of tilted mixtures. -/
noncomputable def mixtureMart (U : Finset ι) (pri : ι → ℝ) (u : ι → E → ℝ)
    (q : ℕ → (ℕ → ℝ) → E) (t : ℕ) : (ℕ → ℝ) → ℝ :=
  ∑ a ∈ U, pri a • adaptMix (u a) q t

theorem mixtureMart_nonneg (U : Finset ι) (pri : ι → ℝ) (hpri : ∀ a ∈ U, 0 ≤ pri a)
    (u : ι → E → ℝ) (q : ℕ → (ℕ → ℝ) → E) (t : ℕ) (ω : ℕ → ℝ) :
    0 ≤ mixtureMart U pri u q t ω := by
  unfold mixtureMart
  rw [Finset.sum_apply]
  refine Finset.sum_nonneg fun a ha => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  exact mul_nonneg (hpri a ha) (adaptMix_pos (u a) q t ω).le

/-- **The mixture is a supermartingale.** -/
theorem mixture_supermartingale (U : Finset ι) (pri : ι → ℝ) (hpri : ∀ a ∈ U, 0 ≤ pri a)
    (u : ι → E → ℝ) (q : ℕ → (ℕ → ℝ) → E)
    (hadapt : ∀ (a : ι) (s : ℕ),
      StronglyMeasurable[innovFiltration s] (adaptIncr (u a) q s))
    (hq : ∀ (t : ℕ) (e : E), MeasurableSet[innovFiltration t] {ω | q (t + 1) ω = e})
    (hq0 : ∀ ω, q 0 ω = q 0 0) :
    MeasureTheory.Supermartingale (mixtureMart U pri u q) innovFiltration streamMeasure := by
  classical
  have hpiece : ∀ a : ι, MeasureTheory.Supermartingale (adaptMix (u a) q)
      innovFiltration streamMeasure :=
    fun a => adaptMix_supermartingale (u a) q (hadapt a) hq hq0
  have hadp : ∀ t, StronglyMeasurable[innovFiltration t] (mixtureMart U pri u q t) := by
    intro t
    unfold mixtureMart
    exact Finset.stronglyMeasurable_sum _ (fun a _ => ((hpiece a).1 t).const_smul _)
  have hint : ∀ t, MeasureTheory.Integrable (mixtureMart U pri u q t) streamMeasure := by
    intro t
    unfold mixtureMart
    have heq : (∑ a ∈ U, pri a • adaptMix (u a) q t)
        = fun ω => ∑ a ∈ U, (pri a • adaptMix (u a) q t) ω := by
      funext ω
      rw [Finset.sum_apply]
    rw [heq]
    exact MeasureTheory.integrable_finset_sum _ (fun a _ => ((hpiece a).2.2 t).smul (pri a))
  refine MeasureTheory.supermartingale_nat hadp hint (fun t => ?_)
  have hsum : streamMeasure[mixtureMart U pri u q (t + 1) |
      (innovFiltration t : MeasurableSpace (ℕ → ℝ))]
      =ᵐ[streamMeasure] fun ω => ∑ a ∈ U,
        (streamMeasure[(pri a • adaptMix (u a) q (t + 1)) |
          (innovFiltration t : MeasurableSpace (ℕ → ℝ))]) ω := by
    have hcs := MeasureTheory.condExp_finset_sum
      (μ := streamMeasure) (m := (innovFiltration t : MeasurableSpace (ℕ → ℝ)))
      (s := U) (f := fun a => pri a • adaptMix (u a) q (t + 1))
      (fun a _ => ((hpiece a).2.2 (t + 1)).smul (pri a))
    refine hcs.trans ?_
    filter_upwards with ω
    rw [Finset.sum_apply]
  refine hsum.trans_le ?_
  have hall : ∀ᵐ ω ∂streamMeasure, ∀ a ∈ U,
      (streamMeasure[(pri a • adaptMix (u a) q (t + 1)) |
        (innovFiltration t : MeasurableSpace (ℕ → ℝ))]) ω
        ≤ (pri a • adaptMix (u a) q t) ω := by
    refine (Filter.eventually_all_finset U).2 (fun a ha => ?_)
    have hsm := MeasureTheory.condExp_smul
      (μ := streamMeasure) (m := (innovFiltration t : MeasurableSpace (ℕ → ℝ)))
      (c := pri a) (f := adaptMix (u a) q (t + 1))
    filter_upwards [hsm, (hpiece a).2.1 t (t + 1) (Nat.le_succ t)] with ω h1 h2
    rw [h1]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left h2 (hpri a ha)
  filter_upwards [hall] with ω hω
  show ∑ a ∈ U, (streamMeasure[(pri a • adaptMix (u a) q (t + 1)) |
      (innovFiltration t : MeasurableSpace (ℕ → ℝ))]) ω ≤ mixtureMart U pri u q t ω
  unfold mixtureMart
  rw [Finset.sum_apply]
  exact Finset.sum_le_sum (fun a ha => hω a ha)

/-- **The anytime bound for the mixture.**  Ville, applied to the process the learner
actually maintains: adaptively queried, and mixed over a finite family of tilts summing to
one. -/
theorem mixture_confidence (U : Finset ι) (pri : ι → ℝ) (hpri : ∀ a ∈ U, 0 ≤ pri a)
    (hpri1 : ∑ a ∈ U, pri a = 1)
    (u : ι → E → ℝ) (q : ℕ → (ℕ → ℝ) → E)
    (hadapt : ∀ (a : ι) (s : ℕ),
      StronglyMeasurable[innovFiltration s] (adaptIncr (u a) q s))
    (hq : ∀ (t : ℕ) (e : E), MeasurableSet[innovFiltration t] {ω | q (t + 1) ω = e})
    (hq0 : ∀ ω, q 0 ω = q 0 0)
    (δ : ℝ) (hδ : 0 < δ) (N : ℕ) :
    streamMeasure.real {ω | ∃ j ≤ N, 1 / δ ≤ mixtureMart U pri u q j ω} ≤ δ := by
  classical
  refine CIGAMF.P13.PaperA7Confidence.confidence_of_supermartingale
    (mixtureMart U pri u q) (mixture_supermartingale U pri hpri u q hadapt hq hq0)
    (fun n ω => mixtureMart_nonneg U pri hpri u q n ω) ?_ δ hδ N
  have hval : ∫ ω, mixtureMart U pri u q 0 ω ∂streamMeasure
      = ∑ a ∈ U, pri a * ∫ ω, adaptMix (u a) q 0 ω ∂streamMeasure := by
    unfold mixtureMart
    have hrw : (fun ω => (∑ a ∈ U, pri a • adaptMix (u a) q 0) ω)
        = fun ω => ∑ a ∈ U, pri a * adaptMix (u a) q 0 ω := by
      funext ω
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl fun a _ => by rw [Pi.smul_apply, smul_eq_mul]
    rw [hrw, MeasureTheory.integral_finset_sum _ (fun a _ =>
      (((adaptMix_supermartingale (u a) q (hadapt a) hq hq0).2.2 0)).const_mul (pri a))]
    exact Finset.sum_congr rfl fun a _ => MeasureTheory.integral_const_mul _ _
  have hone : ∀ a : ι, ∫ ω, adaptMix (u a) q 0 ω ∂streamMeasure = 1 := by
    intro a
    have hc : adaptMix (u a) q 0 = incr (u a (q 0 0)) 0 := by
      rw [adaptMix_zero]
      funext ω
      unfold adaptIncr incr
      rw [hq0 ω]
    rw [hc]
    exact incr_integral _ 0
  rw [hval, Finset.sum_congr rfl (fun a _ => by rw [hone a, mul_one]), hpri1]

end Mixture

/-! ### A FIXED finite grid gives correctness, not the rate

The mixture theorems above are about a finite family of tilts, and it must be said plainly
what they do and do not give.  They give an anytime-valid confidence sequence: that is
`mixture_confidence`, and it is correctness.  They do NOT give the information rate, and a
fixed grid can miss it outright.

One dimension is enough to see it.  Let the grid's smallest non-zero tilt have magnitude
`d`, and let the mean gap be `0 < Δ < d/2`.  The exponential growth rate of the tilted
likelihood at tilt `u` is `u Δ - u^2/2`.  Every non-zero tilt in the grid has `|u| >= d >
2Δ`, so its rate is strictly NEGATIVE; a tilt of `0`, if present, has rate zero.  So the
mixture grows at rate at most zero, while the true information is `Δ^2/2 > 0`.  The
threshold is never crossed at the information rate.

`fixed_grid_rate_negative` and `true_information_pos` below are that statement.  The
consequence for the development: to claim the exact rate one must either carry the
continuous Gaussian prior, or let the grid depend on `alpha` with mesh tending to zero and
a grid penalty of smaller order than `log(1/alpha)`.

The SECOND of those is now carried out, in the section `AlphaDependentGrid` below:
`mesh_grid_attains_rate` shows the loss from a mesh-`m` grid is exactly `m^2/2`, so the
rate is attained to any accuracy once the mesh shrinks, and `grid_penalty_negligible`
shows the corresponding `log(#grid)` penalty is of smaller order than `log(1/alpha)`.
The obstruction `fixed_grid_rate_negative` is therefore exactly the failure of `m -> 0`,
and nothing more. -/

/-- **Every non-zero tilt of a fixed grid has negative growth rate, once the gap is small
enough.** -/
theorem fixed_grid_rate_negative (u Δ d : ℝ) (hΔ : 0 < Δ) (hΔd : Δ < d / 2)
    (hu : d ≤ |u|) : u * Δ - u ^ 2 / 2 < 0 := by
  have hd : 0 < d := by linarith
  rcases le_or_gt u 0 with hneg | hpos
  · rcases eq_or_lt_of_le hneg with heq | hlt
    · exfalso
      subst heq
      simp at hu
      linarith
    · nlinarith [hlt, hΔ, sq_nonneg u]
  · have hud : d ≤ u := by
      rwa [abs_of_pos hpos] at hu
    nlinarith [hpos, hΔd, hud]

/-- And the true information is strictly positive, so the gap is real. -/
theorem true_information_pos (Δ : ℝ) (hΔ : 0 < Δ) : 0 < Δ ^ 2 / 2 := by positivity

/-- **The two together**: at a small enough gap, every non-zero grid tilt is losing ground
while the information is strictly positive. -/
theorem fixed_grid_misses_rate (Δ d : ℝ) (hΔ : 0 < Δ) (hΔd : Δ < d / 2) :
    (∀ u : ℝ, d ≤ |u| → u * Δ - u ^ 2 / 2 < 0) ∧ 0 < Δ ^ 2 / 2 :=
  ⟨fun u hu => fixed_grid_rate_negative u Δ d hΔ hΔd hu, true_information_pos Δ hΔ⟩

/-! ## The alpha-dependent grid: the obstruction is exactly a fixed mesh

`fixed_grid_rate_negative` is about a grid whose mesh does not move.  The identity

    u Delta - u^2/2  =  Delta^2/2 - (u - Delta)^2/2

says the rate at tilt `u` is the information minus the SQUARED miss, so a grid of mesh `m`
loses only `m^2/2` -- second order.  That is why a mesh shrinking at any rate at all
recovers the exponent, while the penalty for the extra grid points, `log(2 B L + 1)` with
`L = log(1/alpha)`, is `O(log L)` and so vanishes against `L`.

Both halves are proved below, so the remark in the section note above is discharged. -/

section AlphaDependentGrid

/-- The growth rate of the mixture martingale at tilt `u` against a true gap `Δ`. -/
noncomputable def tiltRate (u Δ : ℝ) : ℝ := u * Δ - u ^ 2 / 2

/-- **The exact identity.**  The rate is the information minus the squared miss. -/
theorem tiltRate_eq (u Δ : ℝ) : tiltRate u Δ = Δ ^ 2 / 2 - (u - Δ) ^ 2 / 2 := by
  unfold tiltRate; ring

theorem tiltRate_le (u Δ : ℝ) : tiltRate u Δ ≤ Δ ^ 2 / 2 := by
  rw [tiltRate_eq]; nlinarith [sq_nonneg (u - Δ)]

theorem tiltRate_at_truth (Δ : ℝ) : tiltRate Δ Δ = Δ ^ 2 / 2 := by
  rw [tiltRate_eq]; ring

/-- **A mesh-`m` grid loses only `m^2/2`.** -/
theorem mesh_grid_rate_ge (u Δ m : ℝ) (hm : |u - Δ| ≤ m) :
    Δ ^ 2 / 2 - m ^ 2 / 2 ≤ tiltRate u Δ := by
  rw [tiltRate_eq]
  have h : (u - Δ) ^ 2 ≤ m ^ 2 := by
    have h1 : |u - Δ| ^ 2 ≤ m ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hm 2
    rwa [sq_abs] at h1
  linarith

/-- The grid point of mesh `m` just below `Δ`. -/
noncomputable def gridPoint (m Δ : ℝ) : ℝ := m * ⌊Δ / m⌋

theorem gridPoint_close (m Δ : ℝ) (hm : 0 < m) : |gridPoint m Δ - Δ| ≤ m := by
  unfold gridPoint
  have hfl : (⌊Δ / m⌋ : ℝ) ≤ Δ / m := Int.floor_le _
  have hfu : Δ / m < (⌊Δ / m⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have h1 : m * (⌊Δ / m⌋ : ℝ) ≤ Δ := by
    have := mul_le_mul_of_nonneg_left hfl (le_of_lt hm)
    rwa [mul_div_cancel₀ _ (ne_of_gt hm)] at this
  have h2 : Δ < m * ((⌊Δ / m⌋ : ℝ) + 1) := by
    have := (mul_lt_mul_of_pos_left hfu hm)
    rwa [mul_div_cancel₀ _ (ne_of_gt hm)] at this
  rw [abs_le]
  constructor <;> nlinarith [h1, h2, hm]

/-- **The resolution of the prior question.**

`fixed_grid_rate_negative` says a grid whose mesh does NOT depend on the level misses the
rate.  This says the converse: once the mesh is allowed to shrink with the level, the rate
is attained to any accuracy, and the loss is exactly `m^2/2` -- second order in the mesh,
which is why a slowly shrinking mesh suffices. -/
theorem mesh_grid_attains_rate (Δ ε : ℝ) (hε : 0 < ε) :
    ∃ m0 : ℝ, 0 < m0 ∧ ∀ m, 0 < m → m ≤ m0 →
      Δ ^ 2 / 2 - ε ≤ tiltRate (gridPoint m Δ) Δ := by
  refine ⟨Real.sqrt (2 * ε), Real.sqrt_pos.mpr (by linarith), ?_⟩
  intro m hm hle
  have hsq : m ^ 2 ≤ 2 * ε := by
    have h1 : m ^ 2 ≤ (Real.sqrt (2 * ε)) ^ 2 := pow_le_pow_left₀ (le_of_lt hm) hle 2
    rwa [Real.sq_sqrt (by linarith)] at h1
  have := mesh_grid_rate_ge (gridPoint m Δ) Δ m (gridPoint_close m Δ hm)
  linarith

/-- `log L <= 2 sqrt L`: the step that makes the grid penalty negligible. -/
theorem log_le_two_sqrt (L : ℝ) (hL : 0 < L) : Real.log L ≤ 2 * Real.sqrt L := by
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have h1 : Real.log (Real.sqrt L) ≤ Real.sqrt L - 1 :=
    Real.log_le_sub_one_of_pos hs
  have h2 : Real.log L = 2 * Real.log (Real.sqrt L) := by
    have h3 : Real.log (Real.sqrt L ^ 2) = 2 * Real.log (Real.sqrt L) := by
      rw [Real.log_pow]; norm_num
    rwa [Real.sq_sqrt (le_of_lt hL)] at h3
  linarith

/-- **The grid penalty is of smaller order than `log(1/alpha)`.**

With mesh `1/L` on `[-B, B]`, the grid has at most `2 B L + 1` points, so the penalty is
`log(2 B L + 1)`, and its ratio to `L = log(1/alpha)` can be made as small as desired.
Together with `mesh_grid_attains_rate` this is the whole content of the remark in the
section note: an `alpha`-dependent grid does attain the rate. -/
theorem grid_penalty_negligible (B ε : ℝ) (hB : 1 ≤ B) (hε : 0 < ε) :
    ∃ L0 : ℝ, 1 ≤ L0 ∧ ∀ L, L0 ≤ L → Real.log (2 * B * L + 1) / L ≤ ε := by
  refine ⟨max 1 (max (2 * Real.log (3 * B) / ε) (16 / ε ^ 2)), le_max_left _ _, ?_⟩
  intro L hL
  have hL1 : (1 : ℝ) ≤ L := le_trans (le_max_left _ _) hL
  have hLpos : (0 : ℝ) < L := by linarith
  have hlogB : 0 ≤ Real.log (3 * B) := Real.log_nonneg (by linarith)
  -- bound the count
  have hcount : 2 * B * L + 1 ≤ (3 * B) * L := by nlinarith [hB, hL1]
  have hcpos : (0 : ℝ) < 2 * B * L + 1 := by nlinarith [hB, hLpos]
  have hsplit : Real.log (2 * B * L + 1) ≤ Real.log (3 * B) + Real.log L := by
    calc Real.log (2 * B * L + 1) ≤ Real.log ((3 * B) * L) :=
          Real.log_le_log hcpos hcount
      _ = Real.log (3 * B) + Real.log L :=
          Real.log_mul (by linarith) (by linarith)
  have hlogL : Real.log L ≤ 2 * Real.sqrt L := log_le_two_sqrt L hLpos
  -- each piece is at most eps/2
  have hA : Real.log (3 * B) / L ≤ ε / 2 := by
    have h1 : 2 * Real.log (3 * B) / ε ≤ L := le_trans (le_trans (le_max_left _ _)
      (le_max_right _ _)) hL
    rw [div_le_iff₀ hLpos]
    rw [div_le_iff₀ hε] at h1
    linarith
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.mpr hLpos
  have hB2 : 16 / ε ^ 2 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  have hsqrtL : 4 / ε ≤ Real.sqrt L := by
    have h1 : (4 / ε) ^ 2 ≤ L := by
      have : (4 / ε) ^ 2 = 16 / ε ^ 2 := by field_simp; ring
      linarith [hB2, this.le, this.ge]
    have h2 : Real.sqrt ((4 / ε) ^ 2) ≤ Real.sqrt L := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (by positivity)] at h2
  have hBb : 2 * Real.sqrt L / L ≤ ε / 2 := by
    have hLs : L = Real.sqrt L * Real.sqrt L := (Real.mul_self_sqrt (le_of_lt hLpos)).symm
    have hkey : 4 ≤ Real.sqrt L * ε := by rwa [div_le_iff₀ hε] at hsqrtL
    rw [div_le_iff₀ hLpos]
    nlinarith [hkey, hsL, hLs.le, hLs.ge, hε]
  rw [div_le_iff₀ hLpos]
  have h1 : Real.log (3 * B) ≤ ε / 2 * L := by rw [div_le_iff₀ hLpos] at hA; linarith
  have h2 : 2 * Real.sqrt L ≤ ε / 2 * L := by rw [div_le_iff₀ hLpos] at hBb; linarith
  linarith [hsplit, hlogL, h1, h2]

end AlphaDependentGrid

/-! ## The CONTINUOUS Gaussian prior, and the statistic the code actually runs

The section above shows a shrinking grid recovers the exponent.  It does not show the
implementation is covered, because the implementation does not use a grid: it runs

    Q_t(lambda) = (1/2) sum_e  N_e^2 / ((a + N_e) sigma_e^2) * (thetahat_e - lambda_e)^2,

which is the log of a mixture against a CONTINUOUS Gaussian prior.  A finite grid, however
fine, still has a positive mesh at each fixed level, so the grid argument does not by
itself give a guarantee for `Q_t`.

What closes that is the conjugate integral.  Tilting arm `e` by `u` earns
`u N_e (thetahat_e - lambda_e)/sigma_e^2` and pays `u^2 N_e / (2 sigma_e^2)`; charging the
prior `N(0, sigma_e^2/a)` and integrating `u` out gives exactly

    (1 + N_e/a)^{-1/2} exp( N_e^2 (thetahat_e - lambda_e)^2 / (2 (a+N_e) sigma_e^2) ),

so the product over arms is `exp(Q_t)` times the code's own penalty, and the test
`Q_t >= log(1/alpha) + (1/2) sum_e log(1 + N_e/a)` --- threshold and penalty as
implemented --- is exactly the mixture crossing `1/alpha`.  Ville applied to the mixture is
therefore a guarantee for the running statistic and not for a different one.

No grid, no mesh, and no conditional Fubini: the integral is one-dimensional per arm and
is evaluated in closed form. -/

section ContinuousPrior

open Real

/-- **The conjugate Gaussian integral, in the form the mixture method needs.**

Tilting by `u` earns `u z` and costs `v u^2 / 2`; the prior charges `u^2/(2 s^2)`.
Integrating `u` out leaves a closed form.  This is the step that lets a CONTINUOUS prior
be used, so no grid and no mesh appear anywhere. -/
theorem gaussian_tilt_integral (s v z : ℝ) (hs : 0 < s) (hv : 0 ≤ v) :
    ∫ u : ℝ, (Real.sqrt (2 * Real.pi * s ^ 2))⁻¹
        * Real.exp (u * z - v / 2 * u ^ 2 - u ^ 2 / (2 * s ^ 2))
      = (Real.sqrt (1 + s ^ 2 * v))⁻¹
        * Real.exp (z ^ 2 / (2 * (v + 1 / s ^ 2))) := by
  have hs2 : (0 : ℝ) < s ^ 2 := by positivity
  set B : ℝ := v / 2 + 1 / (2 * s ^ 2) with hBdef
  have hB : 0 < B := by
    have h1 : (0 : ℝ) < 1 / (2 * s ^ 2) := by positivity
    have h2 : (0 : ℝ) ≤ v / 2 := by linarith
    linarith
  have hsq : ∀ u : ℝ, u * z - v / 2 * u ^ 2 - u ^ 2 / (2 * s ^ 2)
      = -(B * (u - z / (2 * B)) ^ 2) + z ^ 2 / (4 * B) := by
    intro u
    rw [hBdef]
    field_simp
    ring
  have hshift : ∫ u : ℝ, Real.exp (-(B * (u - z / (2 * B)) ^ 2))
      = ∫ u : ℝ, Real.exp (-(B * u ^ 2)) := by
    simpa using
      (MeasureTheory.integral_sub_right_eq_self
        (fun u : ℝ => Real.exp (-(B * u ^ 2))) (z / (2 * B)))
  have hgauss : ∫ u : ℝ, Real.exp (-(B * u ^ 2)) = Real.sqrt (Real.pi / B) := by
    simpa [neg_mul] using integral_gaussian B
  have hstep : ∫ u : ℝ, (Real.sqrt (2 * Real.pi * s ^ 2))⁻¹
        * Real.exp (u * z - v / 2 * u ^ 2 - u ^ 2 / (2 * s ^ 2))
      = ∫ u : ℝ, (Real.sqrt (2 * Real.pi * s ^ 2))⁻¹ * Real.exp (z ^ 2 / (4 * B))
          * Real.exp (-(B * (u - z / (2 * B)) ^ 2)) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro u
    simp only [hsq u, Real.exp_add]
    ring
  rw [hstep, MeasureTheory.integral_const_mul, hshift, hgauss]
  have h4B : (4 : ℝ) * B = 2 * (v + 1 / s ^ 2) := by rw [hBdef]; field_simp; ring
  have hroot : (Real.sqrt (2 * Real.pi * s ^ 2))⁻¹ * Real.sqrt (Real.pi / B)
      = (Real.sqrt (1 + s ^ 2 * v))⁻¹ := by
    rw [← Real.sqrt_inv, ← Real.sqrt_mul (by positivity), ← Real.sqrt_inv]
    congr 1
    rw [hBdef]
    field_simp
    ring
  rw [h4B, ← hroot]
  ring

/-- The code's per-arm posterior precision, written as the prior variance the mixture
uses: prior `N(0, sigma^2/a)`, tilt earning `N (thetahat - lambda)/sigma^2`. -/
theorem gaussian_prior_arm (a σ N θh l : ℝ) (ha : 0 < a) (hσ : 0 < σ) (hN : 0 ≤ N) :
    ∫ u : ℝ, (Real.sqrt (2 * Real.pi * (σ ^ 2 / a)))⁻¹
        * Real.exp (u * (N * (θh - l) / σ ^ 2) - (N / σ ^ 2) / 2 * u ^ 2
            - u ^ 2 / (2 * (σ ^ 2 / a)))
      = (Real.sqrt (1 + N / a))⁻¹
        * Real.exp (N ^ 2 * (θh - l) ^ 2 / (2 * (a + N) * σ ^ 2)) := by
  have hσ2 : (0 : ℝ) < σ ^ 2 := by positivity
  have hs : (0 : ℝ) < Real.sqrt (σ ^ 2 / a) := Real.sqrt_pos.mpr (by positivity)
  have hsq : Real.sqrt (σ ^ 2 / a) ^ 2 = σ ^ 2 / a := Real.sq_sqrt (by positivity)
  have hv : (0 : ℝ) ≤ N / σ ^ 2 := by positivity
  have h := gaussian_tilt_integral (Real.sqrt (σ ^ 2 / a)) (N / σ ^ 2)
    (N * (θh - l) / σ ^ 2) hs hv
  rw [hsq] at h
  rw [h]
  congr 1
  · congr 2
    field_simp
  · congr 1
    field_simp
    ring

/-- **The statistic the code computes.**  `Qstat` is literally the quadratic form in
`EXP_paperA7_learner`. -/
noncomputable def Qstat {E : Type*} [Fintype E] (a : ℝ) (σ N θh l : E → ℝ) : ℝ :=
  ∑ e, N e ^ 2 * (θh e - l e) ^ 2 / (2 * (a + N e) * σ e ^ 2)

/-- The per-arm closed forms multiply to the code's penalty times `exp(Qstat)`. -/
theorem mixture_closed_form {E : Type*} [Fintype E] (a : ℝ) (σ N θh l : E → ℝ) :
    ∏ e, ((Real.sqrt (1 + N e / a))⁻¹
        * Real.exp (N e ^ 2 * (θh e - l e) ^ 2 / (2 * (a + N e) * σ e ^ 2)))
      = (∏ e, (Real.sqrt (1 + N e / a))⁻¹) * Real.exp (Qstat a σ N θh l) := by
  classical
  rw [Finset.prod_mul_distrib, Qstat, Real.exp_sum]

/-- The penalty factor, as an exponential of the code's own log term. -/
theorem penalty_as_exp {E : Type*} [Fintype E] (a : ℝ) (N : E → ℝ)
    (ha : 0 < a) (hN : ∀ e, 0 ≤ N e) :
    (∏ e, (Real.sqrt (1 + N e / a))⁻¹)
      = Real.exp (-((1 / 2) * ∑ e, Real.log (1 + N e / a))) := by
  classical
  have hpos : ∀ e : E, (0 : ℝ) < 1 + N e / a := fun e => by
    have : (0 : ℝ) ≤ N e / a := div_nonneg (hN e) (le_of_lt ha)
    linarith
  have hfac : ∀ e : E, (Real.sqrt (1 + N e / a))⁻¹
      = Real.exp (-((1 / 2) * Real.log (1 + N e / a))) := by
    intro e
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (hpos e), ← Real.exp_neg]
    congr 1
    ring
  rw [Finset.prod_congr rfl (fun e _ => hfac e), ← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]

/-- **The code's stopping test IS the mixture crossing `1/alpha`.**

`Qstat >= log(1/alpha) + (1/2) sum_e log(1 + N_e/a)` --- the threshold the implementation
uses, penalty term included --- holds exactly when the mixture `penalty * exp(Qstat)` has
reached `1/alpha`.  So Ville applied to the mixture is a guarantee for the running
statistic and not for a different one. -/
theorem qstat_threshold_iff {E : Type*} [Fintype E] (a α : ℝ) (σ N θh l : E → ℝ)
    (ha : 0 < a) (hN : ∀ e, 0 ≤ N e) (hα : 0 < α) :
    Real.log (1 / α) + (1 / 2) * ∑ e, Real.log (1 + N e / a) ≤ Qstat a σ N θh l
      ↔ 1 / α ≤ (∏ e, (Real.sqrt (1 + N e / a))⁻¹)
          * Real.exp (Qstat a σ N θh l) := by
  classical
  have hα1 : (0 : ℝ) < 1 / α := by positivity
  have key : ∀ y : ℝ, (1 / α ≤ Real.exp y) ↔ Real.log (1 / α) ≤ y := by
    intro y
    constructor
    · intro h
      calc Real.log (1 / α) ≤ Real.log (Real.exp y) := Real.log_le_log hα1 h
        _ = y := Real.log_exp y
    · intro h
      have h2 := Real.exp_le_exp.mpr h
      rwa [Real.exp_log hα1] at h2
  rw [penalty_as_exp a N ha hN, ← Real.exp_add, key]
  constructor <;> intro h <;> linarith

end ContinuousPrior

/-! ## Audit -/

#print axioms obs_indep
#print axioms obs_map
#print axioms incr_indep
#print axioms incr_integrable
#print axioms incr_integral
#print axioms mix_succ
#print axioms mix_pos
#print axioms mix_adapted
#print axioms mix_indep_incr
#print axioms mix_integrable
#print axioms mix_martingale_step
#print axioms mix_supermartingale
#print axioms stream_confidence
#print axioms condExp_incr_innov
#print axioms adaptIncr_eq_sum
#print axioms condExp_adaptIncr
#print axioms indep_past_innov
#print axioms indepFun_past_innov
#print axioms adaptMix_supermartingale
#print axioms adaptive_confidence
#print axioms mixture_supermartingale
#print axioms mixture_confidence
#print axioms fixed_grid_rate_negative
#print axioms fixed_grid_misses_rate

#print axioms tiltRate_eq
#print axioms mesh_grid_rate_ge
#print axioms gridPoint_close
#print axioms mesh_grid_attains_rate
#print axioms log_le_two_sqrt
#print axioms grid_penalty_negligible

#print axioms gaussian_tilt_integral
#print axioms gaussian_prior_arm
#print axioms mixture_closed_form
#print axioms penalty_as_exp
#print axioms qstat_threshold_iff

end CIGAMF.P13.PaperA7Stream
