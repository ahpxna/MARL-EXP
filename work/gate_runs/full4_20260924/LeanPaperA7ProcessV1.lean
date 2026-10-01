import «LeanPaperAStopJoinV1»
import «LeanPaperA7StreamV1»

/-!
# Paper A7: the learner as a process on the observation stream, and its confidence event

`LeanPaperAStopJoinV1.closed_form_error_bound` is Ville's inequality for the code's closed-form
mixture, for ANY process that satisfies the one-step martingale identity.  Its docstring
names what was left: identifying the implementation's queries `q_t`, counts `N_e(t)` and
standardised sums `S_e(t)` with such a process.  This module does that.

* The world `theta, sigma` generates observations from the innovation stream
  (`LeanPaperA7StreamV1.streamMeasure`, i.i.d. `N(0,1)`): round `i + 1` uses innovation
  `omega (i + 1)`, `Y = theta_q + sigma_q omega (i+1)`.
* A `Learner` is ONE query rule per round, a measurable function of the history of
  (query, observation) pairs.  The world is not an argument of the rule: `theta` and
  `sigma` enter only through the observations (`histF`).
* The counts `NF`, the standardised sums `SF` and the next query `qF` are functions of the
  past innovations `Xp t`; the process `Mproc t = Mval (NF t) (SF t) (Xp t)` is the code's
  mixture (`Mval_eq_Mstat`).
* `proc_step`: the martingale identity at every round, from `martingale_step` (the fresh
  innovation is independent of the past by the product structure of the stream);
  `Mproc_integrable`: integrability, by induction with `joint_integrable`.
* `ville_process`: `P(exists j <= T, Qstat_j > bthr(delta)) <= delta` for the ACTUAL learner.
* `good_window_real`: with the code's per-time level `delta_j = j^(-4)` on a window
  `[n, T]`, the failure probability is at most `n^(-4)`.
* `radius_of_good`: on the good event the raw mean's error is at most
  `sigma_e sqrt(2 (a + N_e) b) / N_e`, the radius `r_t` the code computes
  (`EXP_paperA7_learner.py`, `r_t = max_e sqrt(var_e) sqrt(2 (a + N_e) b_t4) / N_e`).
-/

namespace CIGAMF.P13.PaperA7Process

open MeasureTheory ProbabilityTheory
open CIGAMF.P13.PaperA7Stream CIGAMF.P13.PaperAAdaptMart CIGAMF.P13.PaperAMartingale
open CIGAMF.P13.PaperA7Confidence CIGAMF.P13.PaperAStopJoin

variable {E : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace E]
  [MeasurableSingletonClass E]

/-- A deterministic adaptive learner: the query of round `t + 1` from the observed history of
the first `t` rounds. -/
structure Learner (E : Type*) [MeasurableSpace E] where
  rule : ∀ t, (Fin t → E × ℝ) → E
  meas : ∀ t, Measurable (rule t)

/-- The observed history of `t` rounds, as a function of the `t` standardised innovations. -/
noncomputable def histF (L : Learner E) (θ σ : E → ℝ) : ∀ t, (Fin t → ℝ) → (Fin t → E × ℝ)
  | 0 => fun _ => Fin.elim0
  | t + 1 => fun z =>
      Fin.snoc (α := fun _ => E × ℝ) (histF L θ σ t (Fin.init z))
        (L.rule t (histF L θ σ t (Fin.init z)),
          θ (L.rule t (histF L θ σ t (Fin.init z)))
            + σ (L.rule t (histF L θ σ t (Fin.init z))) * z (Fin.last t))

variable (L : Learner E) (θ σ : E → ℝ)

theorem histF_snoc (t : ℕ) (x : Fin t → ℝ) (y : ℝ) :
    histF L θ σ (t + 1) (Fin.snoc (α := fun _ => ℝ) x y)
      = Fin.snoc (α := fun _ => E × ℝ) (histF L θ σ t x)
          (L.rule t (histF L θ σ t x),
            θ (L.rule t (histF L θ σ t x)) + σ (L.rule t (histF L θ σ t x)) * y) := by
  simp only [histF, Fin.init_snoc, Fin.snoc_last]

theorem measurable_init (t : ℕ) : Measurable (fun z : Fin (t + 1) → ℝ => Fin.init z) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

theorem measurable_histF : ∀ t, Measurable (histF L θ σ t)
  | 0 => by
      show Measurable fun _ : Fin 0 → ℝ => (Fin.elim0 : Fin 0 → E × ℝ)
      exact measurable_const
  | t + 1 => by
      have hh := (measurable_histF t).comp (measurable_init t)
      have hq := (L.meas t).comp hh
      refine measurable_pi_lambda _ fun i => ?_
      refine Fin.lastCases (motive := fun i => Measurable fun z => histF L θ σ (t + 1) z i)
        ?_ (fun j => ?_) i
      · simp only [histF, Fin.snoc_last]
        refine hq.prodMk ?_
        exact ((Measurable.of_discrete (f := θ)).comp hq).add
          (((Measurable.of_discrete (f := σ)).comp hq).mul (measurable_pi_apply _))
      · simp only [histF, Fin.snoc_castSucc]
        exact (measurable_pi_apply j).comp hh

/-- The observation is the world's mean plus scaled innovation, at every round. -/
theorem histF_obs : ∀ (t : ℕ) (z : Fin t → ℝ) (i : Fin t),
    (histF L θ σ t z i).2 = θ (histF L θ σ t z i).1 + σ (histF L θ σ t z i).1 * z i
  | 0, _, i => i.elim0
  | t + 1, z, i => by
      refine Fin.lastCases (motive := fun i => (histF L θ σ (t + 1) z i).2
        = θ (histF L θ σ (t + 1) z i).1 + σ (histF L θ σ (t + 1) z i).1 * z i) ?_
        (fun j => ?_) i
      · simp only [histF, Fin.snoc_last]
      · simp only [histF, Fin.snoc_castSucc]
        exact histF_obs t (Fin.init z) j

/-- The next query, the counts and the standardised sums, as functions of the past. -/
noncomputable def qF (t : ℕ) (z : Fin t → ℝ) : E := L.rule t (histF L θ σ t z)

noncomputable def NF (t : ℕ) (z : Fin t → ℝ) (e : E) : ℕ :=
  ∑ i : Fin t, if (histF L θ σ t z i).1 = e then 1 else 0

noncomputable def SF (t : ℕ) (z : Fin t → ℝ) (e : E) : ℝ :=
  ∑ i : Fin t, if (histF L θ σ t z i).1 = e then z i else 0

theorem NF_snoc (t : ℕ) (x : Fin t → ℝ) (y : ℝ) (e : E) :
    NF L θ σ (t + 1) (Fin.snoc (α := fun _ => ℝ) x y) e
      = NF L θ σ t x e + if qF L θ σ t x = e then 1 else 0 := by
  unfold NF qF
  rw [histF_snoc, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem SF_snoc (t : ℕ) (x : Fin t → ℝ) (y : ℝ) (e : E) :
    SF L θ σ (t + 1) (Fin.snoc (α := fun _ => ℝ) x y) e
      = SF L θ σ t x e + if qF L θ σ t x = e then y else 0 := by
  unfold SF qF
  rw [histF_snoc, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem Mval_snoc (a : ℝ) (t : ℕ) (x : Fin t → ℝ) (y : ℝ) :
    Mval a (NF L θ σ (t + 1)) (SF L θ σ (t + 1)) (Fin.snoc (α := fun _ => ℝ) x y)
      = Mstep a (NF L θ σ t) (SF L θ σ t) (qF L θ σ t) (x, y) := by
  unfold Mval Mstep
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [NF_snoc, SF_snoc]
  push_cast
  rfl

theorem measurable_NF (t : ℕ) (e : E) : Measurable fun z => NF L θ σ t z e := by
  unfold NF
  refine Finset.measurable_sum _ fun i _ => ?_
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (measurable_fst.comp ((measurable_pi_apply i).comp (measurable_histF L θ σ t)))
    (measurableSet_singleton e)

theorem measurable_SF (t : ℕ) (e : E) : Measurable fun z => SF L θ σ t z e := by
  unfold SF
  refine Finset.measurable_sum _ fun i _ => ?_
  refine Measurable.ite ?_ (measurable_pi_apply i) measurable_const
  exact (measurable_fst.comp ((measurable_pi_apply i).comp (measurable_histF L θ σ t)))
    (measurableSet_singleton e)

theorem measurable_qF (t : ℕ) : Measurable (qF L θ σ t) :=
  (L.meas t).comp (measurable_histF L θ σ t)

theorem measurable_Mval (a : ℝ) (t : ℕ) : Measurable (Mval a (NF L θ σ t) (SF L θ σ t)) := by
  unfold Mval mgfFactor
  refine Finset.measurable_prod _ (fun e _ => ?_)
  have hn : Measurable (fun x => a + (NF L θ σ t x e : ℝ)) :=
    measurable_const.add ((measurable_from_top : Measurable (fun n : ℕ => (n : ℝ))).comp
      (measurable_NF L θ σ t e))
  exact (Real.continuous_sqrt.measurable.comp (measurable_const.div hn)).mul
    (Real.continuous_exp.measurable.comp (((measurable_SF L θ σ t e).pow_const 2).div
      (measurable_const.mul hn)))

/-! ## The process on the stream -/

/-- The past standardised innovations of `t` rounds: `omega 1, ..., omega t`. -/
def Xp (t : ℕ) (ω : ℕ → ℝ) : Fin t → ℝ := fun i => ω ((i : ℕ) + 1)

theorem measurable_Xp (t : ℕ) : Measurable (Xp t) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

theorem Xp_succ (t : ℕ) (ω : ℕ → ℝ) :
    Xp (t + 1) ω = Fin.snoc (α := fun _ => ℝ) (Xp t ω) (ω (t + 1)) := by
  funext i
  refine Fin.lastCases (motive := fun i => Xp (t + 1) ω i
    = Fin.snoc (α := fun _ => ℝ) (Xp t ω) (ω (t + 1)) i) ?_ (fun j => ?_) i
  · simp [Xp]
  · simp [Xp]

/-- The code's mixture along the actual run. -/
noncomputable def Mproc (a : ℝ) (t : ℕ) (ω : ℕ → ℝ) : ℝ :=
  Mval a (NF L θ σ t) (SF L θ σ t) (Xp t ω)

theorem Mproc_succ (a : ℝ) (t : ℕ) :
    Mproc L θ σ a (t + 1)
      = fun ω => Mstep a (NF L θ σ t) (SF L θ σ t) (qF L θ σ t) (Xp t ω, obs (t + 1) ω) := by
  funext ω
  unfold Mproc
  rw [Xp_succ, Mval_snoc]
  rfl

theorem Mproc_zero (a : ℝ) (ha : 0 < a) (ω : ℕ → ℝ) : Mproc L θ σ a 0 ω = 1 := by
  have hN : NF L θ σ 0 = fun _ _ => 0 := by funext z e; simp [NF]
  have hS : SF L θ σ 0 = fun _ _ => 0 := by funext z e; simp [SF]
  unfold Mproc
  rw [hN, hS]
  exact Mval_init a ha _

/-- The filtration of the past innovations. -/
noncomputable def pastFiltration : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → ℝ)) where
  seq t := MeasurableSpace.comap (Xp t) inferInstance
  mono' s t hst := by
    have hfac : Xp s = (fun z : Fin t → ℝ => fun i : Fin s => z (Fin.castLE hst i)) ∘ Xp t := by
      funext ω i
      rfl
    show MeasurableSpace.comap (Xp s) inferInstance ≤ MeasurableSpace.comap (Xp t) inferInstance
    rw [hfac, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono
      (measurable_pi_lambda _ fun _ => measurable_pi_apply _).comap_le
  le' t := (measurable_Xp t).comap_le

/-- The past is measurable in the stream's natural filtration. -/
theorem measurable_Xp_innov (t : ℕ) : Measurable[innovFiltration t] (Xp t) := by
  have hA : StronglyAdapted innovFiltration obs :=
    Filtration.stronglyAdapted_natural (fun n => (obs_measurable n).stronglyMeasurable)
  have hcoord : ∀ i : Fin t, Measurable[innovFiltration t] (fun ω : ℕ → ℝ => Xp t ω i) :=
    fun i => ((hA ((i : ℕ) + 1)).measurable).mono (innovFiltration.mono i.isLt) le_rfl
  letI : MeasurableSpace (ℕ → ℝ) := innovFiltration t
  exact measurable_pi_lambda _ hcoord

/-- **The fresh innovation is independent of the past.** -/
theorem indep_Xp (t : ℕ) : IndepFun (Xp t) (obs (t + 1)) streamMeasure := by
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le (indep_past_innov t) (measurable_Xp_innov t).comap_le le_rfl

theorem Mproc_integrable (a : ℝ) (ha : 0 < a) :
    ∀ t, Integrable (Mproc L θ σ a t) streamMeasure
  | 0 => by
      have : Mproc L θ σ a 0 = fun _ => 1 := funext (Mproc_zero L θ σ a ha)
      rw [this]
      exact integrable_const _
  | t + 1 => by
      have hjoint := joint_integrable streamMeasure a ha (Xp t) (obs (t + 1)) (measurable_Xp t)
        (obs_measurable _) (obs_map _) (indep_Xp t) (NF L θ σ t) (SF L θ σ t) (qF L θ σ t)
        (measurable_NF L θ σ t) (measurable_SF L θ σ t) (measurable_qF L θ σ t)
        (Mproc_integrable a ha t)
      have hmeas := Mstep_measurable a (NF L θ σ t) (SF L θ σ t) (qF L θ σ t)
        (measurable_NF L θ σ t) (measurable_SF L θ σ t) (measurable_qF L θ σ t)
      rw [Mproc_succ]
      exact (integrable_map_measure hmeas.aestronglyMeasurable
        ((measurable_Xp t).prodMk (obs_measurable _)).aemeasurable).mp hjoint

/-- **The martingale identity of the actual learner's mixture.** -/
theorem proc_step (a : ℝ) (ha : 0 < a) (t : ℕ) :
    streamMeasure[Mproc L θ σ a (t + 1) | pastFiltration t]
      =ᵐ[streamMeasure] Mproc L θ σ a t := by
  have hjoint := joint_integrable streamMeasure a ha (Xp t) (obs (t + 1)) (measurable_Xp t)
    (obs_measurable _) (obs_map _) (indep_Xp t) (NF L θ σ t) (SF L θ σ t) (qF L θ σ t)
    (measurable_NF L θ σ t) (measurable_SF L θ σ t) (measurable_qF L θ σ t)
    (Mproc_integrable L θ σ a ha t)
  rw [Mproc_succ]
  exact martingale_step streamMeasure a ha (Xp t) (obs (t + 1)) (measurable_Xp t)
    (obs_measurable _) (obs_map _) (indep_Xp t) (NF L θ σ t) (SF L θ σ t) (qF L θ σ t) hjoint

/-- The counts and standardised sums along the run. -/
noncomputable def Nc (t : ℕ) (ω : ℕ → ℝ) (e : E) : ℝ := (NF L θ σ t (Xp t ω) e : ℝ)
noncomputable def Sc (t : ℕ) (ω : ℕ → ℝ) (e : E) : ℝ := SF L θ σ t (Xp t ω) e

theorem measurable_Nc (t : ℕ) (e : E) : Measurable fun ω => Nc L θ σ t ω e :=
  (measurable_from_top : Measurable (fun n : ℕ => (n : ℝ))).comp
    ((measurable_NF L θ σ t e).comp (measurable_Xp t))

theorem measurable_Sc (t : ℕ) (e : E) : Measurable fun ω => Sc L θ σ t ω e :=
  (measurable_SF L θ σ t e).comp (measurable_Xp t)

theorem measurable_bthr (a δ : ℝ) (t : ℕ) : Measurable fun ω => bthr a δ (Nc L θ σ t ω) := by
  unfold bthr
  refine measurable_const.add (Measurable.div_const ?_ _)
  refine Finset.measurable_sum _ fun e _ => ?_
  exact Real.measurable_log.comp (measurable_const.add ((measurable_Nc L θ σ t e).div_const _))

theorem measurable_Qstat (a : ℝ) (t : ℕ) :
    Measurable fun ω => PaperA7Confidence.Qstat a (Sc L θ σ t ω) (Nc L θ σ t ω) := by
  unfold PaperA7Confidence.Qstat
  refine Finset.measurable_sum _ fun e _ => ?_
  exact ((measurable_Sc L θ σ t e).pow_const 2).div
    (measurable_const.mul (measurable_const.add (measurable_Nc L θ σ t e)))

/-- **Ville's inequality for the actual learner.** -/
theorem ville_process (a δ : ℝ) (ha : 0 < a) (hδ : 0 < δ) (T : ℕ) :
    streamMeasure.real {ω | ∃ j ≤ T,
      bthr a δ (Nc L θ σ j ω) < PaperA7Confidence.Qstat a (Sc L θ σ j ω) (Nc L θ σ j ω)} ≤ δ := by
  have hadapt : StronglyAdapted pastFiltration (Mproc L θ σ a) := by
    intro t
    exact ((measurable_Mval L θ σ a t).comp (comap_measurable (Xp t))).stronglyMeasurable
  have hstart : ∫ ω, Mproc L θ σ a 0 ω ∂streamMeasure ≤ 1 := by
    rw [show Mproc L θ σ a 0 = fun _ => 1 from funext (Mproc_zero L θ σ a ha)]
    simp
  have hmeas : MeasurableSet {ω | ∃ j ≤ T,
      bthr a δ (Nc L θ σ j ω) < PaperA7Confidence.Qstat a (Sc L θ σ j ω) (Nc L θ σ j ω)} := by
    have : {ω | ∃ j ≤ T, bthr a δ (Nc L θ σ j ω) < PaperA7Confidence.Qstat a (Sc L θ σ j ω) (Nc L θ σ j ω)}
        = ⋃ j ∈ Finset.Iic T,
          {ω | bthr a δ (Nc L θ σ j ω) < PaperA7Confidence.Qstat a (Sc L θ σ j ω) (Nc L θ σ j ω)} := by
      ext ω
      simp
    rw [this]
    exact Finset.measurableSet_biUnion _ fun j _ =>
      measurableSet_lt (measurable_bthr L θ σ a δ j) (measurable_Qstat L θ σ a j)
  exact closed_form_error_bound (μ := streamMeasure) (𝒢 := pastFiltration) a δ ha hδ
    (Nc L θ σ) (Sc L θ σ) (fun t ω e => Nat.cast_nonneg _) (Mproc L θ σ a) (fun t ω => rfl)
    hadapt (Mproc_integrable L θ σ a ha) (proc_step L θ σ a ha) hstart T hmeas

/-- The code's per-time level `j^(-4)` only raises the threshold after `n`. -/
theorem bthr_mono_level (a : ℝ) (N : E → ℝ) (n j : ℕ) (hn : 1 ≤ n) (hnj : n ≤ j) :
    bthr a ((n : ℝ) ^ 4)⁻¹ N ≤ bthr a ((j : ℝ) ^ 4)⁻¹ N := by
  unfold bthr
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnjR : (n : ℝ) ≤ j := by exact_mod_cast hnj
  have : Real.log (1 / ((n : ℝ) ^ 4)⁻¹) ≤ Real.log (1 / ((j : ℝ) ^ 4)⁻¹) := by
    rw [one_div, one_div, inv_inv, inv_inv]
    exact Real.log_le_log (by positivity) (pow_le_pow_left₀ hn0.le hnjR 4)
  linarith

/-- **The good window of the actual learner**: at the code's levels `j^(-4)`, the statistic at
the true world stays below its threshold at every time in `[n, T]` except with probability
`n^(-4)`. -/
theorem good_window_real (a : ℝ) (ha : 0 < a) (n T : ℕ) (hn : 1 ≤ n) :
    streamMeasure.real {ω | ∃ j, n ≤ j ∧ j ≤ T ∧
      bthr a ((j : ℝ) ^ 4)⁻¹ (Nc L θ σ j ω) < PaperA7Confidence.Qstat a (Sc L θ σ j ω) (Nc L θ σ j ω)}
      ≤ ((n : ℝ) ^ 4)⁻¹ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine le_trans (measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _))
    (ville_process L θ σ a ((n : ℝ) ^ 4)⁻¹ ha (by positivity) T)
  obtain ⟨j, hnj, hjT, hj⟩ := hω
  exact ⟨j, hjT, lt_of_le_of_lt (bthr_mono_level a _ n j hn hnj) hj⟩

/-! ## The radius on the good event -/

/-- Each summand of the statistic is at most the statistic. -/
theorem S_sq_le (a : ℝ) (ha : 0 < a) (S N : E → ℝ) (hN : ∀ e, 0 ≤ N e) (b : ℝ)
    (hQ : PaperA7Confidence.Qstat a S N ≤ b) (e : E) : S e ^ 2 ≤ 2 * (a + N e) * b := by
  have hpos : ∀ f, 0 < 2 * (a + N f) := fun f => by have := hN f; positivity
  have hterm : S e ^ 2 / (2 * (a + N e)) ≤ PaperA7Confidence.Qstat a S N :=
    Finset.single_le_sum (f := fun f => S f ^ 2 / (2 * (a + N f)))
      (fun f _ => div_nonneg (sq_nonneg _) (hpos f).le) (Finset.mem_univ e)
  have := (div_le_iff₀ (hpos e)).mp (hterm.trans hQ)
  linarith

/-- The code's sum of observations of cell `e`. -/
noncomputable def Ysum (t : ℕ) (z : Fin t → ℝ) (e : E) : ℝ :=
  ∑ i : Fin t, if (histF L θ σ t z i).1 = e then (histF L θ σ t z i).2 else 0

/-- The sum of observations is `N_e theta_e + sigma_e S_e`. -/
theorem Ysum_eq (t : ℕ) (z : Fin t → ℝ) (e : E) :
    Ysum L θ σ t z e = (NF L θ σ t z e : ℝ) * θ e + σ e * SF L θ σ t z e := by
  unfold Ysum NF SF
  push_cast
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : (histF L θ σ t z i).1 = e
  · rw [if_pos h, if_pos h, if_pos h, histF_obs, h]
    ring
  · rw [if_neg h, if_neg h, if_neg h]
    ring

/-- **The radius on the good event**: the raw mean `Ysum / N` is within
`sigma_e sqrt(2 (a + N_e) b) / N_e` of `theta_e`. -/
theorem radius_of_good (a : ℝ) (ha : 0 < a) (hσ : ∀ e, 0 < σ e) (t : ℕ) (z : Fin t → ℝ)
    (b : ℝ) (hQ : PaperA7Confidence.Qstat a (SF L θ σ t z) (fun e => (NF L θ σ t z e : ℝ)) ≤ b) (e : E)
    (hNe : 0 < NF L θ σ t z e) :
    |Ysum L θ σ t z e / (NF L θ σ t z e : ℝ) - θ e|
      ≤ σ e * Real.sqrt (2 * (a + (NF L θ σ t z e : ℝ)) * b) / (NF L θ σ t z e : ℝ) := by
  have hN0 : (0 : ℝ) < (NF L θ σ t z e : ℝ) := by exact_mod_cast hNe
  have hsq := S_sq_le a ha (SF L θ σ t z) (fun e => (NF L θ σ t z e : ℝ))
    (fun _ => Nat.cast_nonneg _) b hQ e
  have hS : |SF L θ σ t z e| ≤ Real.sqrt (2 * (a + (NF L θ σ t z e : ℝ)) * b) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hsq
  have hdiff : Ysum L θ σ t z e / (NF L θ σ t z e : ℝ) - θ e
      = σ e * SF L θ σ t z e / (NF L θ σ t z e : ℝ) := by
    rw [Ysum_eq]
    field_simp
    ring
  rw [hdiff, abs_div, abs_mul, abs_of_pos (hσ e), abs_of_pos hN0]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hS (hσ e).le) hN0.le

#print axioms histF_obs
#print axioms Mval_snoc
#print axioms Mproc_integrable
#print axioms proc_step
#print axioms ville_process
#print axioms good_window_real
#print axioms Ysum_eq
#print axioms radius_of_good

end CIGAMF.P13.PaperA7Process
