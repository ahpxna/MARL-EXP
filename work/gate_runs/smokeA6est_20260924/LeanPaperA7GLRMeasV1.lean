import «LeanPaperA7CorrectV1»

/-!
# Paper A7: the exact generalized-likelihood statistic is a measurable function of the run

The stopping statistic of the ideal learner is the EXACT infimum

    Z(N, mu_hat) = inf_{lambda in Alt} Qstat(a, sigma, N, mu_hat, lambda)

over an arbitrary (unbounded) alternative set.  An infimum over an uncountable set of
measurable functions need not be measurable in general; here each function is continuous in
`(N, mu_hat)`, so the infimum is upper semicontinuous: `{Z < c}` is the union over `lambda` of
the open sets `{Qstat(., ., lambda) < c}` (`sInf_lt_set_eq`), hence open, and `Z` is measurable
by `measurable_of_Iio` (`measurable_glr`).

To have continuity everywhere the statistic is written with `a + |N|` (`qAbs`); it equals the
code's `Qstat` whenever the counts are nonnegative (`qAbs_eq`), which they are along every run
(`glr_run_measurable`).
-/

namespace CIGAMF.P13.PaperA7GLRMeas

open MeasureTheory Topology Set
open CIGAMF.P13.PaperA7Stream CIGAMF.P13.PaperA7Process CIGAMF.P13.PaperA7Correct

variable {E : Type*} [Fintype E]

/-- The statistic with `a + |N|`, continuous everywhere. -/
noncomputable def qAbs (a : ℝ) (σ : E → ℝ) (x : (E → ℝ) × (E → ℝ)) (l : E → ℝ) : ℝ :=
  ∑ e, x.1 e ^ 2 * (x.2 e - l e) ^ 2 / (2 * (a + |x.1 e|) * σ e ^ 2)

theorem qAbs_eq (a : ℝ) (σ N μh l : E → ℝ) (hN : ∀ e, 0 ≤ N e) :
    qAbs a σ (N, μh) l = PaperA7Stream.Qstat a σ N μh l := by
  unfold qAbs PaperA7Stream.Qstat
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [abs_of_nonneg (hN e)]

theorem qAbs_nonneg (a : ℝ) (ha : 0 < a) (σ : E → ℝ) (x : (E → ℝ) × (E → ℝ)) (l : E → ℝ) :
    0 ≤ qAbs a σ x l := by
  unfold qAbs
  refine Finset.sum_nonneg fun e _ => div_nonneg (by positivity) ?_
  have := abs_nonneg (x.1 e)
  have := sq_nonneg (σ e)
  positivity

theorem continuous_qAbs (a : ℝ) (ha : 0 < a) (σ : E → ℝ) (hσ : ∀ e, σ e ≠ 0) (l : E → ℝ) :
    Continuous fun x : (E → ℝ) × (E → ℝ) => qAbs a σ x l := by
  unfold qAbs
  refine continuous_finset_sum _ fun e _ => ?_
  have h1 : Continuous fun x : (E → ℝ) × (E → ℝ) => x.1 e :=
    (continuous_apply e).comp continuous_fst
  have h2 : Continuous fun x : (E → ℝ) × (E → ℝ) => x.2 e :=
    (continuous_apply e).comp continuous_snd
  refine ((h1.pow 2).mul ((h2.sub continuous_const).pow 2)).div
    ((continuous_const.mul (continuous_const.add h1.abs)).mul continuous_const) fun x => ?_
  have : 0 < a + |x.1 e| := by have := abs_nonneg (x.1 e); linarith
  have hs : 0 < σ e ^ 2 := by have := hσ e; positivity
  positivity

/-- The exact statistic, as a function of `(N, mu_hat)`. -/
noncomputable def glr (a : ℝ) (σ : E → ℝ) (Alt : Set (E → ℝ)) (x : (E → ℝ) × (E → ℝ)) : ℝ :=
  sInf ((fun l => qAbs a σ x l) '' Alt)

theorem sInf_lt_set_eq (a : ℝ) (ha : 0 < a) (σ : E → ℝ) (Alt : Set (E → ℝ))
    (hne : Alt.Nonempty) (c : ℝ) :
    {x | glr a σ Alt x < c} = ⋃ l ∈ Alt, {x | qAbs a σ x l < c} := by
  ext x
  simp only [mem_setOf_eq, mem_iUnion, exists_prop]
  unfold glr
  rw [csInf_lt_iff ⟨0, ?_⟩ (hne.image _)]
  · constructor
    · rintro ⟨_, ⟨l, hl, rfl⟩, h⟩; exact ⟨l, hl, h⟩
    · rintro ⟨l, hl, h⟩; exact ⟨_, ⟨l, hl, rfl⟩, h⟩
  · rintro _ ⟨l, -, rfl⟩
    exact qAbs_nonneg a ha σ x l

/-- **The exact statistic is measurable.** -/
theorem measurable_glr (a : ℝ) (ha : 0 < a) (σ : E → ℝ) (hσ : ∀ e, σ e ≠ 0)
    (Alt : Set (E → ℝ)) (hne : Alt.Nonempty) : Measurable (glr a σ Alt) := by
  refine measurable_of_Iio fun c => ?_
  have hset : glr a σ Alt ⁻¹' Iio c = {x | glr a σ Alt x < c} := rfl
  rw [hset, sInf_lt_set_eq a ha σ Alt hne c]
  refine IsOpen.measurableSet ?_
  exact isOpen_biUnion fun l _ => isOpen_lt (continuous_qAbs a ha σ hσ l) continuous_const

variable [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E]

theorem measurable_muHat (L : Learner E) (θ σ : E → ℝ) (j : ℕ) (e : E) :
    Measurable fun ω => muHat L θ σ j ω e := by
  unfold muHat Ysum
  refine (Finset.measurable_sum _ fun i _ => ?_).div (measurable_Nc L θ σ j e)
  refine Measurable.ite ?_ ?_ measurable_const
  · exact (measurable_fst.comp ((measurable_pi_apply i).comp
      ((measurable_histF L θ σ j).comp (measurable_Xp j)))) (measurableSet_singleton e)
  · exact measurable_snd.comp ((measurable_pi_apply i).comp
      ((measurable_histF L θ σ j).comp (measurable_Xp j)))

/-- **The exact statistic along the run is measurable, and it is the code's infimum.** -/
theorem glr_run_measurable (L : Learner E) (θ σ : E → ℝ) (a : ℝ) (ha : 0 < a)
    (hσ : ∀ e, σ e ≠ 0) (Alt : Set (E → ℝ)) (hne : Alt.Nonempty) (j : ℕ) :
    Measurable (fun ω => glr a σ Alt (Nc L θ σ j ω, muHat L θ σ j ω)) ∧
    ∀ ω, glr a σ Alt (Nc L θ σ j ω, muHat L θ σ j ω)
      = sInf ((fun l => PaperA7Stream.Qstat a σ (Nc L θ σ j ω) (muHat L θ σ j ω) l) '' Alt) := by
  refine ⟨(measurable_glr a ha σ hσ Alt hne).comp
    ((measurable_pi_lambda _ fun e => measurable_Nc L θ σ j e).prodMk
      (measurable_pi_lambda _ fun e => measurable_muHat L θ σ j e)), fun ω => ?_⟩
  unfold glr
  congr 1
  refine Set.image_congr fun l _ => ?_
  exact qAbs_eq a σ _ _ l fun e => Nat.cast_nonneg _

#print axioms continuous_qAbs
#print axioms measurable_glr
#print axioms glr_run_measurable

end CIGAMF.P13.PaperA7GLRMeas
