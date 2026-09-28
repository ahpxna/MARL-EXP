import «LeanPaperA7ProcessV1»

/-!
# Paper A7: the generalized-likelihood stop is delta-correct, for every learner

The stopping rule stops with answer `T` at time `j` when a statistic `Z_T(j)` exceeds the
code's threshold `bthr(a, delta, N_j)`, where `Z_T(j)` is at most the code's ridge statistic
`Qstat(a, sigma, N_j, mu_hat_j, lambda)` at EVERY `lambda` in the alternative `Alt_T`
(soundness of the certified lower value; the exact infimum is one such statistic,
`sInf_le_truth`).

If the true world is in `Alt_T`, i.e. `T` is wrong, then stopping with `T` forces
`bthr < Qstat(mu_hat, theta)`, and that statistic at the TRUE world is the standardised
`Qstat(S, N)` of Ville's inequality (`qstat_truth_eq`, through `Ysum_eq`).  Hence
(`wrong_stop_le`, `wrong_stop_ever_le`): the probability of ever stopping with a wrong answer
is at most `delta`, for every measurable learner, on the actual observation law.
-/

namespace CIGAMF.P13.PaperA7Correct

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open CIGAMF.P13.PaperA7Stream CIGAMF.P13.PaperA7Process CIGAMF.P13.PaperA7Confidence

variable {E : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace E]
  [MeasurableSingletonClass E]

variable (L : Learner E) (θ σ : E → ℝ)

/-- The raw mean along the run. -/
noncomputable def muHat (j : ℕ) (ω : ℕ → ℝ) (e : E) : ℝ :=
  Ysum L θ σ j (Xp j ω) e / Nc L θ σ j ω e

/-- **The code's statistic at the true world is Ville's standardised statistic.** -/
theorem qstat_truth_eq (a : ℝ) (hσ : ∀ e, 0 < σ e) (j : ℕ) (ω : ℕ → ℝ) :
    PaperA7Stream.Qstat a σ (Nc L θ σ j ω) (muHat L θ σ j ω) θ
      = PaperA7Confidence.Qstat a (Sc L θ σ j ω) (Nc L θ σ j ω) := by
  unfold PaperA7Stream.Qstat PaperA7Confidence.Qstat
  refine Finset.sum_congr rfl fun e _ => ?_
  have hσe := (hσ e).ne'
  unfold muHat Nc Sc
  rw [Ysum_eq]
  by_cases hN : (NF L θ σ j (Xp j ω) e : ℝ) = 0
  · -- no sample of this cell: both terms vanish
    have hN' : NF L θ σ j (Xp j ω) e = 0 := by exact_mod_cast hN
    have hno : ∀ i, (histF L θ σ j (Xp j ω) i).1 ≠ e := by
      intro i hi
      have h1 : 1 ≤ NF L θ σ j (Xp j ω) e := by
        unfold NF
        calc 1 = (if (histF L θ σ j (Xp j ω) i).1 = e then 1 else 0) := by rw [if_pos hi]
          _ ≤ ∑ i' : Fin j, (if (histF L θ σ j (Xp j ω) i').1 = e then 1 else 0) :=
            Finset.single_le_sum (f := fun i' : Fin j =>
              if (histF L θ σ j (Xp j ω) i').1 = e then 1 else 0)
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    have hS : SF L θ σ j (Xp j ω) e = 0 := by
      unfold SF
      exact Finset.sum_eq_zero fun i _ => if_neg (hno i)
    rw [hN, hS]
    simp
  · field_simp
    ring

/-- The exact infimum over the alternative is a sound statistic at a true world inside it. -/
theorem sInf_le_truth (a : ℝ) (ha : 0 < a) (Alt : Set (E → ℝ)) (hθ : θ ∈ Alt)
    (N μh : E → ℝ) (hN : ∀ e, 0 ≤ N e) :
    sInf ((fun l => PaperA7Stream.Qstat a σ N μh l) '' Alt)
      ≤ PaperA7Stream.Qstat a σ N μh θ := by
  refine csInf_le ⟨0, ?_⟩ ⟨θ, hθ, rfl⟩
  rintro _ ⟨l, -, rfl⟩
  unfold PaperA7Stream.Qstat
  refine Finset.sum_nonneg fun e _ => div_nonneg (by positivity) ?_
  have := hN e
  have : 0 ≤ σ e ^ 2 := sq_nonneg _
  positivity

/-- **A wrong stop by time `T` has probability at most `delta`.** -/
theorem wrong_stop_le (a δ : ℝ) (ha : 0 < a) (hδ : 0 < δ) (hσ : ∀ e, 0 < σ e) (T : ℕ)
    (Z : ℕ → (ℕ → ℝ) → ℝ)
    (hZ : ∀ j ω, Z j ω ≤ PaperA7Stream.Qstat a σ (Nc L θ σ j ω) (muHat L θ σ j ω) θ) :
    streamMeasure {ω | ∃ j ≤ T, bthr a δ (Nc L θ σ j ω) < Z j ω} ≤ ENNReal.ofReal δ := by
  have hv := ville_process L θ σ a δ ha hδ T
  have hsub : {ω | ∃ j ≤ T, bthr a δ (Nc L θ σ j ω) < Z j ω}
      ⊆ {ω | ∃ j ≤ T, bthr a δ (Nc L θ σ j ω)
          < PaperA7Confidence.Qstat a (Sc L θ σ j ω) (Nc L θ σ j ω)} := by
    rintro ω ⟨j, hj, hZj⟩
    refine ⟨j, hj, lt_of_lt_of_le hZj ?_⟩
    rw [← qstat_truth_eq L θ σ a hσ j ω]
    exact hZ j ω
  refine le_trans (measure_mono hsub) ?_
  rw [← ENNReal.ofReal_toReal (measure_ne_top streamMeasure _)]
  exact ENNReal.ofReal_le_ofReal hv

/-- **A wrong stop at any time has probability at most `delta`.** -/
theorem wrong_stop_ever_le (a δ : ℝ) (ha : 0 < a) (hδ : 0 < δ) (hσ : ∀ e, 0 < σ e)
    (Z : ℕ → (ℕ → ℝ) → ℝ)
    (hZ : ∀ j ω, Z j ω ≤ PaperA7Stream.Qstat a σ (Nc L θ σ j ω) (muHat L θ σ j ω) θ) :
    streamMeasure {ω | ∃ j, bthr a δ (Nc L θ σ j ω) < Z j ω} ≤ ENNReal.ofReal δ := by
  have hU : {ω | ∃ j, bthr a δ (Nc L θ σ j ω) < Z j ω}
      = ⋃ T, {ω | ∃ j ≤ T, bthr a δ (Nc L θ σ j ω) < Z j ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨j, hj⟩; exact ⟨j, j, le_rfl, hj⟩
    · rintro ⟨T, j, -, hj⟩; exact ⟨j, hj⟩
  have hmono : Monotone fun T => {ω | ∃ j ≤ T, bthr a δ (Nc L θ σ j ω) < Z j ω} := by
    intro T T' hTT' ω ⟨j, hj, hZj⟩
    exact ⟨j, le_trans hj hTT', hZj⟩
  rw [hU, hmono.measure_iUnion]
  exact iSup_le fun T => wrong_stop_le L θ σ a δ ha hδ hσ T Z hZ

#print axioms qstat_truth_eq
#print axioms sInf_le_truth
#print axioms wrong_stop_le
#print axioms wrong_stop_ever_le

end CIGAMF.P13.PaperA7Correct
