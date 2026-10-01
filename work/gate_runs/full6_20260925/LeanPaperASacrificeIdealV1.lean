import «LeanPaperA7IdealFamilyV1»
import «LeanPaperASacrificeV1»

/-!
# Paper A: the sacrifice law is not vacuous, and the ideal learner attains its order

`sacrifice_cost_law` (`LeanPaperASacrificeV1`) quantifies over finite-horizon policies that are
`delta`-correct against the strict alternatives.  A theorem with unsatisfiable hypotheses says
nothing, so this module exhibits such a policy.  It is the ideal learner of
`LeanPaperA7IdealFamilyV1`, truncated at the Markov horizon, with its own answer event.  On that
one policy both sides hold:

    8 r M D(2 delta)  <=  N * sacrifice(wbar)  <=  N  <=  E tau_delta,

where `N` is the truncated run's expected number of real queries and `wbar` its average design
(`ideal_sacrifice`).  The upper end is the learner's expected stopping time, which is
`log(1/delta)/Gamma_true + o(log(1/delta))` (`ideal_family_finish`) with
`1/Gamma_true <= 128 (4 + 2 r M)/9` (`upper_constant`).  So the surrogate-value budget of the
rate-optimal learner is `Theta(r M log(1/delta))`, the same order as the lower bound that binds
every policy.
-/

namespace CIGAMF.P13.PaperASacrificeIdeal

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal
open CIGAMF.P13.PaperA7Stream CIGAMF.P13.PaperA7Process
open CIGAMF.P13.PaperA7IdealLearner CIGAMF.P13.PaperA7IdealStop CIGAMF.P13.PaperA7IdealSelect
open CIGAMF.P13.PaperA7IdealUpper CIGAMF.P13.PaperA7IdealStopped CIGAMF.P13.PaperA7DirectLower
open CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperALowerKL CIGAMF.P13.PaperALowerGame
open CIGAMF.P13.PaperABridge CIGAMF.P13.PaperABridgeDummy
open CIGAMF.P13.PaperAFamilyLower CIGAMF.P13.PaperAEndgame CIGAMF.P13.PaperAStrict
open CIGAMF.P13.PaperACentred CIGAMF.P13.PaperAGaussianKL CIGAMF.P13.PaperAActualDecisionBridge
open CIGAMF.P13.PaperARPair (Cell IsAlloc)
open CIGAMF.P13.PaperA7IdealFamily CIGAMF.P13.PaperASacrifice

variable {r : ℕ}

/-- **The ideal learner, truncated, satisfies the sacrifice law, and its budget is at most its
expected stopping time.** -/
theorem ideal_sacrifice [NeZero r] (M : ℝ) (hM : 0 < M) (hr : 0 < r) (a : ℝ) (ha : 0 < a)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : 2 * δ ≤ 1) (hD : 0 < demand (2 * δ))
    (hfin : (∫⁻ ω, (tauI (famSpec r M hM) a δ (thetaC r) ω).toENNReal ∂streamMeasure) ≠ ⊤) :
    ∃ n : ℕ,
      0 < ∑ e, expCnt M hM (detPol (stoppedLearner (famSpec r M hM) a δ ha)) n e
      ∧ 8 * (r : ℝ) * M * demand (2 * δ)
          ≤ (∑ e, expCnt M hM (detPol (stoppedLearner (famSpec r M hM) a δ ha)) n e)
            * sacrifice M (fun e => expCnt M hM (detPol (stoppedLearner (famSpec r M hM) a δ ha)) n e
                / ∑ e', expCnt M hM (detPol (stoppedLearner (famSpec r M hM) a δ ha)) n e')
      ∧ (∑ e, expCnt M hM (detPol (stoppedLearner (famSpec r M hM) a δ ha)) n e)
          ≤ (∫⁻ ω, (tauI (famSpec r M hM) a δ (thetaC r) ω).toENNReal ∂streamMeasure).toReal := by
  set P := famSpec r M hM with hP
  obtain ⟨n, hn⟩ := markov_horizon streamMeasure (tauI P a δ (thetaC r))
    (measurable_tauI P a δ ha (thetaC r)) hfin δ hδ
  set L := stoppedLearner P a δ ha with hL
  set S := ansEv P a δ true n with hSdef
  have hS : MeasurableSet S := measurableSet_ansEv P a δ ha true n
  have hbr : ∀ m : Cell r → ℝ, hist (famChan M hM) (detPol L) (lift m) n
      = streamMeasure.map (runS P a δ ha m n) :=
    fun m => (stream_eq_hist_fresh L (famS M) (famS_pos M hM) m n).symm
  have hreal : ∀ m : Cell r → ℝ, (hist (famChan M hM) (detPol L) (lift m) n).real S
      = streamMeasure.real {ω | runS P a δ ha m n ω ∈ S} := by
    intro m
    rw [hbr m, map_measureReal_apply (measurable_runS P a δ ha m n) hS]
    rfl
  have hθ : 1 - 2 * δ ≤ (hist (famChan M hM) (detPol L) (lift (thetaC r)) n).real S := by
    rw [hreal]
    have h := ansEv_true_ge P a δ ha hδ true (thetaC r) (fam_wrong r M hM) n
    have hc : ((Fintype.card Bool - 1 : ℕ) : ℝ) = 1 := by simp
    rw [hc, one_mul] at h
    linarith
  have hl : ∀ lam ∈ TrueAltStrict r,
      (hist (famChan M hM) (detPol L) (lift lam) n).real S ≤ 2 * δ := by
    intro lam hlam
    rw [hreal]
    have h := ansEv_alt_le P a δ ha hδ true lam hlam n
    have h2 : streamMeasure.real {ω | runS P a δ ha lam n ω ∈ S} ≤ δ := by
      rw [measureReal_def]
      exact le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top h)
        (le_of_eq (ENNReal.toReal_ofReal hδ.le))
    linarith
  obtain ⟨hNpos, -, hlaw⟩ :=
    sacrifice_cost_law M hM hr (detPol L) n S hS (2 * δ) (by positivity) hδ1 hθ hl hD
  refine ⟨n, hNpos, hlaw, ?_⟩
  -- the expected number of real queries is at most the expected stopping time
  have hfinC : ∀ e : Cell r,
      ∫⁻ ω, cntQ (Sum.inl e) n ω ∂hist (famChan M hM) (detPol L) (lift (thetaC r)) n ≠ ⊤ :=
    fun e => lintegral_cntQ_ne_top _ _ _ _ n
  show ∑ e, (∫⁻ ω, cntQ (Sum.inl e) n ω
      ∂hist (famChan M hM) (detPol L) (lift (thetaC r)) n).toReal ≤ _
  rw [← ENNReal.toReal_sum (fun e _ => hfinC e)]
  refine ENNReal.toReal_mono hfin ?_
  have hsum : ∑ e : Cell r,
      ∫⁻ ω, cntQ (Sum.inl e) n ω ∂hist (famChan M hM) (detPol L) (lift (thetaC r)) n
      = ∫⁻ ω, ∑ e : Cell r, cntQ (Sum.inl e) n ω
          ∂hist (famChan M hM) (detPol L) (lift (thetaC r)) n :=
    (lintegral_finsetSum _ fun e _ => measurable_cntQ _ n).symm
  rw [hsum, hbr, lintegral_map (Finset.measurable_sum _ fun e _ => measurable_cntQ _ n)
    (measurable_runS P a δ ha _ n)]
  exact lintegral_mono fun ω => cnt_le_tau P a δ ha (thetaC r) ω n

/-- **Satisfiability, stated plainly.**  For every small `delta` there is a finite-horizon
policy on the family that meets every hypothesis of `sacrifice_cost_law` at level `2 delta`. -/
theorem sacrifice_hypotheses_satisfiable [NeZero r] (M : ℝ) (hM : 0 < M) (hr : 0 < r)
    (δ : ℝ) (hδ : 0 < δ) (hδ16 : δ < 1 / 16) :
    ∃ (π : Policy (Cell r ⊕ Unit)) (n : ℕ) (S : Set (Hist (Cell r ⊕ Unit) n)),
      MeasurableSet S
      ∧ 1 - 2 * δ ≤ (hist (famChan M hM) π (lift (thetaC r)) n).real S
      ∧ (∀ lam ∈ TrueAltStrict r, (hist (famChan M hM) π (lift lam) n).real S ≤ 2 * δ)
      ∧ 0 < demand (2 * δ) := by
  set P := famSpec r M hM with hP
  have hfin := ideal_finite P 1 one_pos true (thetaC r) (fam_wrong r M hM) (fam_kf r M hM)
    (GamT_fam_pos M hM hr) δ hδ (by linarith)
  obtain ⟨n, hn⟩ := markov_horizon streamMeasure (tauI P 1 δ (thetaC r))
    (measurable_tauI P 1 δ one_pos (thetaC r)) hfin δ hδ
  set L := stoppedLearner P 1 δ one_pos with hL
  set S := ansEv P 1 δ true n with hSdef
  have hS : MeasurableSet S := measurableSet_ansEv P 1 δ one_pos true n
  have hbr : ∀ m : Cell r → ℝ, hist (famChan M hM) (detPol L) (lift m) n
      = streamMeasure.map (runS P 1 δ one_pos m n) :=
    fun m => (stream_eq_hist_fresh L (famS M) (famS_pos M hM) m n).symm
  have hreal : ∀ m : Cell r → ℝ, (hist (famChan M hM) (detPol L) (lift m) n).real S
      = streamMeasure.real {ω | runS P 1 δ one_pos m n ω ∈ S} := by
    intro m
    rw [hbr m, map_measureReal_apply (measurable_runS P 1 δ one_pos m n) hS]
    rfl
  refine ⟨detPol L, n, S, hS, ?_, fun lam hlam => ?_, ?_⟩
  · rw [hreal]
    have h := ansEv_true_ge P 1 δ one_pos hδ true (thetaC r) (fam_wrong r M hM) n
    have hc : ((Fintype.card Bool - 1 : ℕ) : ℝ) = 1 := by simp
    rw [hc, one_mul] at h
    linarith
  · rw [hreal]
    have h := ansEv_alt_le P 1 δ one_pos hδ true lam hlam n
    have h2 : streamMeasure.real {ω | runS P 1 δ one_pos lam n ω ∈ S} ≤ δ := by
      rw [measureReal_def]
      exact le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top h)
        (le_of_eq (ENNReal.toReal_ofReal hδ.le))
    linarith
  · exact hD_small δ hδ hδ16

#print axioms ideal_sacrifice
#print axioms sacrifice_hypotheses_satisfiable

end CIGAMF.P13.PaperASacrificeIdeal
