import «LeanPaperA6SurrogateAtV1»
import «LeanPaperA6BadRoundsV1»
import «LeanPaperA6SurrogateCostV1»

/-!
# Paper A6: the learner that RE-SOLVES the surrogate at its estimate costs `log^2(1/delta)`

On the separating family, run the tracking learner `oLearner O` (warm start, forcing
`1/sqrt(s+1)`, first maximiser of `W - N`) whose oracle `O` is ANY measurable allocation rule of
the estimate that puts no weight on the middle cells once the estimate is within `1/16` of the
truth, and stop with the GLR stop of the true alternatives (`tauG`).  Two oracles qualify:

* `surOracle r` -- the frozen surrogate re-solved at the estimate (`surD_middle_zero`);
* every oracle that returns an exact optimum of the surrogate re-solved at the estimate whenever
  the estimate's extrema are the anchors (`optimal_oracle_middle_zero`).

Then `E tau_delta >= (K M / 8)^2 log(1/delta)^2` for every `delta < delta_0`
(`est_cost_log_sq`, `surrogate_learner_cost`, `exact_oracle_cost`), and the ratio to the ideal
learner is unbounded (`surrogate_learner_vs_ideal`).

The mechanism is that of `LeanPaperA6SurrogateCostV1`, with one more term.  A middle pair is
queried only by forcing, or in a round where the estimate is off by `1/16` or more
(`oCount_le_amgm`, `badT_le_badAll`), and the expected number of such rounds is at most
`s0 + 2` at every horizon (`badAll_expect`, from Ville at the learner's own statistic).  So
`E[N_pair] <= 4 + 2(s0 + 2) + 2(E tau/s + s)/K`, and the stopped change of measure at the hidden
pair forces `sqrt(E tau) >~ log(1/delta)`.

No oracle information: the oracle sees only the estimate.  The true world enters only as the
law of the observations and, in the analysis, as the centre of the `1/16` ball.
-/

namespace CIGAMF.P13.PaperA6EstCost

open Finset MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal
open CIGAMF.P13.PaperA7Stream CIGAMF.P13.PaperA7Process
open CIGAMF.P13.PaperA7IdealLearner CIGAMF.P13.PaperA7IdealStop CIGAMF.P13.PaperA7IdealStopped
open CIGAMF.P13.PaperA7StoppedGen CIGAMF.P13.PaperA7IdealFamily CIGAMF.P13.PaperA7IdealUpper
open CIGAMF.P13.PaperA7IdealSelect
open CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperALowerKL
open CIGAMF.P13.PaperABridge CIGAMF.P13.PaperABridgeDummy CIGAMF.P13.PaperAFamilyLower
open CIGAMF.P13.PaperAEndgame CIGAMF.P13.PaperAStrict CIGAMF.P13.PaperACentred
open CIGAMF.P13.PaperA6OracleLearner CIGAMF.P13.PaperA6BadRounds CIGAMF.P13.PaperA6SurrogateAt
open CIGAMF.P13.PaperA6SurrogateCost (pairCells card_pairCells pairAlt pairAlt_alt sum_klq_eq
  D_ge_half)
open CIGAMF.P13.PaperARPair (Cell pairVar)

variable {r : ℕ}

/-- The oracle ignores the middles once the estimate is within `1/16` of the truth. -/
def IgnoresMiddlesNear (O : Oracle (Cell r)) : Prop :=
  ∀ μ : Cell r → ℝ, (∀ e, |μ e - thetaC r e| < 1 / 16) → ∀ p : Fin r × Bool, O.D μ (Sum.inr p) = 0

/-- The noise bound on the family. -/
noncomputable def σ2 (M : ℝ) : ℝ := max 1 M

theorem famσ_sq_le [NeZero r] (M : ℝ) (hM : 0 < M) (e : Cell r) :
    (famSpec r M hM).σ e ^ 2 ≤ σ2 M := by
  show Real.sqrt (pairVar M e) ^ 2 ≤ max 1 M
  rw [Real.sq_sqrt (pairVarC_pos M hM e).le]
  cases e with
  | inl _ => exact le_max_left _ _
  | inr _ => exact le_max_right _ _

theorem badT_le_badAll [NeZero r] (M : ℝ) (hM : 0 < M) (O : Oracle (Cell r))
    (hO : IgnoresMiddlesNear O) (ω : ℕ → ℝ) (t : ℕ) (p : Fin r × Bool) :
    badT O (thetaC r) (famSpec r M hM).σ ω t (Sum.inr p)
      ≤ badAll O (thetaC r) (famSpec r M hM).σ (1 / 16) ω t := by
  classical
  unfold badT badAll
  refine sum_le_sum fun s _ => ?_
  by_cases h : Fintype.card (Cell r) ≤ s ∧
      O.D (hMu (oRun O (thetaC r) (famSpec r M hM).σ s ω)) (Sum.inr p) ≠ 0
  · rw [if_pos h, if_pos ⟨h.1, fun hc => h.2 (hO _ hc p)⟩]
  · rw [if_neg h]; split_ifs <;> norm_num

/-! ## 1. At one level -/

/-- **At one level**, for the estimate-driven learner: with `B = s0 + 4`,
`(1 - 2delta) log(1/(2delta)) - log 2 <= (1/M)(B + s/K + I/(K s))`. -/
theorem est_lower_at [NeZero r] (M : ℝ) (hM : 0 < M) (a : ℝ) (ha : 0 < a) (O : Oracle (Cell r))
    (hO : IgnoresMiddlesNear O) (s₀ : ℕ) (hs₀K : Fintype.card (Cell r) ≤ s₀) (hs₀1 : 1 ≤ s₀)
    (hs₀ : ∀ s : ℕ, s₀ ≤ s → ∀ N : ℝ,
      Real.sqrt (s : ℝ) / Fintype.card (Cell r) - ((Fintype.card (Cell r) : ℝ) - 1) ≤ N →
        1 ≤ N ∧ σ2 M * (2 * (a + N) * bS (Fintype.card (Cell r)) a s) < (1 / 16) ^ 2 * N ^ 2)
    (j : Fin r) (δ : ℝ) (hδ : 0 < δ) (hδ1 : 2 * δ ≤ 1) (s : ℝ) (hs : 0 < s)
    (hfin : ∫⁻ ω, (tauG (famSpec r M hM) a δ (oLearner O) (thetaC r) ω).toENNReal
      ∂streamMeasure ≠ ⊤) :
    (1 - 2 * δ) * Real.log (1 / (2 * δ)) - Real.log 2
      ≤ (1 / M) * ((s₀ : ℝ) + 4 + s / (Fintype.card (Cell r) : ℝ)
        + (∫⁻ ω, (tauG (famSpec r M hM) a δ (oLearner O) (thetaC r) ω).toENNReal
            ∂streamMeasure).toReal / ((Fintype.card (Cell r) : ℝ) * s)) := by
  set P := famSpec r M hM with hP
  set L := oLearner O with hL
  set K : ℝ := (Fintype.card (Cell r) : ℝ) with hK
  have hK0 : 0 < K := by rw [hK]; exact_mod_cast Fintype.card_pos
  set I := ∫⁻ ω, (tauG P a δ L (thetaC r) ω).toENNReal ∂streamMeasure with hI
  obtain ⟨n, hn⟩ := markov_horizon streamMeasure (tauG P a δ L (thetaC r))
    (measurable_tauG P a δ L ha (thetaC r)) hfin δ hδ
  set Lst := stoppedG P a δ L ha with hLst
  set S := ansEv P a δ true n with hSdef
  have hS : MeasurableSet S := measurableSet_ansEv P a δ ha true n
  have hbr : ∀ m : Cell r → ℝ, hist (famChan M hM) (detPol Lst) (lift m) n
      = streamMeasure.map (runSG P a δ L ha m n) :=
    fun m => (stream_eq_hist_fresh Lst (famS M) (famS_pos M hM) m n).symm
  have hreal : ∀ m : Cell r → ℝ, (hist (famChan M hM) (detPol Lst) (lift m) n).real S
      = streamMeasure.real {ω | runSG P a δ L ha m n ω ∈ S} := by
    intro m
    rw [hbr m, map_measureReal_apply (measurable_runSG P a δ L ha m n) hS]
    rfl
  have hθ : 1 - 2 * δ ≤ (hist (famChan M hM) (detPol Lst) (lift (thetaC r)) n).real S := by
    rw [hreal]
    have h := ansEv_true_geG P a δ L ha hδ true (thetaC r) (fam_wrong r M hM) n
    have hc : ((Fintype.card Bool - 1 : ℕ) : ℝ) = 1 := by simp
    rw [hc, one_mul] at h
    linarith
  have hl : (hist (famChan M hM) (detPol Lst) (lift (pairAlt j)) n).real S ≤ 2 * δ := by
    rw [hreal]
    have h := ansEv_alt_leG P a δ L ha hδ true (pairAlt j) (pairAlt_alt j) n
    have h2 : streamMeasure.real {ω | runSG P a δ L ha (pairAlt j) n ω ∈ S} ≤ δ := by
      rw [measureReal_def]
      exact le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top h)
        (le_of_eq (ENNReal.toReal_ofReal hδ.le))
    linarith
  have hcm := change_of_measure (famChan M hM) (detPol Lst) (lift (thetaC r)) (lift (pairAlt j))
    n S hS (2 * δ) (by positivity) hδ1 hθ hl
  rw [Fintype.sum_sum_type] at hcm
  have hdum : ∑ u : Unit, (∫⁻ ω, cntQ (Sum.inr u) n ω
      ∂hist (famChan M hM) (detPol Lst) (lift (thetaC r)) n)
      * klq (famChan M hM) (lift (thetaC r)) (lift (pairAlt j)) (Sum.inr u) = 0 := by
    refine Finset.sum_eq_zero fun u _ => ?_
    have : (Sum.inr u : Cell r ⊕ Unit) = (famChan (r := r) M hM).dummy := rfl
    rw [this, klq_dummy, mul_zero]
  rw [hdum, add_zero, sum_klq_eq M hM j] at hcm
  have hsum : ∑ e ∈ pairCells j,
      ∫⁻ ω, cntQ (Sum.inl e) n ω ∂hist (famChan M hM) (detPol Lst) (lift (thetaC r)) n
      = ∫⁻ ω, ∑ e ∈ pairCells j, cntQ (Sum.inl e) n (runSG P a δ L ha (thetaC r) n ω)
          ∂streamMeasure := by
    rw [← lintegral_finset_sum _ fun e _ => measurable_cntQ _ n, hbr,
      lintegral_map (Finset.measurable_sum _ fun e _ => measurable_cntQ _ n)
        (measurable_runSG P a δ L ha _ n)]
  rw [hsum] at hcm
  have hc0 : (0 : ℝ) ≤ 4 + 2 * s / K := by positivity
  have hd0 : (0 : ℝ) ≤ 2 / (K * s) := by positivity
  -- pathwise: forcing, plus the rounds with a bad estimate
  set X : (ℕ → ℝ) → ℝ := fun ω => badAll O (thetaC r) P.σ (1 / 16) ω n with hX
  have hX0 : ∀ ω, 0 ≤ X ω := fun ω => badAll_nonneg O _ _ _ ω n
  have hpath : ∀ ω, ∑ e ∈ pairCells j, cntQ (Sum.inl e) n (runSG P a δ L ha (thetaC r) n ω)
      ≤ (ENNReal.ofReal (4 + 2 * s / K)
        + ENNReal.ofReal (2 / (K * s)) * (tauG P a δ L (thetaC r) ω).toENNReal)
        + ENNReal.ofReal (2 * X ω) := by
    intro ω
    obtain ⟨m, hmn, hmτ, -, hcnt⟩ := cnt_eq_at_min P a δ L ha (thetaC r) ω n
    have hstep : ∀ e ∈ pairCells j, cntQ (Sum.inl e) n (runSG P a δ L ha (thetaC r) n ω)
        ≤ ENNReal.ofReal (2 + X ω + ((m : ℝ) / s + s) / K) := by
      intro e he
      rw [hcnt e]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := oCount_le_amgm O (thetaC r) P.σ ω e m s hs
      have h2 : badT O (thetaC r) P.σ ω m e ≤ X ω := by
        unfold pairCells at he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        have hb : ∀ p : Fin r × Bool, e = Sum.inr p →
            badT O (thetaC r) P.σ ω m e ≤ X ω := by
          rintro p rfl
          exact (badT_le_badAll M hM O hO ω m p).trans (badAll_mono O _ _ _ ω hmn)
        rcases he with rfl | rfl
        · exact hb _ rfl
        · exact hb _ rfl
      linarith
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [Finset.sum_const, card_pairCells, nsmul_eq_mul]
    have hmE : (m : ℝ≥0∞) ≤ (tauG P a δ L (thetaC r) ω).toENNReal := by
      have h := ENat.toENNReal_le.mpr hmτ
      rwa [ENat.toENNReal_coe] at h
    have hsplit : ((2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (2 + X ω + ((m : ℝ) / s + s) / K)
        = (ENNReal.ofReal (4 + 2 * s / K) + ENNReal.ofReal (2 / (K * s)) * (m : ℝ≥0∞))
          + ENNReal.ofReal (2 * X ω) := by
      rw [← ENNReal.ofReal_natCast m, ← ENNReal.ofReal_mul hd0,
        ← ENNReal.ofReal_add hc0 (mul_nonneg hd0 (Nat.cast_nonneg m)),
        ← ENNReal.ofReal_add (by positivity) (by linarith [hX0 ω]),
        ← ENNReal.ofReal_natCast 2, ← ENNReal.ofReal_mul (Nat.cast_nonneg 2)]
      congr 1
      push_cast
      field_simp
      ring
    rw [hsplit]
    gcongr
  have hτE : Measurable fun ω => (tauG P a δ L (thetaC r) ω).toENNReal :=
    (Measurable.of_discrete (f := ENat.toENNReal)).comp (measurable_tauG P a δ L ha (thetaC r))
  have hbad := badAll_expect O a ha (thetaC r) P.σ P.σ_pos (σ2 M) (famσ_sq_le M hM) (1 / 16)
    (by norm_num) s₀ hs₀K hs₀1 hs₀ n
  have hint : ∫⁻ ω, ∑ e ∈ pairCells j, cntQ (Sum.inl e) n (runSG P a δ L ha (thetaC r) n ω)
      ∂streamMeasure
      ≤ (ENNReal.ofReal (4 + 2 * s / K) + ENNReal.ofReal (2 / (K * s)) * I)
        + ENNReal.ofReal (2 * ((s₀ : ℝ) + 2)) := by
    refine le_trans (lintegral_mono hpath) ?_
    have hmeasA : Measurable fun ω => ENNReal.ofReal (4 + 2 * s / K)
        + ENNReal.ofReal (2 / (K * s)) * (tauG P a δ L (thetaC r) ω).toENNReal :=
      (hτE.const_mul _).const_add _
    rw [lintegral_add_left hmeasA]
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    gcongr
    have heq : ∀ ω, ENNReal.ofReal (2 * X ω) = ENNReal.ofReal 2 * ENNReal.ofReal (X ω) :=
      fun ω => ENNReal.ofReal_mul (by norm_num)
    simp_rw [heq]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul (by norm_num)]
    gcongr
  have hk0 : (0 : ℝ) ≤ 1 / (2 * M) := by positivity
  have hx0 : (0 : ℝ) ≤ I.toReal := ENNReal.toReal_nonneg
  have hb0 : (0 : ℝ) ≤ 2 * ((s₀ : ℝ) + 2) := by positivity
  have heqE : ENNReal.ofReal (1 / (2 * M) * ((4 + 2 * s / K + 2 / (K * s) * I.toReal)
        + 2 * ((s₀ : ℝ) + 2)))
      = ENNReal.ofReal (1 / (2 * M))
        * ((ENNReal.ofReal (4 + 2 * s / K) + ENNReal.ofReal (2 / (K * s)) * I)
          + ENNReal.ofReal (2 * ((s₀ : ℝ) + 2))) := by
    rw [ENNReal.ofReal_mul hk0, ENNReal.ofReal_add (add_nonneg hc0 (mul_nonneg hd0 hx0)) hb0,
      ENNReal.ofReal_add hc0 (mul_nonneg hd0 hx0), ENNReal.ofReal_mul hd0,
      ENNReal.ofReal_toReal hfin]
  have hchain : ENNReal.ofReal ((1 - 2 * δ) * Real.log (1 / (2 * δ)) - Real.log 2)
      ≤ ENNReal.ofReal (1 / (2 * M) * ((4 + 2 * s / K + 2 / (K * s) * I.toReal)
        + 2 * ((s₀ : ℝ) + 2))) :=
    le_trans hcm (le_trans (mul_le_mul_right hint _) heqE.symm.le)
  have hreal' := (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg hk0 (add_nonneg (add_nonneg hc0 (mul_nonneg hd0 hx0)) hb0))).mp hchain
  have hid : 1 / (2 * M) * ((4 + 2 * s / K + 2 / (K * s) * I.toReal) + 2 * ((s₀ : ℝ) + 2))
      = 1 / M * ((s₀ : ℝ) + 4 + s / K + I.toReal / (K * s)) := by
    field_simp
    ring
  linarith

/-! ## 2. The square of the logarithm -/

/-- **`E tau >= (KM/8)^2 log(1/delta)^2`** for the learner driven by any oracle that ignores the
middles near the truth. -/
theorem est_cost_log_sq [NeZero r] (M : ℝ) (hM : 0 < M) (a : ℝ) (ha : 0 < a)
    (O : Oracle (Cell r)) (hO : IgnoresMiddlesNear O) :
    ∃ c > 0, ∃ δ₀ > 0, ∀ δ, 0 < δ → δ < δ₀ →
      ENNReal.ofReal (c * Real.log (1 / δ) ^ 2)
        ≤ ∫⁻ ω, (tauG (famSpec r M hM) a δ (oLearner O) (thetaC r) ω).toENNReal
            ∂streamMeasure := by
  have hK1 : 1 ≤ Fintype.card (Cell r) := Fintype.card_pos
  have hσ2 : 0 < σ2 M := lt_of_lt_of_le one_pos (le_max_left _ _)
  obtain ⟨s₀, hs₀K, hs₀1, hs₀⟩ := radius_eventually (Fintype.card (Cell r)) hK1 a (σ2 M) (1 / 16)
    ha hσ2 (by norm_num)
  have hK0 : (0 : ℝ) < (Fintype.card (Cell r) : ℝ) := by exact_mod_cast Fintype.card_pos
  set B : ℝ := (s₀ : ℝ) + 4 with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨((Fintype.card (Cell r) : ℝ) * M / 8) ^ 2, by positivity,
    min (1 / 32) (Real.exp (-(4 * ((Fintype.card (Cell r) : ℝ) * B + 1)
      / ((Fintype.card (Cell r) : ℝ) * M)))), by positivity, fun δ hδ hδ0 => ?_⟩
  set K : ℝ := (Fintype.card (Cell r) : ℝ) with hK
  have hδ32 : δ ≤ 1 / 32 := le_trans hδ0.le (min_le_left _ _)
  have hδe : δ < Real.exp (-(4 * (K * B + 1) / (K * M))) :=
    lt_of_lt_of_le hδ0 (min_le_right _ _)
  by_cases hfin : ∫⁻ ω, (tauG (famSpec r M hM) a δ (oLearner O) (thetaC r) ω).toENNReal
      ∂streamMeasure = ⊤
  · rw [hfin]; exact le_top
  have hD := D_ge_half δ hδ hδ32
  have hℓ0 : 4 * (K * B + 1) / (K * M) < Real.log (1 / δ) := by
    rw [one_div, Real.log_inv]
    have := Real.log_lt_log hδ hδe
    rw [Real.log_exp] at this
    linarith
  set I := (∫⁻ ω, (tauG (famSpec r M hM) a δ (oLearner O) (thetaC r) ω).toENNReal
      ∂streamMeasure).toReal with hI
  have hI0 : 0 ≤ I := ENNReal.toReal_nonneg
  set q := Real.sqrt I with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqq : q * q = I := Real.mul_self_sqrt hI0
  have hq1 : 0 < q + 1 := by linarith
  have hbound := est_lower_at M hM a ha O hO s₀ hs₀K hs₀1 hs₀ ⟨0, Nat.pos_of_ne_zero (NeZero.ne r)⟩
    δ hδ (by linarith) (q + 1) hq1 hfin
  rw [← hI, ← hK, ← hB] at hbound
  have hq1' := hq1.ne'
  have hK0' := hK0.ne'
  have hM' := hM.ne'
  have hfrac : I / (q + 1) ≤ q := by
    rw [div_le_iff₀ hq1, ← hqq]
    nlinarith
  have hBq : 1 / M * (B + (q + 1) / K + I / (K * (q + 1)))
      = (K * B + (q + 1) + I / (q + 1)) / (K * M) := by
    field_simp
    try ring
  rw [hBq, le_div_iff₀ (by positivity)] at hbound
  have hKM : 0 < K * M := by positivity
  have h2 : Real.log (1 / δ) / 2 * (K * M) ≤ K * B + 2 * q + 1 := by
    have := mul_le_mul_of_nonneg_right hD hKM.le
    linarith
  have h3 : 4 * (K * B + 1) < Real.log (1 / δ) * (K * M) := by
    rwa [div_lt_iff₀ hKM] at hℓ0
  have hqge : K * M * Real.log (1 / δ) / 8 ≤ q := by linarith
  have hℓpos : 0 ≤ Real.log (1 / δ) := by
    have : 0 < 4 * (K * B + 1) / (K * M) := by positivity
    linarith
  have h0 : 0 ≤ K * M * Real.log (1 / δ) / 8 := by positivity
  have hsq : (K * M / 8) ^ 2 * Real.log (1 / δ) ^ 2 ≤ I := by
    rw [← hqq]
    calc (K * M / 8) ^ 2 * Real.log (1 / δ) ^ 2
        = (K * M * Real.log (1 / δ) / 8) * (K * M * Real.log (1 / δ) / 8) := by ring
      _ ≤ q * q := mul_le_mul hqge hqge h0 hq0
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal hsq

/-! ## 3. The two oracles, and the comparison with the ideal learner -/

/-- **The frozen surrogate re-solved at the estimate costs `Omega(log^2(1/delta))`.** -/
theorem surrogate_learner_cost [NeZero r] (M : ℝ) (hM : 0 < M) (a : ℝ) (ha : 0 < a) :
    ∃ c > 0, ∃ δ₀ > 0, ∀ δ, 0 < δ → δ < δ₀ →
      ENNReal.ofReal (c * Real.log (1 / δ) ^ 2)
        ≤ ∫⁻ ω, (tauG (famSpec r M hM) a δ (oLearner (surOracle r)) (thetaC r) ω).toENNReal
            ∂streamMeasure :=
  est_cost_log_sq M hM a ha (surOracle r) fun μ hμ p => surD_middle_zero μ hμ p

/-- **Every oracle that returns an exact optimum of the surrogate re-solved at the estimate
(where the estimate's extrema are the anchors) costs `Omega(log^2(1/delta))`.** -/
theorem exact_oracle_cost [NeZero r] (M : ℝ) (hM : 0 < M) (a : ℝ) (ha : 0 < a)
    (O : Oracle (Cell r))
    (hopt : ∀ μ, AnchorsExtreme μ ∧ 0 < margin μ → frozenAt M μ (O.D μ) = frozenGameAt r M μ) :
    ∃ c > 0, ∃ δ₀ > 0, ∀ δ, 0 < δ → δ < δ₀ →
      ENNReal.ofReal (c * Real.log (1 / δ) ^ 2)
        ≤ ∫⁻ ω, (tauG (famSpec r M hM) a δ (oLearner O) (thetaC r) ω).toENNReal
            ∂streamMeasure :=
  est_cost_log_sq M hM a ha O fun μ hμ p => optimal_oracle_middle_zero M hM O hopt μ hμ p

/-- **Against the ideal learner, the ratio is unbounded.** -/
theorem surrogate_learner_vs_ideal [NeZero r] (M : ℝ) (hM : 0 < M) (hr : 0 < r) (a : ℝ)
    (ha : 0 < a) (B : ℝ) (hB : 0 < B) :
    ∃ δ₀ > 0, ∀ δ, 0 < δ → δ < δ₀ →
      ENNReal.ofReal (B * (∫⁻ ω, (tauI (famSpec r M hM) a δ (thetaC r) ω).toENNReal
          ∂streamMeasure).toReal)
        ≤ ∫⁻ ω, (tauG (famSpec r M hM) a δ (oLearner (surOracle r)) (thetaC r) ω).toENNReal
            ∂streamMeasure := by
  obtain ⟨c, hc, δ₁, hδ₁, hlow⟩ := surrogate_learner_cost (r := r) M hM a ha
  have hΓ := GamT_fam_pos M hM hr
  obtain ⟨δ₂, hδ₂, hup⟩ := ideal_upper_rate (famSpec r M hM) a ha true (thetaC r)
    (fam_wrong r M hM) (fam_kf r M hM) hΓ 1 one_pos
  have hC0 : 0 < B * (1 / GamT (famSpec r M hM) true (thetaC r) + 1) / c := by positivity
  refine ⟨min (min δ₁ δ₂) (min 1 (Real.exp (-(B * (1 / GamT (famSpec r M hM) true (thetaC r) + 1)
    / c)))), by positivity, fun δ hδ hδ0 => ?_⟩
  have hδa : δ < δ₁ := lt_of_lt_of_le hδ0 (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδb : δ < δ₂ := lt_of_lt_of_le hδ0 (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδ1 : δ < 1 := lt_of_lt_of_le hδ0 (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδc : δ < Real.exp (-(B * (1 / GamT (famSpec r M hM) true (thetaC r) + 1) / c)) :=
    lt_of_lt_of_le hδ0 (le_trans (min_le_right _ _) (min_le_right _ _))
  have hℓC : B * (1 / GamT (famSpec r M hM) true (thetaC r) + 1) / c < Real.log (1 / δ) := by
    have hlog : Real.log (1 / δ) = -Real.log δ := by rw [one_div, Real.log_inv]
    rw [hlog]
    have := Real.log_lt_log hδ hδc
    rw [Real.log_exp] at this
    linarith
  have hℓ0 : 0 < Real.log (1 / δ) := lt_trans hC0 hℓC
  have hid := hup δ hδ (lt_min hδb hδ1)
  beta_reduce at hid
  rw [div_le_iff₀ hℓ0] at hid
  refine le_trans ?_ (hlow δ hδ hδa)
  apply ENNReal.ofReal_le_ofReal
  have hcl : B * (1 / GamT (famSpec r M hM) true (thetaC r) + 1) ≤ c * Real.log (1 / δ) := by
    rw [div_lt_iff₀ hc] at hℓC; linarith
  calc B * (∫⁻ ω, (tauI (famSpec r M hM) a δ (thetaC r) ω).toENNReal ∂streamMeasure).toReal
      ≤ B * ((1 / GamT (famSpec r M hM) true (thetaC r) + 1) * Real.log (1 / δ)) :=
        mul_le_mul_of_nonneg_left hid hB.le
    _ = B * (1 / GamT (famSpec r M hM) true (thetaC r) + 1) * Real.log (1 / δ) := by ring
    _ ≤ c * Real.log (1 / δ) * Real.log (1 / δ) := mul_le_mul_of_nonneg_right hcl hℓ0.le
    _ = c * Real.log (1 / δ) ^ 2 := by ring

#print axioms est_lower_at
#print axioms est_cost_log_sq
#print axioms surrogate_learner_cost
#print axioms exact_oracle_cost
#print axioms surrogate_learner_vs_ideal

end CIGAMF.P13.PaperA6EstCost
