import «LeanPaperA7IdealStoppedV1»
import «LeanPaperAFamilyLowerV1»

/-!
# Paper A7: the ideal learner on the separating family -- the operational finish

The concrete two-answer problem of Paper A: cells `Cell r`, noise `sigma_e = sqrt(pairVar M e)`,
answers `true` (retain `A`) and `false` (retain `B`), with

* `Alt true  = TrueAltStrict r = {rangeA < rangeB} ∩ Centred r` (the worlds where `A` is wrong),
* `Alt false = {rangeB < rangeA} ∩ Centred r` (the worlds where `B` is wrong).

At the family's world `thetaC` the answer is `A` (`thetaC_mem_altB`), and

* `GamT_fam` -- the ideal learner's game is the ACTUAL Gaussian KL game:
  `GamT (famSpec) true thetaC = actualKLGame r M` (the scaled penalty is the family's energy);
* `ideal_family_lower` -- through the stopped learner, the fresh-dummy bridge
  (`stream_eq_hist_fresh`) and `family_policy_lower` at level `2 delta` (the horizon chosen by
  Markov so that `P(tau > n) <= delta`):
  `((1 - 2 delta) log(1/(2 delta)) - log 2) / actualKLGame <= E tau_delta`;
* `ideal_family_finish` -- **`OperationalFinish streamMeasure tau (actualKLGame r M)`** for the
  hitting time `tau_delta = tauI` of the learner that is actually defined (`idealLearner` with
  the GLR stop at level `delta`).  The world enters only as the law of the observations.
-/

namespace CIGAMF.P13.PaperA7IdealFamily

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal
open CIGAMF.P13.PaperA7Stream CIGAMF.P13.PaperA7Process
open CIGAMF.P13.PaperA7IdealLearner CIGAMF.P13.PaperA7IdealStop CIGAMF.P13.PaperA7IdealSelect
open CIGAMF.P13.PaperA7IdealUpper CIGAMF.P13.PaperA7IdealStopped CIGAMF.P13.PaperA7DirectLower
open CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperALowerKL CIGAMF.P13.PaperALowerGame
open CIGAMF.P13.PaperABridge CIGAMF.P13.PaperABridgeDummy
open CIGAMF.P13.PaperAFamilyLower CIGAMF.P13.PaperAEndgame CIGAMF.P13.PaperAStrict
open CIGAMF.P13.PaperACentred CIGAMF.P13.PaperAGaussianKL CIGAMF.P13.PaperAActualDecisionBridge
open CIGAMF.P13.PaperARPair (Cell)

variable {r : ℕ}

/-! ## 1. The family as a specification -/

/-- The alternatives of the two answers. -/
def famAlt (r : ℕ) : Bool → Set (Cell r → ℝ)
  | true => TrueAltStrict r
  | false => {lam | PaperARPair.rangeB lam < PaperARPair.rangeA lam} ∩ Centred r

theorem rangeB_lt_rangeA_thetaC (r : ℕ) :
    PaperARPair.rangeB (thetaC r) < PaperARPair.rangeA (thetaC r) := by
  have hA : PaperARPair.rangeA (thetaC r) = 1 := by
    simp [PaperARPair.rangeA, thetaC_0, thetaC_1]; norm_num
  have hB : PaperARPair.rangeB (thetaC r) = 1 / 4 := by
    have hhi : (PaperARPair.BCells r).sup' (PaperARPair.BCells_nonempty r) (thetaC r) = 1 / 8 := by
      apply le_antisymm
      · exact Finset.sup'_le _ _ (fun e he => (thetaC_bcell_bound r e he).2)
      · have hmem : (Sum.inl 3 : Cell r) ∈ PaperARPair.BCells r := by
          rw [PaperARPair.BCells, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, rfl⟩
        have hle := Finset.le_sup' (thetaC r) hmem
        rwa [thetaC_3] at hle
    have hlo : (PaperARPair.BCells r).inf' (PaperARPair.BCells_nonempty r) (thetaC r)
        = -(1 / 8) := by
      apply le_antisymm
      · have hge := Finset.inf'_le (thetaC r) (PaperARPair.bAnchor_mem r)
        rwa [thetaC_2] at hge
      · exact Finset.le_inf' _ _ (fun e he => (thetaC_bcell_bound r e he).1)
    unfold PaperARPair.rangeB; rw [hhi, hlo]; norm_num
  rw [hA, hB]; norm_num

theorem thetaC_mem_altB (r : ℕ) : thetaC r ∈ famAlt r false :=
  ⟨rangeB_lt_rangeA_thetaC r, thetaC_mem_centred r⟩

theorem famAlt_ne (r : ℕ) [NeZero r] : ∀ T, (famAlt r T).Nonempty
  | true => by
      obtain ⟨lam⟩ := instNonemptyTrueAltStrict r
      exact ⟨lam.1, lam.2⟩
  | false => ⟨thetaC r, thetaC_mem_altB r⟩

/-- **The family's specification.**  The noise is the family's; the forcing schedule is
`kf s = s + 1`. -/
noncomputable def famSpec (r : ℕ) [NeZero r] (M : ℝ) (hM : 0 < M) : Spec (Cell r) Bool where
  σ e := Real.sqrt (PaperARPair.pairVar M e)
  σ_pos e := Real.sqrt_pos.mpr (pairVarC_pos M hM e)
  Alt := famAlt r
  Alt_ne := famAlt_ne r
  kf s := s + 1
  kf_pos s := Nat.succ_pos s

theorem fam_wrong (r : ℕ) [NeZero r] (M : ℝ) (hM : 0 < M) :
    ∀ T, T ≠ true → thetaC r ∈ (famSpec r M hM).Alt T := by
  intro T hT
  cases T with
  | false => exact thetaC_mem_altB r
  | true => exact absurd rfl hT

theorem fam_kf (r : ℕ) [NeZero r] (M : ℝ) (hM : 0 < M) :
    ∀ s : ℕ, (s : ℝ) + 1 ≤ (famSpec r M hM).kf s := by
  intro s
  show (s : ℝ) + 1 ≤ ((s + 1 : ℕ) : ℝ)
  push_cast
  exact le_rfl

/-! ## 2. The learner's game is the actual KL game -/

theorem pen_sc_eq [NeZero r] (M : ℝ) (hM : 0 < M) (w lam : Cell r → ℝ) :
    PaperA7OracleSelect.pen w (sc (famSpec r M hM).σ (thetaC r)) (sc (famSpec r M hM).σ lam)
      = PaperARPair.energy w (PaperARPair.pairVar M) (thetaC r) lam := by
  unfold PaperA7OracleSelect.pen PaperARPair.energy sc
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  have hv := pairVarC_pos M hM e
  have hss : Real.sqrt (PaperARPair.pairVar M e) ^ 2 = PaperARPair.pairVar M e :=
    Real.sq_sqrt hv.le
  show w e * (thetaC r e / Real.sqrt (PaperARPair.pairVar M e)
      - lam e / Real.sqrt (PaperARPair.pairVar M e)) ^ 2
    = w e * (lam e - thetaC r e) ^ 2 / PaperARPair.pairVar M e
  rw [div_sub_div_same, div_pow, hss]
  ring

/-- **The ideal learner's game on the family is the actual Gaussian KL game.** -/
theorem GamT_fam [NeZero r] (M : ℝ) (hM : 0 < M) :
    GamT (famSpec r M hM) true (thetaC r) = actualKLGame r M hM := by
  rw [actualKLGame_eq M hM (gaussianKLIdentification_holds r M hM)]
  have hval : ∀ w, PaperA7OracleSelect.Jval (sc (famSpec r M hM).σ '' (famSpec r M hM).Alt true)
      w (sc (famSpec r M hM).σ (thetaC r)) = trueValueStrict M w := by
    intro w
    unfold PaperA7OracleSelect.Jval trueValueStrict
    rw [Set.image_image, sInf_image']
    exact iInf_congr fun lam => pen_sc_eq M hM w lam
  unfold GamT trueGameStrict
  have hset : {v : ℝ | ∃ w : Cell r → ℝ, PaperA7OracleSelect.IsAlloc w ∧
      v = PaperA7OracleSelect.Jval (sc (famSpec r M hM).σ '' (famSpec r M hM).Alt true) w
        (sc (famSpec r M hM).σ (thetaC r))}
      = Set.range (fun w : {w : Cell r → ℝ // PaperARPair.IsAlloc w} =>
          trueValueStrict M (w : Cell r → ℝ)) := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, hw.1, hw.2⟩, (hval w).symm⟩
    · rintro ⟨w, rfl⟩
      exact ⟨w.val, ⟨w.2.1, w.2.2⟩, (hval w.val).symm⟩
  rw [hset]
  rfl

theorem game_pos [NeZero r] (M : ℝ) (hM : 0 < M) (hr : 0 < r) : 0 < actualKLGame r M hM := by
  rw [actualKLGame_eq M hM (gaussianKLIdentification_holds r M hM)]
  exact lt_of_lt_of_le (by positivity) (strict_game_bounds M hM hr).1

theorem GamT_fam_pos [NeZero r] (M : ℝ) (hM : 0 < M) (hr : 0 < r) :
    0 < GamT (famSpec r M hM) true (thetaC r) := by
  rw [GamT_fam]; exact game_pos M hM hr

/-! ## 3. The lower bound through the stopped learner -/

/-- **Markov's inequality for the horizon.** -/
theorem markov_horizon {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : Ω → ℕ∞) (hτ : Measurable τ) (hfin : ∫⁻ ω, (τ ω).toENNReal ∂μ ≠ ⊤) (δ : ℝ)
    (hδ : 0 < δ) : ∃ n : ℕ, μ.real {ω | (n : ℕ∞) < τ ω} ≤ δ := by
  set I := (∫⁻ ω, (τ ω).toENNReal ∂μ).toReal with hI
  have hI0 : 0 ≤ I := ENNReal.toReal_nonneg
  refine ⟨⌈I / δ⌉₊ + 1, ?_⟩
  set n := ⌈I / δ⌉₊ + 1 with hn
  have hn0 : (0 : ℝ) < n := by positivity
  have hmk := mul_meas_ge_le_lintegral₀ (μ := μ)
    ((Measurable.of_discrete (f := ENat.toENNReal)).comp hτ).aemeasurable (n : ℝ≥0∞)
  have hsub : {ω | (n : ℕ∞) < τ ω} ⊆ {ω | (n : ℝ≥0∞) ≤ (τ ω).toENNReal} := by
    intro ω hω
    show (n : ℝ≥0∞) ≤ (τ ω).toENNReal
    rw [← ENat.toENNReal_coe]
    exact ENat.toENNReal_le.mpr (le_of_lt hω)
  have h1 : (n : ℝ≥0∞) * μ {ω | (n : ℕ∞) < τ ω} ≤ ∫⁻ ω, (τ ω).toENNReal ∂μ :=
    le_trans (mul_le_mul_of_nonneg_left (measure_mono hsub) (by positivity)) hmk
  have h2 := ENNReal.toReal_mono hfin h1
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ← measureReal_def] at h2
  have hceil : I / δ ≤ ⌈I / δ⌉₊ := Nat.le_ceil _
  have hnI : I < n * δ := by
    have : I / δ < n := by rw [hn]; push_cast; linarith
    rwa [div_lt_iff₀ hδ] at this
  have hp0 : 0 ≤ μ.real {ω | (n : ℕ∞) < τ ω} := measureReal_nonneg
  nlinarith

theorem hD_small (δ : ℝ) (hδ : 0 < δ) (hδ16 : δ < 1 / 16) :
    0 < (1 - 2 * δ) * Real.log (1 / (2 * δ)) - Real.log 2 := by
  have h8 : (8 : ℝ) < 1 / (2 * δ) := by rw [lt_div_iff₀ (by positivity)]; linarith
  have hl8 : Real.log 8 < Real.log (1 / (2 * δ)) := Real.log_lt_log (by norm_num) h8
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : (7 / 8 : ℝ) ≤ 1 - 2 * δ := by linarith
  have hLpos : 0 < Real.log (1 / (2 * δ)) := by linarith
  have := mul_le_mul_of_nonneg_right h1 hLpos.le
  linarith

/-- **The lower bound for the ideal learner on the family**, at each level. -/
theorem ideal_family_lower [NeZero r] (M : ℝ) (hM : 0 < M) (hr : 0 < r) (a : ℝ) (ha : 0 < a)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : 2 * δ ≤ 1)
    (hD : 0 < (1 - 2 * δ) * Real.log (1 / (2 * δ)) - Real.log 2)
    (hfin : (∫⁻ ω, (tauI (famSpec r M hM) a δ (thetaC r) ω).toENNReal ∂streamMeasure) ≠ ⊤) :
    ((1 - 2 * δ) * Real.log (1 / (2 * δ)) - Real.log 2) / actualKLGame r M hM
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
  have hmain := family_policy_lower M hM hr (detPol L) n S hS (2 * δ) (by positivity) hδ1 hθ hl hD
  refine le_trans hmain ?_
  have hfinC : ∀ e : Cell r,
      ∫⁻ ω, cntQ (Sum.inl e) n ω ∂hist (famChan M hM) (detPol L) (lift (thetaC r)) n ≠ ⊤ :=
    fun e => lintegral_cntQ_ne_top _ _ _ _ n
  rw [← ENNReal.toReal_sum (fun e _ => hfinC e)]
  refine ENNReal.toReal_mono hfin ?_
  have hsum : ∑ e : Cell r,
      ∫⁻ ω, cntQ (Sum.inl e) n ω ∂hist (famChan M hM) (detPol L) (lift (thetaC r)) n
      = ∫⁻ ω, ∑ e : Cell r, cntQ (Sum.inl e) n ω
          ∂hist (famChan M hM) (detPol L) (lift (thetaC r)) n :=
    (lintegral_finset_sum _ fun e _ => measurable_cntQ _ n).symm
  rw [hsum, hbr, lintegral_map (Finset.measurable_sum _ fun e _ => measurable_cntQ _ n)
    (measurable_runS P a δ ha _ n)]
  exact lintegral_mono fun ω => cnt_le_tau P a δ ha (thetaC r) ω n

/-- **From the per-level lower bound to the lower rate.** -/
theorem lower_rate_of_bound (N : ℝ → ℝ) (Γ : ℝ) (hΓ : 0 < Γ) (δ0 : ℝ) (hδ0 : 0 < δ0)
    (hbound : ∀ δ, 0 < δ → δ < δ0 →
      ((1 - 2 * δ) * Real.log (1 / (2 * δ)) - Real.log 2) / Γ ≤ N δ) :
    LowerRate N Γ := by
  intro ε hε
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c := 4 * Real.log 2 / (ε * Γ) with hc
  have hc0 : 0 < c := by positivity
  refine ⟨min (min δ0 (1 / 2)) (min (ε * Γ / 4) (Real.exp (-c))), by positivity,
    fun δ hδ hδu => ?_⟩
  have hδu' : δ < min (min δ0 (1 / 2)) (min (ε * Γ / 4) (Real.exp (-c))) :=
    lt_of_lt_of_le hδu (min_le_left _ _)
  have hδ0' : δ < δ0 := lt_of_lt_of_le hδu' (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδε : δ < ε * Γ / 4 := lt_of_lt_of_le hδu' (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδe : δ < Real.exp (-c) :=
    lt_of_lt_of_le hδu' (le_trans (min_le_right _ _) (min_le_right _ _))
  set ℓ := Real.log (1 / δ) with hℓ
  have hℓc : c < ℓ := by
    rw [hℓ, one_div, Real.log_inv]
    have := Real.log_lt_log hδ hδe
    rw [Real.log_exp] at this
    linarith
  have hℓ0 : 0 < ℓ := lt_trans hc0 hℓc
  have hsplit : Real.log (1 / (2 * δ)) = ℓ - Real.log 2 := by
    rw [hℓ, one_div, one_div, Real.log_inv, Real.log_inv, Real.log_mul two_ne_zero hδ.ne']
    ring
  have hb := hbound δ hδ hδ0'
  rw [hsplit] at hb
  show 1 / Γ - ε ≤ N δ / ℓ
  rw [le_div_iff₀ hℓ0]
  refine le_trans ?_ hb
  rw [le_div_iff₀ hΓ]
  have hcl : 4 * Real.log 2 < ε * Γ * ℓ := by
    rw [hc, div_lt_iff₀ (by positivity)] at hℓc; linarith
  have e1 : (1 / Γ - ε) * ℓ * Γ = ℓ - ε * Γ * ℓ := by
    field_simp
    try ring
  rw [e1]
  have h2δ : 2 * δ * ℓ ≤ ε * Γ / 2 * ℓ :=
    mul_le_mul_of_nonneg_right (by linarith) hℓ0.le
  nlinarith [mul_nonneg hδ.le hl2.le]

/-- **The lower rate of the ideal learner on the family.** -/
theorem ideal_family_lower_rate [NeZero r] (M : ℝ) (hM : 0 < M) (hr : 0 < r) (a : ℝ)
    (ha : 0 < a) :
    LowerRate (fun δ => (∫⁻ ω, (tauI (famSpec r M hM) a δ (thetaC r) ω).toENNReal
      ∂streamMeasure).toReal) (actualKLGame r M hM) := by
  have hfin := ideal_finite (famSpec r M hM) a ha true (thetaC r) (fam_wrong r M hM)
    (fam_kf r M hM) (GamT_fam_pos M hM hr)
  refine lower_rate_of_bound _ _ (game_pos M hM hr) (1 / 16) (by norm_num) fun δ hδ hδ16 => ?_
  exact ideal_family_lower M hM hr a ha δ hδ (by linarith) (hD_small δ hδ hδ16)
    (hfin δ hδ (by linarith))

/-! ## 4. The operational finish -/

/-- **The defined ideal learner attains the exact rate `1 / actualKLGame` on the family.** -/
theorem ideal_family_finish [NeZero r] (M : ℝ) (hM : 0 < M) (hr : 0 < r) (a : ℝ) (ha : 0 < a) :
    OperationalFinish streamMeasure (fun δ => tauI (famSpec r M hM) a δ (thetaC r))
      (actualKLGame r M hM) := by
  have hΓ := GamT_fam_pos M hM hr
  refine family_operational_finish streamMeasure _ M hM hr (gaussianKLIdentification_holds r M hM)
    (ideal_finite (famSpec r M hM) a ha true (thetaC r) (fam_wrong r M hM) (fam_kf r M hM) hΓ)
    ?_ (ideal_family_lower_rate M hM hr a ha)
  rw [← GamT_fam M hM]
  exact ideal_upper_rate (famSpec r M hM) a ha true (thetaC r) (fam_wrong r M hM)
    (fam_kf r M hM) hΓ

/-- **The same learner is `delta`-correct on the family**: at `thetaC` (answer `A`) a wrong
answer has probability at most `delta`. -/
theorem ideal_family_correct [NeZero r] (M : ℝ) (hM : 0 < M) (a : ℝ) (ha : 0 < a) (δ : ℝ)
    (hδ : 0 < δ) :
    streamMeasure {ω | ∃ t, stopAt (famSpec r M hM) a δ t (runH (famSpec r M hM) (thetaC r) t ω)
      ∧ answerAt (famSpec r M hM) a (runH (famSpec r M hM) (thetaC r) t ω) ≠ true}
      ≤ ENNReal.ofReal δ := by
  have h := ideal_correct (famSpec r M hM) a ha δ hδ true (thetaC r) (fam_wrong r M hM)
  simpa using h

#print axioms rangeB_lt_rangeA_thetaC
#print axioms GamT_fam
#print axioms markov_horizon
#print axioms ideal_family_lower
#print axioms lower_rate_of_bound
#print axioms ideal_family_lower_rate
#print axioms ideal_family_finish
#print axioms ideal_family_correct

end CIGAMF.P13.PaperA7IdealFamily
