import «LeanPaperA6FixedDesignV1»
import «LeanPaperA7StoppedGenV1»
import «LeanPaperA7IdealFamilyV1»

/-!
# Paper A6: following the surrogate's optimal design costs `log^2(1/delta)`

On the separating family (`thetaC`, cells `Cell r`, noise `sqrt(pairVar M)`), take any
allocation `w` that puts no weight on one middle pair `j`, and run the fixed-design tracking
learner `fixLearner w` (warm start, forcing `1/sqrt(s+1)`, `argmax(W - N)`;
`LeanPaperA6FixedDesignV1`) with the GLR stop of the true alternatives (`tauG`,
`LeanPaperA7StoppedGenV1`).  Then

    E tau_delta >= c log(1/delta)^2,     c = (K M / 8)^2,  K = |Cell r|,

for every `delta` below an explicit `delta_0` (`starved_cost_log_sq`).

The mechanism, all proved here:

* a hidden world `pairAlt j = pairShift thetaC j 1` moves only pair `j`; it is a strict
  alternative, and each query of the pair carries divergence `1/(2M)`, every other query `0`
  (`klq_pair`);
* the stopped change of measure at level `2 delta` (Markov horizon, `ansEv_true_geG`,
  `ansEv_alt_leG`, the fresh-dummy bridge, `change_of_measure`) forces
  `E[N_pair] / (2M) >= (1 - 2delta) log(1/(2delta)) - log 2`;
* forcing is the only source of pair queries, so pathwise
  `N_pair(min(n, tau)) <= 4 + 2(tau/s + s)/K` for every `s > 0`
  (`fCount_le_amgm`, `cnt_eq_at_min`), linear in `tau`;
* choosing `s = sqrt(E tau) + 1` turns `sqrt(E tau) >~ log(1/delta)` into the square.

`surrogate_optimum_cost`: by `starvation_at_optimum₀`, EVERY exact optimum of the frozen
surrogate game puts zero weight on all middle cells, so following it -- the design the
surrogate oracle returns once its estimate is accurate -- costs `Omega(log^2(1/delta))`.
`surrogate_vs_ideal`: the ideal learner of Theorem II pays `O(log(1/delta))` on the same
family, so the ratio of expected costs is unbounded as `delta -> 0`.

SCOPE.  The design is fixed at the surrogate's optimum AT THE TRUE WORLD: the true extrema
enter the allocation, so this is an ORACLE-ALLOCATION statement about the surrogate's own
optimal design, not yet about a learner that recomputes the surrogate at its estimate.  The
lower bound needs no correctness of the stop at other worlds beyond what the GLR stop proves
(`wrong_answer_leG`), and it holds whether or not `E tau` is finite.
-/

namespace CIGAMF.P13.PaperA6SurrogateCost

open Finset MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal
open CIGAMF.P13.PaperA7Stream CIGAMF.P13.PaperA7Process
open CIGAMF.P13.PaperA7IdealLearner CIGAMF.P13.PaperA7IdealStop CIGAMF.P13.PaperA7IdealStopped
open CIGAMF.P13.PaperA7StoppedGen CIGAMF.P13.PaperA6FixedDesign CIGAMF.P13.PaperA7IdealFamily
open CIGAMF.P13.PaperA7IdealUpper CIGAMF.P13.PaperA7IdealSelect
open CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperALowerKL
open CIGAMF.P13.PaperABridge CIGAMF.P13.PaperABridgeDummy CIGAMF.P13.PaperAFamilyLower
open CIGAMF.P13.PaperAEndgame CIGAMF.P13.PaperAStrict CIGAMF.P13.PaperACentred
open CIGAMF.P13.PaperAGaussianKL
open CIGAMF.P13.PaperAActualDecisionBridge
open CIGAMF.P13.PaperARPair (Cell pairShift pairVar pairShift_rest pairShift_true pairShift_false)

variable {r : ℕ}

/-! ## 1. The hidden world and its per-query divergence -/

/-- The two cells of middle pair `j`. -/
def pairCells (j : Fin r) : Finset (Cell r) := {Sum.inr (j, true), Sum.inr (j, false)}

theorem card_pairCells (j : Fin r) : (pairCells j).card = 2 := by
  unfold pairCells
  rw [Finset.card_insert_of_notMem (by simp), Finset.card_singleton]

/-- The hidden world: pair `j` moved apart by `1` each way. -/
noncomputable def pairAlt (j : Fin r) : Cell r → ℝ := pairShift (thetaC r) j 1

theorem pairAlt_alt (j : Fin r) : pairAlt j ∈ TrueAltStrict r := by
  have h := pairShiftC_strict_alt (r := r) j (1 / 2) (by norm_num)
  rw [show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num] at h
  exact ⟨h.1, h.2⟩

theorem pairAlt_centred (j : Fin r) : pairAlt j ∈ Centred r := pairShiftC_mem_centred j 1

/-- **Only the pair's queries separate the two worlds, each by `1/(2M)`.** -/
theorem klq_pair [NeZero r] (M : ℝ) (hM : 0 < M) (j : Fin r) (e : Cell r) :
    klq (famChan M hM) (lift (thetaC r)) (lift (pairAlt j)) (Sum.inl e)
      = if e ∈ pairCells j then ENNReal.ofReal (1 / (2 * M)) else 0 := by
  have hKL := gaussianKLIdentification_holds r M hM (thetaC r) (pairAlt j)
    (thetaC_mem_centred r) (pairAlt_centred j) e
  have h1 : klDiv (observationLaw (familyVariance r M hM) (thetaC r) e)
      (observationLaw (familyVariance r M hM) (pairAlt j) e) ≠ ⊤ := hKL.1
  have h2 : (klDiv (observationLaw (familyVariance r M hM) (thetaC r) e)
      (observationLaw (familyVariance r M hM) (pairAlt j) e)).toReal
        = gaussKL (thetaC r e) (pairAlt j e) (pairVar M e) := hKL.2
  have hk : klq (famChan M hM) (lift (thetaC r)) (lift (pairAlt j)) (Sum.inl e)
      = ENNReal.ofReal (gaussKL (thetaC r e) (pairAlt j e) (pairVar M e)) := by
    unfold klq
    rw [obsLaw_fam_real M hM _ (thetaC_mem_centred r), obsLaw_fam_real M hM _ (pairAlt_centred j),
      ← h2, ENNReal.ofReal_toReal h1]
  rw [hk]
  by_cases he : e ∈ pairCells j
  · rw [if_pos he]
    congr 1
    unfold pairCells at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    unfold gaussKL
    rcases he with rfl | rfl
    · have h := pairShift_true (thetaC r) j 1
      have hd : thetaC r (Sum.inr (j, true)) - pairAlt j (Sum.inr (j, true)) = -1 := by
        unfold pairAlt; linarith
      rw [hd]
      show (-1 : ℝ) ^ 2 / (2 * M) = 1 / (2 * M)
      norm_num
    · have h := pairShift_false (thetaC r) j 1
      have hd : thetaC r (Sum.inr (j, false)) - pairAlt j (Sum.inr (j, false)) = 1 := by
        unfold pairAlt; linarith
      rw [hd]
      show (1 : ℝ) ^ 2 / (2 * M) = 1 / (2 * M)
      norm_num
  · rw [if_neg he]
    unfold pairCells at he
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
    have hrest : pairAlt j e = thetaC r e := pairShift_rest (thetaC r) j 1 e he.1 he.2
    unfold gaussKL
    rw [hrest, sub_self]
    simp

/-! ## 2. The bound at one level -/

/-- The real-cell divergence sum is the pair's expected count times `1/(2M)`. -/
theorem sum_klq_eq [NeZero r] (M : ℝ) (hM : 0 < M) (j : Fin r) (X : Cell r → ℝ≥0∞) :
    ∑ e, X e * klq (famChan M hM) (lift (thetaC r)) (lift (pairAlt j)) (Sum.inl e)
      = ENNReal.ofReal (1 / (2 * M)) * ∑ e ∈ pairCells j, X e := by
  simp_rw [klq_pair M hM j, mul_ite, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
  exact Finset.sum_congr rfl fun e _ => mul_comm _ _

/-- **At one level.**  For a design ignoring pair `j`, every `s > 0`, and a finite expected
cost `I`: `(1 - 2delta) log(1/(2delta)) - log 2 <= (1/M)(2 + s/K + I/(K s))`. -/
theorem starved_lower_at [NeZero r] (M : ℝ) (hM : 0 < M) (a : ℝ) (ha : 0 < a)
    (w : Cell r → ℝ) (hw : PaperA7OracleSelect.IsAlloc w) (j : Fin r)
    (hj : ∀ e ∈ pairCells j, w e = 0)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : 2 * δ ≤ 1) (s : ℝ) (hs : 0 < s)
    (hfin : ∫⁻ ω, (tauG (famSpec r M hM) a δ (fixLearner w) (thetaC r) ω).toENNReal
      ∂streamMeasure ≠ ⊤) :
    (1 - 2 * δ) * Real.log (1 / (2 * δ)) - Real.log 2
      ≤ (1 / M) * (2 + s / (Fintype.card (Cell r) : ℝ)
        + (∫⁻ ω, (tauG (famSpec r M hM) a δ (fixLearner w) (thetaC r) ω).toENNReal
            ∂streamMeasure).toReal / ((Fintype.card (Cell r) : ℝ) * s)) := by
  set P := famSpec r M hM with hP
  set L := fixLearner w with hL
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
  -- the pair's expected count, through the bridge
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
  -- pathwise: forcing is the only source of pair queries
  have hpath : ∀ ω, ∑ e ∈ pairCells j, cntQ (Sum.inl e) n (runSG P a δ L ha (thetaC r) n ω)
      ≤ ENNReal.ofReal (4 + 2 * s / K)
        + ENNReal.ofReal (2 / (K * s)) * (tauG P a δ L (thetaC r) ω).toENNReal := by
    intro ω
    obtain ⟨m, -, hmτ, -, hcnt⟩ := cnt_eq_at_min P a δ L ha (thetaC r) ω n
    have hstep : ∀ e ∈ pairCells j, cntQ (Sum.inl e) n (runSG P a δ L ha (thetaC r) n ω)
        ≤ ENNReal.ofReal (2 + ((m : ℝ) / s + s) / K) := by
      intro e he
      rw [hcnt e]
      exact ENNReal.ofReal_le_ofReal (fCount_le_amgm w hw (thetaC r) P.σ ω e (hj e he) m s hs)
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [Finset.sum_const, card_pairCells, nsmul_eq_mul]
    have hmE : (m : ℝ≥0∞) ≤ (tauG P a δ L (thetaC r) ω).toENNReal := by
      have h := ENat.toENNReal_le.mpr hmτ
      rwa [ENat.toENNReal_coe] at h
    have hsplit : ((2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (2 + ((m : ℝ) / s + s) / K)
        = ENNReal.ofReal (4 + 2 * s / K) + ENNReal.ofReal (2 / (K * s)) * (m : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_natCast m, ← ENNReal.ofReal_mul hd0,
        ← ENNReal.ofReal_add hc0 (mul_nonneg hd0 (Nat.cast_nonneg m)),
        ← ENNReal.ofReal_natCast 2, ← ENNReal.ofReal_mul (Nat.cast_nonneg 2)]
      congr 1
      push_cast
      field_simp
      ring
    rw [hsplit]
    gcongr
  have hint : ∫⁻ ω, ∑ e ∈ pairCells j, cntQ (Sum.inl e) n (runSG P a δ L ha (thetaC r) n ω)
      ∂streamMeasure ≤ ENNReal.ofReal (4 + 2 * s / K) + ENNReal.ofReal (2 / (K * s)) * I := by
    refine le_trans (lintegral_mono hpath) (le_of_eq ?_)
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hk0 : (0 : ℝ) ≤ 1 / (2 * M) := by positivity
  have hx0 : (0 : ℝ) ≤ I.toReal := ENNReal.toReal_nonneg
  have heqE : ENNReal.ofReal (1 / (2 * M) * (4 + 2 * s / K + 2 / (K * s) * I.toReal))
      = ENNReal.ofReal (1 / (2 * M))
        * (ENNReal.ofReal (4 + 2 * s / K) + ENNReal.ofReal (2 / (K * s)) * I) := by
    rw [ENNReal.ofReal_mul hk0, ENNReal.ofReal_add hc0 (mul_nonneg hd0 hx0),
      ENNReal.ofReal_mul hd0, ENNReal.ofReal_toReal hfin]
  have hchain : ENNReal.ofReal ((1 - 2 * δ) * Real.log (1 / (2 * δ)) - Real.log 2)
      ≤ ENNReal.ofReal (1 / (2 * M) * (4 + 2 * s / K + 2 / (K * s) * I.toReal)) :=
    le_trans hcm (le_trans (mul_le_mul_right hint _) heqE.symm.le)
  have hreal' := (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg hk0 (add_nonneg hc0 (mul_nonneg hd0 hx0)))).mp hchain
  have hid : 1 / (2 * M) * (4 + 2 * s / K + 2 / (K * s) * I.toReal)
      = 1 / M * (2 + s / K + I.toReal / (K * s)) := by
    field_simp
    ring
  linarith

/-! ## 3. The square of the logarithm -/

theorem D_ge_half (δ : ℝ) (hδ : 0 < δ) (hδ32 : δ ≤ 1 / 32) :
    Real.log (1 / δ) / 2 ≤ (1 - 2 * δ) * Real.log (1 / (2 * δ)) - Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsplit : Real.log (1 / (2 * δ)) = Real.log (1 / δ) - Real.log 2 := by
    rw [one_div, one_div, Real.log_inv, Real.log_inv, Real.log_mul two_ne_zero hδ.ne']
    ring
  have h32 : 5 * Real.log 2 ≤ Real.log (1 / δ) := by
    have : (32 : ℝ) ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
    have h := Real.log_le_log (by norm_num) this
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow] at h
    push_cast at h
    linarith
  rw [hsplit]
  have hpos : 0 ≤ Real.log (1 / δ) - Real.log 2 := by linarith
  have h1 : (15 / 16 : ℝ) * (Real.log (1 / δ) - Real.log 2)
      ≤ (1 - 2 * δ) * (Real.log (1 / δ) - Real.log 2) :=
    mul_le_mul_of_nonneg_right (by linarith) hpos
  linarith

/-- **`E tau >= c log(1/delta)^2`** for a design that ignores one middle pair. -/
theorem starved_cost_log_sq [NeZero r] (M : ℝ) (hM : 0 < M) (a : ℝ) (ha : 0 < a)
    (w : Cell r → ℝ) (hw : PaperA7OracleSelect.IsAlloc w) (j : Fin r)
    (hj : ∀ e ∈ pairCells j, w e = 0) :
    ∃ c > 0, ∃ δ₀ > 0, ∀ δ, 0 < δ → δ < δ₀ →
      ENNReal.ofReal (c * Real.log (1 / δ) ^ 2)
        ≤ ∫⁻ ω, (tauG (famSpec r M hM) a δ (fixLearner w) (thetaC r) ω).toENNReal
            ∂streamMeasure := by
  have hK0 : (0 : ℝ) < (Fintype.card (Cell r) : ℝ) := by exact_mod_cast Fintype.card_pos
  refine ⟨((Fintype.card (Cell r) : ℝ) * M / 8) ^ 2, by positivity,
    min (1 / 32) (Real.exp (-(4 * (2 * (Fintype.card (Cell r) : ℝ) + 1)
      / ((Fintype.card (Cell r) : ℝ) * M)))), by positivity, fun δ hδ hδ0 => ?_⟩
  set K : ℝ := (Fintype.card (Cell r) : ℝ) with hK
  have hδ32 : δ ≤ 1 / 32 := le_trans hδ0.le (min_le_left _ _)
  have hδe : δ < Real.exp (-(4 * (2 * K + 1) / (K * M))) :=
    lt_of_lt_of_le hδ0 (min_le_right _ _)
  by_cases hfin : ∫⁻ ω, (tauG (famSpec r M hM) a δ (fixLearner w) (thetaC r) ω).toENNReal
      ∂streamMeasure = ⊤
  · rw [hfin]; exact le_top
  have hD := D_ge_half δ hδ hδ32
  have hℓ0 : 4 * (2 * K + 1) / (K * M) < Real.log (1 / δ) := by
    rw [one_div, Real.log_inv]
    have := Real.log_lt_log hδ hδe
    rw [Real.log_exp] at this
    linarith
  have hℓpos : 0 < Real.log (1 / δ) := lt_trans (by positivity) hℓ0
  set I := (∫⁻ ω, (tauG (famSpec r M hM) a δ (fixLearner w) (thetaC r) ω).toENNReal
      ∂streamMeasure).toReal with hI
  have hI0 : 0 ≤ I := ENNReal.toReal_nonneg
  set q := Real.sqrt I with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqq : q * q = I := Real.mul_self_sqrt hI0
  have hq1 : 0 < q + 1 := by linarith
  have hbound := starved_lower_at M hM a ha w hw j hj δ hδ (by linarith) (q + 1) hq1 hfin
  rw [← hI, ← hK] at hbound
  have hq1' := hq1.ne'
  have hK0' := hK0.ne'
  have hM' := hM.ne'
  -- `I / (K (q+1)) <= q / K`
  have hfrac : I / (q + 1) ≤ q := by
    rw [div_le_iff₀ hq1, ← hqq]
    nlinarith
  have hB : 1 / M * (2 + (q + 1) / K + I / (K * (q + 1)))
      = (2 * K + (q + 1) + I / (q + 1)) / (K * M) := by
    field_simp
    try ring
  rw [hB, le_div_iff₀ (by positivity)] at hbound
  have hKM : 0 < K * M := by positivity
  have h2 : Real.log (1 / δ) / 2 * (K * M) ≤ 2 * K + 2 * q + 1 := by
    have := mul_le_mul_of_nonneg_right hD hKM.le
    linarith
  have h3 : 4 * (2 * K + 1) < Real.log (1 / δ) * (K * M) := by
    rwa [div_lt_iff₀ hKM] at hℓ0
  have hqge : K * M * Real.log (1 / δ) / 8 ≤ q := by linarith
  have h0 : 0 ≤ K * M * Real.log (1 / δ) / 8 := by positivity
  have hsq : (K * M / 8) ^ 2 * Real.log (1 / δ) ^ 2 ≤ I := by
    rw [← hqq]
    calc (K * M / 8) ^ 2 * Real.log (1 / δ) ^ 2
        = (K * M * Real.log (1 / δ) / 8) * (K * M * Real.log (1 / δ) / 8) := by ring
      _ ≤ q * q := mul_le_mul hqge hqge h0 hq0
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal hsq

/-! ## 4. Every exact surrogate optimum, and the comparison with the ideal learner -/

/-- **Following ANY exact optimum of the frozen surrogate game costs `Omega(log^2(1/delta))`.**
`frozenValueC₀ M w = frozenGameC₀ r M`: `w` attains the surrogate's optimum (`= 9/512`). -/
theorem surrogate_optimum_cost [NeZero r] (M : ℝ) (hM : 0 < M) (a : ℝ) (ha : 0 < a)
    (w : Cell r → ℝ) (hw : CIGAMF.P13.PaperARPair.IsAlloc w)
    (hopt : frozenValueC₀ M w = frozenGameC₀ r M) :
    ∃ c > 0, ∃ δ₀ > 0, ∀ δ, 0 < δ → δ < δ₀ →
      ENNReal.ofReal (c * Real.log (1 / δ) ^ 2)
        ≤ ∫⁻ ω, (tauG (famSpec r M hM) a δ (fixLearner w) (thetaC r) ω).toENNReal
            ∂streamMeasure := by
  have hopt' : (9 : ℝ) / 512 ≤ frozenValueC₀ M w := by rw [hopt, frozenGameC₀_eq r M hM]
  have hmid := (starvation_at_optimum₀ M hM w hw hopt').2
  have hzero : ∀ p : Fin r × Bool, w (Sum.inr p) = 0 := fun p =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => hw.1 (Sum.inr p))).mp hmid p
      (Finset.mem_univ p)
  refine starved_cost_log_sq M hM a ha w ⟨hw.1, hw.2⟩ ⟨0, Nat.pos_of_ne_zero (NeZero.ne r)⟩
    fun e he => ?_
  unfold pairCells at he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl <;> exact hzero _

/-- **The ratio of expected costs is unbounded.**  On the same family, for every `B`, the
surrogate-optimal design eventually costs more than `B` times the ideal learner. -/
theorem surrogate_vs_ideal [NeZero r] (M : ℝ) (hM : 0 < M) (hr : 0 < r) (a : ℝ) (ha : 0 < a)
    (w : Cell r → ℝ) (hw : CIGAMF.P13.PaperARPair.IsAlloc w)
    (hopt : frozenValueC₀ M w = frozenGameC₀ r M) (B : ℝ) (hB : 0 < B) :
    ∃ δ₀ > 0, ∀ δ, 0 < δ → δ < δ₀ →
      ENNReal.ofReal (B * (∫⁻ ω, (tauI (famSpec r M hM) a δ (thetaC r) ω).toENNReal
          ∂streamMeasure).toReal)
        ≤ ∫⁻ ω, (tauG (famSpec r M hM) a δ (fixLearner w) (thetaC r) ω).toENNReal
            ∂streamMeasure := by
  obtain ⟨c, hc, δ₁, hδ₁, hlow⟩ := surrogate_optimum_cost M hM a ha w hw hopt
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

/-- **The optimum hypothesis is satisfiable**: the uniform design on the anchors is an exact
optimum of the frozen surrogate game. -/
theorem surrogate_optimum_exists (M : ℝ) (hM : 0 < M) :
    CIGAMF.P13.PaperARPair.IsAlloc (wUnifC r) ∧ frozenValueC₀ M (wUnifC r) = frozenGameC₀ r M := by
  refine ⟨wUnifC_isAlloc r, ?_⟩
  rw [frozenGameC₀_eq r M hM]
  refine le_antisymm ?_ (le_trans (frozenValueC_unif_ge M hM)
    (frozenValueC_le_restricted M hM (wUnifC r) (wUnifC_isAlloc r).1))
  have h := frozenValueC₀_le M hM (wUnifC r) (wUnifC_isAlloc r)
  have ha := aMass_le_one (wUnifC r) (wUnifC_isAlloc r)
  linarith

/-- **The concrete instance**: tracking the uniform surrogate optimum costs `Omega(log^2(1/delta))`. -/
theorem uniform_surrogate_cost [NeZero r] (M : ℝ) (hM : 0 < M) (a : ℝ) (ha : 0 < a) :
    ∃ c > 0, ∃ δ₀ > 0, ∀ δ, 0 < δ → δ < δ₀ →
      ENNReal.ofReal (c * Real.log (1 / δ) ^ 2)
        ≤ ∫⁻ ω, (tauG (famSpec r M hM) a δ (fixLearner (wUnifC r)) (thetaC r) ω).toENNReal
            ∂streamMeasure :=
  surrogate_optimum_cost M hM a ha (wUnifC r) (surrogate_optimum_exists M hM).1
    (surrogate_optimum_exists M hM).2

#print axioms klq_pair
#print axioms starved_lower_at
#print axioms starved_cost_log_sq
#print axioms surrogate_optimum_cost
#print axioms surrogate_vs_ideal
#print axioms surrogate_optimum_exists
#print axioms uniform_surrogate_cost

end CIGAMF.P13.PaperA6SurrogateCost
