import «LeanPaperBParityChannelV1»
import «LeanPaperBObstructionV1»
import «LeanPaperBRateClosureV1»

/-!
# Paper B: the parity experiment as an `Experiment`, and its two lower certificates

This module instantiates the typed interface `PaperBEndgame.Experiment` from the concrete
adaptive protocol on the parity channel -- not from a discrete surrogate:

* a policy (`Pol`) is a horizon `N`, the adaptive query kernels `pol` of
  `LeanPaperBProtocolV1` (round `n` sees only the first `n` rounds, so queries are predictable
  by construction), and an answer and a guess that are functions of the history at the
  horizon.  Stopping early is issuing the dummy query, which costs nothing and carries no
  information; the cost `tau` counts the non-dummy queries;
* the law of the run at signal level `h` in world `w` is the history law `hist` of
  `LeanPaperBProtocolV1` on `parChan` (at level `max h 0`), pushed to the sequence space
  `ℕ → Fin m × ℝ` by padding with dummy rounds;
* `allowed` requires the answer and the guess to be measurable;
* loss `tipLoss m` and tolerance `0`, so a safe answer is any `a ≠ w` (`tip_wrong_iff`).

The policy class is that of every randomised adaptive policy with a finite horizon: its
stopping time is bounded (by the horizon), not merely almost surely finite.

The two lower certificates are then DERIVED, for every such policy:

* `safeLower` -- `find_pair`: a correct policy's answer at world `0` puts mass
  `(1-delta)/(m-1)` on some `v ≠ 0` (`safe_pair_exists`), an event that has mass `<= delta`
  at world `v`; the event bound `event_klDiv_ge` and `demand_of_small_delta` give
  `KL >= log(1/delta) / (4(m-1))`.  `stopped_information`: data processing
  (`klDiv_map_le`) and the transcript bound `transcript_kl_le`, with the per-query chi-square
  of `parChan_chi_le`, give `KL <= aS h^2 * E[tau]`;
* `idLower` -- the pair `(m-1, m-2)`: only query `m-1` names either world, so the per-query
  information is `<= aI h^(2(m-1))`, and correctness of the guess gives
  `KL >= log(1/delta)/4`.
-/

namespace CIGAMF.P13.PaperBParityExperiment

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBChiSq CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperBParityLaw
open CIGAMF.P13.PaperBParityChiSq CIGAMF.P13.PaperBParityChannel CIGAMF.P13.PaperBObstruction
open CIGAMF.P13.PaperBEndgame CIGAMF.P13.PaperBRateClosure

variable (m : ℕ)

/-- A policy: horizon, adaptive query kernels, and the outputs at the horizon. -/
structure Pol where
  N : ℕ
  pol : Policy (Fin m)
  answer : Hist (Fin m) N → Fin m
  guess : Hist (Fin m) N → Fin m

/-- The sequence space of runs. -/
abbrev Om := ℕ → Fin m × ℝ

/-- The first `N` rounds of a run. -/
def restrictH (N : ℕ) (ω : Om m) : Hist (Fin m) N := fun i => ω i

/-- A history padded with dummy rounds. -/
def extendH (d : Fin m) (N : ℕ) (x : Hist (Fin m) N) : Om m :=
  fun i => if hi : i < N then x ⟨i, hi⟩ else (d, 0)

theorem restrict_extend (d : Fin m) (N : ℕ) (x : Hist (Fin m) N) :
    restrictH m N (extendH m d N x) = x := by
  funext i
  simp [restrictH, extendH, i.isLt]

theorem measurable_restrictH (N : ℕ) : Measurable (restrictH m N) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply (i : ℕ)

theorem measurable_extendH (d : Fin m) (N : ℕ) : Measurable (extendH m d N) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases hi : i < N
  · have : (fun x : Hist (Fin m) N => extendH m d N x i) = fun x => x ⟨i, hi⟩ := by
      funext x; simp [extendH, hi]
    rw [this]; exact measurable_pi_apply _
  · have : (fun x : Hist (Fin m) N => extendH m d N x i) = fun _ => (d, 0) := by
      funext x; simp [extendH, hi]
    rw [this]; exact measurable_const

variable {m}

/-- The channel at signal level `h` (a negative level is read as `0`). -/
noncomputable def chanAt (σ : ℝ) (hσ : 0 < σ) (hm : 0 < m) (h : ℝ) : Channel (Fin m) (Fin m) :=
  parChan m σ (max h 0) hσ (le_max_right h 0) hm

/-- The law of a run. -/
noncomputable def lawAt (σ : ℝ) (hσ : 0 < σ) (hm : 0 < m) (h : ℝ) (P : Pol m) (w : Fin m) :
    Measure (Om m) :=
  (hist (chanAt σ hσ hm h) P.pol w P.N).map (extendH m ⟨0, hm⟩ P.N)

theorem lawAt_prob (σ : ℝ) (hσ : 0 < σ) (hm : 0 < m) (h : ℝ) (P : Pol m) (w : Fin m) :
    IsProbabilityMeasure (lawAt σ hσ hm h P w) := by
  haveI := hist_prob (chanAt σ hσ hm h) P.pol w P.N
  exact (Measure.isProbabilityMeasure_map_iff (measurable_extendH m _ _).aemeasurable).mpr
    inferInstance

/-- The cost of a run: its number of non-dummy queries. -/
noncomputable def tauP (hm : 0 < m) (P : Pol m) (ω : Om m) : ℕ∞ :=
  ((tauN (⟨0, hm⟩ : Fin m) P.N (restrictH m P.N ω) : ℕ) : ℕ∞)

theorem measurable_tauP (hm : 0 < m) (P : Pol m) : Measurable (tauP hm P) :=
  (Measurable.of_discrete (f := fun k : ℕ => (k : ℕ∞))).comp
    ((measurable_tauN _ _).comp (measurable_restrictH m _))

/-- **The parity experiment.** -/
noncomputable def parExp (σ : ℝ) (hσ : 0 < σ) (hm : 0 < m) :
    Experiment (Fin m) (Fin m) (Pol m) (Om m) where
  law := lawAt σ hσ hm
  probability h P w := lawAt_prob σ hσ hm h P w
  allowed P := Measurable P.answer ∧ Measurable P.guess
  tau P := tauP hm P
  answer P ω := P.answer (restrictH m P.N ω)
  guess P ω := P.guess (restrictH m P.N ω)
  loss := tipLoss m
  tolerance := 0
  tau_measurable P := measurable_tauP hm P

/-- The experiment's cost is the protocol's cost. -/
theorem costAt_eq (σ : ℝ) (hσ : 0 < σ) (hm : 0 < m) (h : ℝ) (P : Pol m) (w : Fin m) :
    costAt (parExp σ hσ hm) h P w = costN (chanAt σ hσ hm h) P.pol w P.N := by
  unfold costAt costN
  show ∫⁻ ω, (tauP hm P ω).toENNReal ∂(lawAt σ hσ hm h P w) = _
  have hmeas : Measurable fun ω : Om m => (tauP hm P ω).toENNReal :=
    (Measurable.of_discrete (f := fun k : ℕ => ((k : ℕ∞).toENNReal))).comp
      ((measurable_tauN _ _).comp (measurable_restrictH m _))
  unfold lawAt
  rw [lintegral_map hmeas (measurable_extendH m _ _)]
  refine lintegral_congr fun x => ?_
  unfold tauP
  rw [restrict_extend, ENat.toENNReal_coe]
  rfl

/-- **Stopped information**: data processing and the transcript bound. -/
theorem kl_le_cost (σ : ℝ) (hσ : 0 < σ) (hm : 0 < m) (h : ℝ) (P : Pol m) (w v : Fin m)
    (Cmax : ℝ≥0∞) (hchi : ∀ q, q ≠ (⟨0, hm⟩ : Fin m) → chi (chanAt σ hσ hm h) w v q ≤ Cmax) :
    klDiv ((parExp σ hσ hm).law h P w) ((parExp σ hσ hm).law h P v)
      ≤ Cmax * costAt (parExp σ hσ hm) h P w := by
  haveI := hist_prob (chanAt σ hσ hm h) P.pol w P.N
  haveI := hist_prob (chanAt σ hσ hm h) P.pol v P.N
  rw [costAt_eq]
  exact (klDiv_map_le _ _ (measurable_extendH m _ _)).trans
    (transcript_kl_le (chanAt σ hσ hm h) P.pol w v Cmax hchi P.N)

/-! ## Per-query information of the two hard pairs -/

/-- The safe information constant. -/
noncomputable def aS (m : ℕ) (σ : ℝ) : ℝ := 1 + ∑ q ∈ Finset.range m, parC q σ 1

theorem aS_pos (σ : ℝ) (hσ : 0 < σ) : 0 < aS m σ := by
  unfold aS
  have := Finset.sum_nonneg fun q (_ : q ∈ Finset.range m) => parC_nonneg q σ 1 hσ
  linarith

/-- The identification information constant. -/
noncomputable def aI (m : ℕ) (σ : ℝ) : ℝ := 1 + parC (m - 1) σ 1

theorem aI_pos (σ : ℝ) (hσ : 0 < σ) : 0 < aI m σ := by
  unfold aI
  have := parC_nonneg (m - 1) σ 1 hσ
  linarith

theorem chi_le_safe (σ : ℝ) (hσ : 0 < σ) (hm : 0 < m) (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1)
    (w v q : Fin m) (hq : q ≠ (⟨0, hm⟩ : Fin m)) :
    chi (chanAt σ hσ hm h) w v q ≤ ENNReal.ofReal (aS m σ * h ^ (2 * 1)) := by
  have hmax : max h 0 = h := max_eq_left hh.le
  have hc := parChan_chi_le m σ (max h 0) 1 hσ (le_max_right h 0) (by rw [hmax]; exact hh1) hm
    w v q
  refine hc.trans ?_
  split_ifs
  · exact bot_le
  · apply ENNReal.ofReal_le_ofReal
    rw [hmax]
    have hq1 : 1 ≤ (q : ℕ) := Nat.one_le_iff_ne_zero.mpr fun h0 => hq (Fin.ext h0)
    have hpow : h ^ (2 * (q : ℕ)) ≤ h ^ (2 * 1) := pow_le_pow_of_le_one hh.le hh1 (by omega)
    have hpc : parC q σ 1 ≤ aS m σ := by
      unfold aS
      have := Finset.single_le_sum (fun i (_ : i ∈ Finset.range m) => parC_nonneg i σ 1 hσ)
        (Finset.mem_range.mpr q.isLt)
      linarith
    calc parC q σ 1 * h ^ (2 * (q : ℕ)) ≤ aS m σ * h ^ (2 * (q : ℕ)) :=
          mul_le_mul_of_nonneg_right hpc (by positivity)
      _ ≤ aS m σ * h ^ (2 * 1) := mul_le_mul_of_nonneg_left hpow (aS_pos σ hσ).le

theorem chi_le_id (σ : ℝ) (hσ : 0 < σ) (hm : 0 < m) (hm2 : 2 ≤ m) (h : ℝ) (hh : 0 < h)
    (hh1 : h ≤ 1) (w v q : Fin m) (hw : (w : ℕ) = m - 1) (hv : (v : ℕ) = m - 2)
    (hq : q ≠ (⟨0, hm⟩ : Fin m)) :
    chi (chanAt σ hσ hm h) w v q ≤ ENNReal.ofReal (aI m σ * h ^ (2 * (m - 1))) := by
  have hmax : max h 0 = h := max_eq_left hh.le
  have hc := parChan_chi_le m σ (max h 0) 1 hσ (le_max_right h 0) (by rw [hmax]; exact hh1) hm
    w v q
  refine hc.trans ?_
  split_ifs with hmask
  · exact bot_le
  · apply ENNReal.ofReal_le_ofReal
    rw [hmax]
    have hne : (w : ℕ) + 1 ≠ (v : ℕ) + 1 := by omega
    have hname := (masks_differ_iff q ((w : ℕ) + 1) ((v : ℕ) + 1) hne).mp hmask
    have hqv : (q : ℕ) = m - 1 := by
      have := q.isLt
      omega
    rw [hqv]
    have : parC (m - 1) σ 1 ≤ aI m σ := by unfold aI; linarith
    exact mul_le_mul_of_nonneg_right this (by positivity)

/-! ## The two lower certificates -/

theorem hεmax (hm2 : 2 ≤ m) : (0 : ℝ) < ((m : ℝ) - 1) / 2 := by
  have : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  linarith

theorem wrong_safe_eq (σ : ℝ) (hσ : 0 < σ) (hm : 0 < m) (hm2 : 2 ≤ m) (P : Pol m) (w : Fin m) :
    wrong (parExp σ hσ hm) .safe P w = {ω | (parExp σ hσ hm).answer P ω = w} := by
  ext ω
  show (0 : ℝ) < tipLoss m w (P.answer (restrictH m P.N ω)) ↔ P.answer (restrictH m P.N ω) = w
  exact tip_wrong_iff m hm2 0 le_rfl (hεmax hm2) w _

/-- **The safe lower certificate**, for every finite-horizon adaptive policy. -/
noncomputable def safeLower (σ : ℝ) (hσ : 0 < σ) (hm : 0 < m) (hm2 : 2 ≤ m) (h δ : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hδm : δ ≤ (2 : ℝ) ^ (-(4 * ((m : ℝ) - 1)))) :
    HardPairCertificate (parExp σ hσ hm) .safe h δ (ENNReal.ofReal (aS m σ * h ^ (2 * 1)))
      (ENNReal.ofReal ((1 / (4 * ((m : ℝ) - 1))) * Real.log (1 / δ))) where
  hard w v := w ≠ v
  find_pair P hP := by
    obtain ⟨hallow, hcorr⟩ := hP
    set X := parExp σ hσ hm with hX
    let w0 : Fin m := ⟨0, hm⟩
    haveI := X.probability h P w0
    have hans : Measurable (X.answer P) := hallow.1.comp (measurable_restrictH m P.N)
    have hw0 : (X.law h P w0).real {ω | X.answer P ω = w0} ≤ δ := by
      rw [← wrong_safe_eq σ hσ hm hm2]
      exact ENNReal.toReal_le_of_le_ofReal hδ.le (hcorr w0).2
    obtain ⟨v, hv, hpv⟩ := safe_pair_exists hm2 (X.law h P w0) (X.answer P) hans w0 δ hw0
    refine ⟨w0, v, fun h' => hv h'.symm, ?_⟩
    haveI := X.probability h P v
    have hQE : (X.law h P v).real {ω | X.answer P ω = v} ≤ δ := by
      rw [← wrong_safe_eq σ hσ hm hm2]
      exact ENNReal.toReal_le_of_le_ofReal hδ.le (hcorr v).2
    have hev := event_klDiv_ge (X.law h P w0) (X.law h P v) {ω | X.answer P ω = v}
      (hans (measurableSet_singleton v)) δ hδ hQE
    refine le_trans ?_ hev
    apply ENNReal.ofReal_le_ofReal
    have hdem := demand_of_small_delta m hm2 δ hδ hδ2 hδm
    have hlog : 0 ≤ Real.log (1 / δ) :=
      Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
    calc 1 / (4 * ((m : ℝ) - 1)) * Real.log (1 / δ)
        = Real.log (1 / δ) / (4 * ((m : ℝ) - 1)) := by ring
      _ ≤ (1 - δ) / ((m : ℝ) - 1) * Real.log (1 / δ) - Real.log 2 := hdem
      _ ≤ (X.law h P w0).real {ω | X.answer P ω = v} * Real.log (1 / δ) - Real.log 2 := by
          have := mul_le_mul_of_nonneg_right hpv hlog
          linarith
  stopped_information P _ w v _ :=
    kl_le_cost σ hσ hm h P w v _ fun q hq => chi_le_safe σ hσ hm h hh hh1 w v q hq

/-- The pair of worlds that only query `m - 1` separates. -/
def idW (hm : 0 < m) : Fin m := ⟨m - 1, by omega⟩
def idV (hm2 : 2 ≤ m) : Fin m := ⟨m - 2, by omega⟩

/-- **The identification lower certificate**, for every finite-horizon adaptive policy. -/
noncomputable def idLower (σ : ℝ) (hσ : 0 < σ) (hm : 0 < m) (hm2 : 2 ≤ m) (h δ : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hδ : 0 < δ) (hδ16 : δ ≤ 1 / 16) :
    HardPairCertificate (parExp σ hσ hm) .identify h δ
      (ENNReal.ofReal (aI m σ * h ^ (2 * (m - 1))))
      (ENNReal.ofReal ((1 / 4) * Real.log (1 / δ))) where
  hard w v := (w : ℕ) = m - 1 ∧ (v : ℕ) = m - 2
  find_pair P hP := by
    obtain ⟨hallow, hcorr⟩ := hP
    set X := parExp σ hσ hm with hX
    let w : Fin m := idW hm
    let v : Fin m := idV hm2
    have hwv : w ≠ v := by
      intro h'
      have := congrArg Fin.val h'
      simp [w, v, idW, idV] at this
      omega
    haveI := X.probability h P w
    haveI := X.probability h P v
    have hg : Measurable (X.guess P) := hallow.2.comp (measurable_restrictH m P.N)
    have hEm : MeasurableSet {ω | X.guess P ω = w} := hg (measurableSet_singleton w)
    -- at `v`, guessing `w` is wrong
    have hQE : (X.law h P v).real {ω | X.guess P ω = w} ≤ δ := by
      refine le_trans (measureReal_mono (fun ω hω => ?_)) (ENNReal.toReal_le_of_le_ofReal hδ.le
        (hcorr v).2)
      show X.guess P ω ≠ v
      rw [show X.guess P ω = w from hω]
      exact hwv
    -- at `w`, the guess is `w` with probability at least `1 - delta`
    have hPE : 1 - δ ≤ (X.law h P w).real {ω | X.guess P ω = w} := by
      have hc : (X.law h P w).real {ω | X.guess P ω = w}ᶜ ≤ δ :=
        ENNReal.toReal_le_of_le_ofReal hδ.le (hcorr w).2
      rw [probReal_compl_eq_one_sub hEm] at hc
      linarith
    refine ⟨w, v, ⟨rfl, rfl⟩, ?_⟩
    have hev := event_klDiv_ge (X.law h P w) (X.law h P v) {ω | X.guess P ω = w} hEm δ hδ hQE
    refine le_trans ?_ hev
    apply ENNReal.ofReal_le_ofReal
    have h16 : (16 : ℝ) ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
    have hL : 4 * Real.log 2 ≤ Real.log (1 / δ) := by
      have : Real.log 16 = 4 * Real.log 2 := by
        rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
      rw [← this]
      exact Real.log_le_log (by norm_num) h16
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hmul := mul_le_mul_of_nonneg_right hPE (by linarith : 0 ≤ Real.log (1 / δ))
    nlinarith
  stopped_information P _ w v hwv :=
    kl_le_cost σ hσ hm h P w v _ fun q hq =>
      chi_le_id σ hσ hm hm2 h hh hh1 w v q hwv.1 hwv.2 hq

#print axioms costAt_eq
#print axioms kl_le_cost
#print axioms chi_le_safe
#print axioms chi_le_id
#print axioms safeLower
#print axioms idLower

end CIGAMF.P13.PaperBParityExperiment
