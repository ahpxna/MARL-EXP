import Mathlib
import «LeanMarlRepairCalibrationV1»

/-!
# T2 debt: the `log |Amb|` gap, closed for fixed schedules

`LeanMarlRepairCalibrationV1` proves, on the needle class,

* a lower bound on the NULL-world expected cost of ANY adaptive protocol,
  `|Amb| · ((1−α) log(1/α) − log 2) ≤ E_0[cost] · β²/2` (`calibration_lower`), and
* an upper bound by a FIXED schedule of block tests,
  `cost ≤ |Amb| · ⌈8 log(|Amb|/α)/β²⌉` (`calibration_upper`).

The two differ by `log |Amb|`.  This file locates the factor.

## WHAT IS PROVED

* `own_world_lower` — the reverse change of measure: in the needle world `T`, the needle repair
  must be rolled out until `{out = T}` is unlikely at null level `δ`:
  `(1−α) log(1/δ) − log 2 ≤ E_T[N_T] · β²/2`.
* `null_mass_le` — the events `{out = T}`, `T ∈ Amb`, are disjoint and unacceptable at the null
  world, so their null probabilities sum to at most `α`.
* `log_sum_ge` — `Σ_i log(1/δ_i) ≥ M log(M/B)` when `Σ_i δ_i ≤ B` (via `log x ≤ x − 1`).
* `own_world_sum` — for ANY adaptive protocol,
  `|Amb| · ((1−α) log(|Amb|/(2α)) − log 2) ≤ (Σ_{T ∈ Amb} E_T[N_T]) · β²/2`.
  The `log |Amb|` factor is real, but it is paid in each needle world on that world's own needle.
* `sched_calibration_lower` — for a FIXED schedule the counts do not depend on the world, so
  the sum above is a cost: `|Amb| · ((1−α) log(|Amb|/(2α)) − log 2) ≤ cost · β²/2` in every
  world.
* `sched_upper` — `calibration_upper` restated with its schedule explicit, so that both bounds
  are about the same class.  Within fixed schedules, the optimal calibration cost is
  `Θ(|Amb| log(|Amb|/α) / β²)`: upper `≈ 8|Amb| log(|Amb|/α)/β²`, lower
  `≈ 2(1−α)|Amb| log(|Amb|/(2α))/β²`, a ratio tending to `4/(1−α)` as `|Amb|` grows.
* `sched_satisfiable` — on a concrete instance with `|Amb| ≥ 4`, the explicit schedule meets
  every hypothesis of `sched_calibration_lower` and the bound is strictly positive.

## WHAT THIS DOES NOT ESTABLISH

- For ADAPTIVE protocols, the proved lower bounds are `calibration_lower` (null world, no
  `log |Amb|`) and `own_world_sum` (one needle per world carries `log(|Amb|/α)`).  An adaptive
  protocol whose worst-world expected cost matches them up to constants (screen, then confirm
  only survivors) is NOT constructed here.  Whether adaptivity removes the factor is therefore
  a numerical observation, not a theorem: `scripts/MARL_E1a_two_stage.py` (exact error
  formulas, Monte-Carlo checked) finds a two-stage design whose worst-world expected cost is
  below `sched_calibration_lower` for `|Amb| ≥ 256` (α = 0.05) and `|Amb| ≥ 1024` (α = 0.01),
  and within 3.6× of `calibration_lower` for every tested `|Amb|` from 4 to 65536.
- Anything outside the needle class.
-/

namespace CIGAMF.P13.MarlCalibrationGap

open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperALowerKL CIGAMF.P13.PaperBPrivateQuery
open CIGAMF.P13.PaperBSchedule CIGAMF.P13.PaperBObstruction CIGAMF.P13.PaperBConcentration
open CIGAMF.P13.MarlSubsetFrontier CIGAMF.P13.MarlEstimatedRevision
open CIGAMF.P13.MarlRepairCalibration
open CIGAMF.P13.PaperBHellingerTest CIGAMF.P13.PaperABridge CIGAMF.P13.PaperAFamilyLower
open CIGAMF.P13.PaperAGaussianKL CIGAMF.P13.PaperAStrict

variable {m : ℕ}

/-! ## 1. The reverse change of measure -/

/-- **The needle world pays on its own needle.** -/
theorem own_world_lower (g : Fin m → ℝ) (P : Finset (Fin m)) (k R : ℕ) (β ε α : ℝ)
    (hP : P.card = k) (hTop : ∀ i ∈ P, ∀ j ∉ P, g j ≤ g i)
    (pol : Policy (Fin (NQ m))) (n : ℕ) (out : Hist (Fin (NQ m)) n → Finset (Fin m))
    (hmeas : ∀ S, MeasurableSet {ω | out ω = S})
    (T : Finset (Fin m)) (hT : T ∈ Amb g P k R β ε)
    (hcT : 1 - α ≤ (hist (rChan P) pol (needle β T) n).real
      {ω | Acc g P k R ε (needle β T) (out ω)})
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hl : (hist (rChan P) pol null0 n).real {ω | out ω = T} ≤ δ) :
    ENNReal.ofReal ((1 - α) * Real.log (1 / δ) - Real.log 2)
      ≤ (∫⁻ ω, cntQ (code T) n ω ∂hist (rChan P) pol (needle β T) n)
          * ENNReal.ofReal (β ^ 2 / 2) := by
  classical
  obtain ⟨_, hTP, _, _⟩ := mem_Amb.mp hT
  haveI := hist_prob (rChan P) pol (needle β T) n
  haveI := hist_prob (rChan P) pol null0 n
  have hsub : {ω | Acc g P k R ε (needle β T) (out ω)} ⊆ {ω | out ω = T} :=
    fun ω hω => acc_needle_unique g P k R β ε hP hTop T hT (out ω) hω
  have hθ : 1 - α ≤ (hist (rChan P) pol (needle β T) n).real {ω | out ω = T} :=
    hcT.trans (measureReal_mono hsub (measure_ne_top _ _))
  have hlog : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have hev := event_klDiv_ge (hist (rChan P) pol (needle β T) n) (hist (rChan P) pol null0 n)
    _ (hmeas T) δ hδ hl
  calc ENNReal.ofReal ((1 - α) * Real.log (1 / δ) - Real.log 2)
      ≤ ENNReal.ofReal ((hist (rChan P) pol (needle β T) n).real {ω | out ω = T}
          * Real.log (1 / δ) - Real.log 2) := by
        apply ENNReal.ofReal_le_ofReal
        have := mul_le_mul_of_nonneg_right hθ hlog
        linarith
    _ ≤ klDiv (hist (rChan P) pol (needle β T) n) (hist (rChan P) pol null0 n) := hev
    _ ≤ ∫⁻ ω, qsum (klq (rChan P) (needle β T) null0) n ω ∂hist (rChan P) pol (needle β T) n :=
        transcript_kl_le_qsum (rChan P) pol (needle β T) null0 n
    _ = ∑ q, (∫⁻ ω, cntQ q n ω ∂hist (rChan P) pol (needle β T) n)
          * klq (rChan P) (needle β T) null0 q := lintegral_qsum_eq _ _
    _ = (∫⁻ ω, cntQ (code T) n ω ∂hist (rChan P) pol (needle β T) n)
          * ENNReal.ofReal (β ^ 2 / 2) := by
        rw [Finset.sum_eq_single (code T)]
        · rw [klq_rChan, mz_null, mz_needle_self P T β hTP, sub_zero]
        · intro q _ hq
          rw [klq_rChan, mz_null]
          have : mz (code P) (needle β T) q = 0 := by simp [mz, needle, hq]
          rw [this]; simp
        · intro h; exact absurd (Finset.mem_univ _) h

/-! ## 2. The null world cannot afford many false alarms -/

/-- **The null masses of the ambiguous outputs sum to at most `α`.** -/
theorem null_mass_le (g : Fin m → ℝ) (P : Finset (Fin m)) (k R : ℕ) (β ε α : ℝ)
    (hP : P.card = k)
    (pol : Policy (Fin (NQ m))) (n : ℕ) (out : Hist (Fin (NQ m)) n → Finset (Fin m))
    (hmeas : ∀ S, MeasurableSet {ω | out ω = S})
    (h0 : 1 - α ≤ (hist (rChan P) pol null0 n).real {ω | Acc g P k R ε null0 (out ω)}) :
    ∑ T ∈ Amb g P k R β ε, (hist (rChan P) pol null0 n).real {ω | out ω = T} ≤ α := by
  classical
  haveI := hist_prob (rChan P) pol null0 n
  have hd : Set.PairwiseDisjoint (↑(Amb g P k R β ε))
      (fun T => {ω : Hist (Fin (NQ m)) n | out ω = T}) := by
    intro S _ T _ hST
    refine Set.disjoint_left.mpr fun ω h1 h2 => hST ?_
    have e1 : out ω = S := h1
    have e2 : out ω = T := h2
    exact e1.symm.trans e2
  rw [← measureReal_biUnion_finset hd (fun T _ => hmeas T)]
  have hsub : (⋃ T ∈ Amb g P k R β ε, {ω : Hist (Fin (NQ m)) n | out ω = T})
      ⊆ {ω | Acc g P k R ε null0 (out ω)}ᶜ := by
    intro ω hω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hω
    obtain ⟨T, hT, hoT⟩ := hω
    intro hA
    have hA' : Acc g P k R ε null0 (out ω) := hA
    rw [hoT] at hA'
    exact not_acc_null g P k R ε hP T (mem_Amb.mp hT).2.2.1 hA'
  have hAm : MeasurableSet {ω | Acc g P k R ε null0 (out ω)} :=
    measurableSet_out_mem n out hmeas {S | Acc g P k R ε null0 S}
  have := measureReal_mono hsub (measure_ne_top (hist (rChan P) pol null0 n) _)
  rw [measureReal_compl hAm, probReal_univ] at this
  linarith

/-! ## 3. Jensen, elementary form -/

theorem log_sum_ge {ι : Type*} (s : Finset ι) (δ : ι → ℝ) (hδ : ∀ i ∈ s, 0 < δ i) (B : ℝ)
    (hB : 0 < B) (hsum : ∑ i ∈ s, δ i ≤ B) :
    (s.card : ℝ) * Real.log (s.card / B) ≤ ∑ i ∈ s, Real.log (1 / δ i) := by
  classical
  rcases s.eq_empty_or_nonempty with hs | hs
  · simp [hs]
  have hM : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hMB : 0 < (s.card : ℝ) / B := div_pos hM hB
  have hpt : ∀ i ∈ s,
      Real.log (s.card / B) - ((s.card : ℝ) / B * δ i - 1) ≤ Real.log (1 / δ i) := by
    intro i hi
    have hx : 0 < (s.card : ℝ) / B * δ i := mul_pos hMB (hδ i hi)
    have h1 := Real.log_le_sub_one_of_pos hx
    have h2 : Real.log (1 / δ i) = Real.log (s.card / B) - Real.log (s.card / B * δ i) := by
      rw [Real.log_mul hMB.ne' (hδ i hi).ne', one_div, Real.log_inv]; ring
    linarith
  have hsum' := Finset.sum_le_sum hpt
  have hL : ∑ i ∈ s, (Real.log (s.card / B) - ((s.card : ℝ) / B * δ i - 1))
      = s.card * Real.log (s.card / B) - ((s.card : ℝ) / B * ∑ i ∈ s, δ i - s.card) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
      ← Finset.mul_sum, nsmul_eq_mul, nsmul_eq_mul, mul_one]
  have hcap : (s.card : ℝ) / B * ∑ i ∈ s, δ i ≤ s.card := by
    calc (s.card : ℝ) / B * ∑ i ∈ s, δ i ≤ s.card / B * B :=
          mul_le_mul_of_nonneg_left hsum hMB.le
      _ = s.card := by field_simp
  linarith

theorem ofReal_sum_le' {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ENNReal.ofReal (∑ i ∈ s, f i) ≤ ∑ i ∈ s, ENNReal.ofReal (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ENNReal.ofReal_add_le.trans (add_le_add le_rfl ih)

/-! ## 4. The own-world sum, for any adaptive protocol -/

/-- **`log |Amb|` is paid in the needle worlds.** -/
theorem own_world_sum (g : Fin m → ℝ) (P : Finset (Fin m)) (k R : ℕ) (β ε α : ℝ)
    (hP : P.card = k) (hTop : ∀ i ∈ P, ∀ j ∉ P, g j ≤ g i)
    (pol : Policy (Fin (NQ m))) (n : ℕ) (out : Hist (Fin (NQ m)) n → Finset (Fin m))
    (hmeas : ∀ S, MeasurableSet {ω | out ω = S}) (hα : 0 < α) (hα2 : α ≤ 1 / 2)
    (h0 : 1 - α ≤ (hist (rChan P) pol null0 n).real {ω | Acc g P k R ε null0 (out ω)})
    (hcorr : ∀ T ∈ Amb g P k R β ε, 1 - α ≤ (hist (rChan P) pol (needle β T) n).real
      {ω | Acc g P k R ε (needle β T) (out ω)}) :
    ((Amb g P k R β ε).card : ℝ≥0∞)
        * ENNReal.ofReal ((1 - α) * Real.log ((Amb g P k R β ε).card / (2 * α)) - Real.log 2)
      ≤ (∑ T ∈ Amb g P k R β ε, ∫⁻ ω, cntQ (code T) n ω ∂hist (rChan P) pol (needle β T) n)
          * ENNReal.ofReal (β ^ 2 / 2) := by
  classical
  set A := Amb g P k R β ε with hAdef
  rcases A.eq_empty_or_nonempty with hA0 | hAne
  · rw [hA0]; simp
  set M : ℝ := (A.card : ℝ) with hMdef
  have hM : (0 : ℝ) < M := by rw [hMdef]; exact_mod_cast hAne.card_pos
  have hM1 : (1 : ℝ) ≤ M := by rw [hMdef]; exact_mod_cast hAne.card_pos
  set a : Finset (Fin m) → ℝ := fun T => (hist (rChan P) pol null0 n).real {ω | out ω = T}
    with ha
  have ha0 : ∀ T, 0 ≤ a T := fun T => measureReal_nonneg
  have hasum : ∑ T ∈ A, a T ≤ α := null_mass_le g P k R β ε α hP pol n out hmeas h0
  set δ : Finset (Fin m) → ℝ := fun T => a T + α / M with hδdef
  have hαM : 0 < α / M := div_pos hα hM
  have hαM' : α / M ≤ α := div_le_self hα.le hM1
  have hδpos : ∀ T ∈ A, 0 < δ T := fun T _ => add_pos_of_nonneg_of_pos (ha0 T) hαM
  have hδ1 : ∀ T ∈ A, δ T ≤ 1 := by
    intro T hT
    have : a T ≤ α := (Finset.single_le_sum (fun S _ => ha0 S) hT).trans hasum
    show a T + α / M ≤ 1
    linarith
  have hδsum : ∑ T ∈ A, δ T ≤ 2 * α := by
    rw [hδdef, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← hMdef,
      mul_div_cancel₀ _ hM.ne']
    linarith
  set c := ENNReal.ofReal (β ^ 2 / 2) with hc
  set F : Finset (Fin m) → ℝ≥0∞ :=
    fun T => ∫⁻ ω, cntQ (code T) n ω ∂hist (rChan P) pol (needle β T) n with hF
  have hper : ∀ T ∈ A,
      ENNReal.ofReal ((1 - α) * Real.log (1 / δ T) - Real.log 2) ≤ F T * c := fun T hT =>
    own_world_lower g P k R β ε α hP hTop pol n out hmeas T hT (hcorr T hT) (δ T) (hδpos T hT)
      (hδ1 T hT) (by show a T ≤ a T + α / M; linarith)
  have hjen := log_sum_ge A δ hδpos (2 * α) (by linarith) hδsum
  have hreal : M * ((1 - α) * Real.log (M / (2 * α)) - Real.log 2)
      ≤ ∑ T ∈ A, ((1 - α) * Real.log (1 / δ T) - Real.log 2) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, ← hMdef]
    have h1α : 0 ≤ 1 - α := by linarith
    have := mul_le_mul_of_nonneg_left hjen h1α
    rw [← hMdef] at this
    nlinarith
  calc (A.card : ℝ≥0∞) * ENNReal.ofReal ((1 - α) * Real.log (A.card / (2 * α)) - Real.log 2)
      = ENNReal.ofReal (M * ((1 - α) * Real.log (M / (2 * α)) - Real.log 2)) := by
        rw [ENNReal.ofReal_mul hM.le, hMdef, ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (∑ T ∈ A, ((1 - α) * Real.log (1 / δ T) - Real.log 2)) :=
        ENNReal.ofReal_le_ofReal hreal
    _ ≤ ∑ T ∈ A, ENNReal.ofReal ((1 - α) * Real.log (1 / δ T) - Real.log 2) := ofReal_sum_le' _ _
    _ ≤ ∑ T ∈ A, F T * c := Finset.sum_le_sum hper
    _ = (∑ T ∈ A, F T) * c := (Finset.sum_mul _ _ _).symm

/-! ## 5. Fixed schedules: the sum is a cost -/

theorem lintegral_cntQ_sched (P : Finset (Fin m)) (s : ℕ → Fin (NQ m)) (w : Fin (NQ m) → ℝ)
    (n : ℕ) (q : Fin (NQ m)) :
    ∫⁻ ω, cntQ q n ω ∂hist (rChan P) (schedPolicy s) w n
      = ∑ i : Fin n, if s i = q then (1 : ℝ≥0∞) else 0 := by
  haveI := hist_prob (rChan P) (schedPolicy s) w n
  have hae : ∀ᵐ ω ∂hist (rChan P) (schedPolicy s) w n,
      cntQ q n ω = ∑ i : Fin n, if s i = q then (1 : ℝ≥0∞) else 0 := by
    filter_upwards [hist_sched_ae (rChan P) s w n] with ω hω
    unfold cntQ
    exact Finset.sum_congr rfl fun i _ => by rw [hω i]
  rw [lintegral_congr_ae hae, lintegral_const, measure_univ, mul_one]

/-- **Fixed schedules pay `log |Amb|` on every repair.** -/
theorem sched_calibration_lower (g : Fin m → ℝ) (P : Finset (Fin m)) (k R : ℕ) (β ε α : ℝ)
    (hP : P.card = k) (hTop : ∀ i ∈ P, ∀ j ∉ P, g j ≤ g i)
    (s : ℕ → Fin (NQ m)) (n : ℕ) (out : Hist (Fin (NQ m)) n → Finset (Fin m))
    (hmeas : ∀ S, MeasurableSet {ω | out ω = S}) (hα : 0 < α) (hα2 : α ≤ 1 / 2)
    (h0 : 1 - α ≤ (hist (rChan P) (schedPolicy s) null0 n).real
      {ω | Acc g P k R ε null0 (out ω)})
    (hcorr : ∀ T ∈ Amb g P k R β ε, 1 - α ≤ (hist (rChan P) (schedPolicy s) (needle β T) n).real
      {ω | Acc g P k R ε (needle β T) (out ω)}) (μ : Fin (NQ m) → ℝ) :
    ((Amb g P k R β ε).card : ℝ≥0∞)
        * ENNReal.ofReal ((1 - α) * Real.log ((Amb g P k R β ε).card / (2 * α)) - Real.log 2)
      ≤ costN (rChan P) (schedPolicy s) μ n * ENNReal.ofReal (β ^ 2 / 2) := by
  classical
  set A := Amb g P k R β ε with hAdef
  set K : Fin (NQ m) → ℝ≥0∞ := fun q => ∑ i : Fin n, if s i = q then (1 : ℝ≥0∞) else 0 with hK
  have hKw : ∀ w q, ∫⁻ ω, cntQ q n ω ∂hist (rChan P) (schedPolicy s) w n = K q :=
    fun w q => lintegral_cntQ_sched P s w n q
  have hsumK : ∑ T ∈ A, ∫⁻ ω, cntQ (code T) n ω ∂hist (rChan P) (schedPolicy s) (needle β T) n
      ≤ costN (rChan P) (schedPolicy s) μ n := by
    calc ∑ T ∈ A, ∫⁻ ω, cntQ (code T) n ω ∂hist (rChan P) (schedPolicy s) (needle β T) n
        = ∑ T ∈ A, K (code T) := Finset.sum_congr rfl fun T _ => hKw _ _
      _ = ∑ q ∈ A.image code, K q := by rw [Finset.sum_image (fun S _ T _ h => code_inj h)]
      _ ≤ ∑ q ∈ Finset.univ.filter (fun q => q ≠ code P), K q := by
          apply Finset.sum_le_sum_of_subset
          intro q hq
          obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          intro h; exact (mem_Amb.mp hT).2.1 (code_inj h)
      _ = costN (rChan P) (schedPolicy s) μ n := by
          rw [costN_eq_sum, rChan_dummy, Finset.sum_filter]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [hKw]
          by_cases h : q = code P <;> simp [h]
  exact (own_world_sum g P k R β ε α hP hTop (schedPolicy s) n out hmeas hα hα2 h0 hcorr).trans
    (mul_le_mul_of_nonneg_right hsumK bot_le)

/-- **`calibration_upper` with its schedule explicit.** -/
theorem sched_upper (g : Fin m → ℝ) (P : Finset (Fin m)) (k R : ℕ) (β ε α : ℝ)
    (hP : P.card = k) (hTop : ∀ i ∈ P, ∀ j ∉ P, g j ≤ g i) (hε : 0 ≤ ε) (hβ : 0 < β)
    (hα : 0 < α) (hSep : ∀ T, Reach P k R T → T ≠ P → ε < defc g P T) :
    ∃ (s : ℕ → Fin (NQ m)) (n : ℕ) (out : Hist (Fin (NQ m)) n → Finset (Fin m)),
      (∀ S, MeasurableSet {ω | out ω = S}) ∧
      1 - α ≤ (hist (rChan P) (schedPolicy s) null0 n).real {ω | Acc g P k R ε null0 (out ω)} ∧
      (∀ T, Reach P k R T → T ≠ P →
        1 - α ≤ (hist (rChan P) (schedPolicy s) (needle β T) n).real
          {ω | Acc g P k R ε (needle β T) (out ω)}) ∧
      ∀ μ, costN (rChan P) (schedPolicy s) μ n ≤
        (((Amb g P k R β ε).card *
          ⌈8 * Real.log ((Amb g P k R β ε).card / α) / β ^ 2⌉₊ : ℕ) : ℝ≥0∞) := by
  classical
  set A := Amb g P k R β ε with hAdef
  set nn := ⌈8 * Real.log (A.card / α) / β ^ 2⌉₊ with hnn
  have hA : ∀ T ∈ A, T ≠ P := fun T hT => (mem_Amb.mp hT).2.1
  have hn : 8 * Real.log (A.card / α) / β ^ 2 ≤ nn := Nat.le_ceil _
  have hbound := card_eB_le A.card β α hβ.ne' hα nn hn
  refine ⟨rsched P A nn, A.card * nn, rout P A β nn, measurableSet_rout P A β nn, ?_, ?_, ?_⟩
  · haveI := hist_prob (rChan P) (schedPolicy (rsched P A nn)) null0 (A.card * nn)
    refine real_ge_of_compl_le _ _ (measurableSet_out_mem _ _ (measurableSet_rout P A β nn)
      {S | Acc g P k R ε null0 S}) α hα.le ?_
    exact (err_zero_world P A β nn hA null0 (fun j => mz_null P _) _
      (acc_null_P g P k R ε hP hTop hε)).trans hbound
  · intro T hTr hTP
    haveI := hist_prob (rChan P) (schedPolicy (rsched P A nn)) (needle β T) (A.card * nn)
    refine real_ge_of_compl_le _ _ (measurableSet_out_mem _ _ (measurableSet_rout P A β nn)
      {S | Acc g P k R ε (needle β T) S}) α hα.le ?_
    by_cases hTA : T ∈ A
    · have he := enumA_equivFin A T hTA
      have herr := err_needle_world P A β nn hA (A.equivFin ⟨T, hTA⟩)
        (fun S => Acc g P k R ε (needle β T) S)
        (by rw [he]; exact acc_needle_self g P k R β ε hP hTop hε T hTA)
      rw [he] at herr
      exact herr.trans hbound
    · have hTd : β - ε ≤ defc g P T := by
        by_contra hlt
        push Not at hlt
        exact hTA (mem_Amb.mpr ⟨hTr, hTP, hSep T hTr hTP, hlt⟩)
      refine (err_zero_world P A β nn hA (needle β T) (fun j => ?_) _
        (acc_needle_P g P k R β ε hP hTop hε T hTP hTd)).trans hbound
      exact mz_needle_off P T (enumA A j) β (fun h => hTA (h ▸ enumA_mem A j))
  · intro μ
    rw [costN_sched]
    exact_mod_cast schedCost_le' (rsched P A nn) (rChan P).dummy (A.card * nn)

/-! ## 6. Satisfiability -/

theorem gapD_pos (M : ℝ) (hM : 1 ≤ M) :
    0 < (1 - 1 / 100 : ℝ) * Real.log (M / (2 * (1 / 100))) - Real.log 2 := by
  have h1 : (1 : ℝ) ≤ Real.log (M / (2 * (1 / 100))) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    have hM' : (50 : ℝ) ≤ M / (2 * (1 / 100)) := by
      rw [le_div_iff₀ (by norm_num)]; linarith
    linarith
  have h2 := Real.log_two_lt_d9
  norm_num at h1 h2 ⊢
  linarith

/-- **The fixed-schedule lower bound is not vacuous.**  On four messages with a two-message
prefix and one revision, `|Amb| ≥ 4`, the bound is strictly positive, and the explicit schedule
of `sched_upper` meets every hypothesis of `sched_calibration_lower`. -/
theorem sched_satisfiable :
    4 ≤ (Amb (gapGain ({0, 1} : Finset (Fin 4)) 1) {0, 1} 2 1 3 (1 / 2)).card ∧
    0 < (1 - 1 / 100 : ℝ) * Real.log
        ((Amb (gapGain ({0, 1} : Finset (Fin 4)) 1) {0, 1} 2 1 3 (1 / 2)).card / (2 * (1 / 100)))
        - Real.log 2 ∧
    ∃ (s : ℕ → Fin (NQ 4)) (n : ℕ) (out : Hist (Fin (NQ 4)) n → Finset (Fin 4)),
      (∀ S, MeasurableSet {ω | out ω = S}) ∧
      1 - 1 / 100 ≤ (hist (rChan {0, 1}) (schedPolicy s) null0 n).real
        {ω | Acc (gapGain {0, 1} 1) {0, 1} 2 1 (1 / 2) null0 (out ω)} ∧
      ∀ T ∈ Amb (gapGain ({0, 1} : Finset (Fin 4)) 1) {0, 1} 2 1 3 (1 / 2),
        1 - 1 / 100 ≤ (hist (rChan {0, 1}) (schedPolicy s) (needle 3 T) n).real
          {ω | Acc (gapGain {0, 1} 1) {0, 1} 2 1 (1 / 2) (needle 3 T) (out ω)} := by
  have hP : ({0, 1} : Finset (Fin 4)).card = 2 := by decide
  have h4 : 4 ≤ (Amb (gapGain ({0, 1} : Finset (Fin 4)) 1) {0, 1} 2 1 3 (1 / 2)).card := by
    have := amb_card_ge_gap ({0, 1} : Finset (Fin 4)) 2 1 3 (1 / 2) 1 hP le_rfl (by norm_num)
      (by norm_num) (by norm_num)
    simpa using this
  refine ⟨h4, gapD_pos _ (by exact_mod_cast (by omega : 1 ≤ _)), ?_⟩
  obtain ⟨s, n, out, hm, h0, hT, _⟩ := sched_upper (gapGain ({0, 1} : Finset (Fin 4)) 1)
    {0, 1} 2 1 3 (1 / 2) (1 / 100) hP (gap_top _ 1 (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (gap_sep _ 2 1 (1 / 2) 1 hP (by norm_num) (by norm_num))
  exact ⟨s, n, out, hm, h0, fun T hTA => hT T (mem_Amb.mp hTA).1 (mem_Amb.mp hTA).2.1⟩

end CIGAMF.P13.MarlCalibrationGap

#print axioms CIGAMF.P13.MarlCalibrationGap.own_world_lower
#print axioms CIGAMF.P13.MarlCalibrationGap.null_mass_le
#print axioms CIGAMF.P13.MarlCalibrationGap.log_sum_ge
#print axioms CIGAMF.P13.MarlCalibrationGap.own_world_sum
#print axioms CIGAMF.P13.MarlCalibrationGap.lintegral_cntQ_sched
#print axioms CIGAMF.P13.MarlCalibrationGap.sched_calibration_lower
#print axioms CIGAMF.P13.MarlCalibrationGap.sched_upper
#print axioms CIGAMF.P13.MarlCalibrationGap.sched_satisfiable
