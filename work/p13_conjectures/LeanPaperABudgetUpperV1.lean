import «LeanPaperA6OracleLearnerV1»
import «LeanPaperA7StoppedGenV1»
import «LeanPaperA7IdealUpperV1»

/-!
# Paper A: the budget frontier is attained — the upper rate of a tracking learner

The lower half of the repair law (`LeanPaperAPolicyClassesV1`) says that every δ-correct policy
whose design meets the sacrifice budget pays `E N ≥ D_δ / R(b)`. This module proves the upper
half. A design within the budget is **attained at its own information rate** by the tracking
learner of Paper A6 with the GLR stop.

**The learner.** `oLearner O` (`LeanPaperA6OracleLearnerV1`) tracks an oracle `O` of the
estimate. It has warm start, forcing `1/√(s+1)` toward uniform, post-warm quota, and the first
maximiser of `W - N`. `tauG` is the GLR stop of `LeanPaperA7StoppedGenV1`.

**What is proved, for any oracle.**
* `oracle_direct`: suppose that on the confidence event the oracle's design eventually carries
  true information at least `Γ - η/4`. Then on the good window the stopping statistic of the
  true answer is at least `(Γ - η) t` for all large `t`.
* `oracle_expect_bound`: `E τ_δ ≤ log(1/δ)/(Γ - η) + A_η` for every `δ ∈ (0,1)`, with `E τ_δ`
  finite.
* `oracle_correct`: a wrong answer has probability at most `(|Ans| - 1) δ` (from `correctG`,
  for every allocation rule).

**The fixed design** (`constO w`: the oracle ignores the estimate and returns `w`).
* `fix_expect_bound`, `fix_upper_rate`: `E τ_δ ≤ log(1/δ)/(J(w) - η) + A_η`, where `J(w)` is the
  true game at `w` in unit-variance coordinates. So `limsup E τ_δ / log(1/δ) ≤ 1/J(w)`.
* `fix_design_floor`: for every `ε > 0` there is a deterministic `T` such that, at every
  `t ≥ T` and on every path, the realised design dominates `(1 - ε) w` cellwise.
* `Jval_ge_scale`: a game value is monotone and homogeneous in the design.
* `fix_budget_eventually`: hence the realised design's surrogate information converges to that
  of `w` uniformly in `ω`. If `s(w) < b` for the sacrifice `s = 1 - J_f/Γ_f` of any frozen
  game, the realised design is within the budget `b` at every `t ≥ t₀`, on every path. This is
  the eventual class of `LeanPaperAPolicyClassesV1`, stated on the stream.

SCOPE. `w` is a design of the true world. When `w` is chosen as a maximiser of the budgeted
game at `θ`, it is an oracle design (the policy is tuned to `θ`, as in the definition of the
optimal cost `inf_π E_θ τ`). δ-correctness holds at every world regardless, because the stop
reads only the history.
-/

namespace CIGAMF.P13.PaperABudgetUpper

open Finset MeasureTheory Filter Topology
open scoped ENNReal
open CIGAMF.P13.PaperA7Stream CIGAMF.P13.PaperA7Process CIGAMF.P13.PaperA7Confidence
open CIGAMF.P13.PaperA7Correct CIGAMF.P13.PaperA7IdealLearner CIGAMF.P13.PaperA7IdealStop
open CIGAMF.P13.PaperA7IdealRun CIGAMF.P13.PaperA7IdealSelect CIGAMF.P13.PaperA7DirectLower
open CIGAMF.P13.PaperA7OracleSelect CIGAMF.P13.PaperA7Asym CIGAMF.P13.PaperA7IdealBounds
open CIGAMF.P13.PaperA7DirectFree CIGAMF.P13.PaperA7FreeAccum CIGAMF.P13.PaperA7GLRMeas
open CIGAMF.P13.PaperA7IdealDirect CIGAMF.P13.PaperA7IdealDirect2 CIGAMF.P13.PaperA7WarmTrack
open CIGAMF.P13.PaperA7UpperChain CIGAMF.P13.PaperAStopping CIGAMF.P13.PaperA7IdealUpper
open CIGAMF.P13.PaperA6OracleLearner CIGAMF.P13.PaperA7StoppedGen

variable {E : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [Nonempty E]
variable {Ans : Type*} [Fintype Ans] [DecidableEq Ans] [Nonempty Ans]
variable (P : Spec E Ans) (O : Oracle E)

/-! ## 1. The run of the oracle learner -/

/-- The confidence event at time `s`, at the true world. -/
def GoodAtO (a : ℝ) (θ : E → ℝ) (s : ℕ) (ω : ℕ → ℝ) : Prop :=
  PaperA7Stream.Qstat a P.σ (Nc (oLearner O) θ P.σ s ω) (muHat (oLearner O) θ P.σ s ω) θ
    ≤ bthr a ((s : ℝ) ^ 4)⁻¹ (Nc (oLearner O) θ P.σ s ω)

/-- The good window ending at `t`. -/
def GoodWinO (a : ℝ) (θ : E → ℝ) (t : ℕ) : Set (ℕ → ℝ) :=
  {ω | ∀ s, Nat.sqrt t ≤ s → s ≤ t → GoodAtO P O a θ s ω}

theorem o_count_le (θ : E → ℝ) (ω : ℕ → ℝ) (t : ℕ) (e : E) :
    Nc (oLearner O) θ P.σ t ω e ≤ t := by
  unfold Nc NF
  have : ∑ i : Fin t, (if (histF (oLearner O) θ P.σ t (Xp t ω) i).1 = e then (1 : ℕ) else 0)
      ≤ ∑ _i : Fin t, (1 : ℕ) := sum_le_sum fun i _ => by split_ifs <;> norm_num
  rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at this
  exact_mod_cast this

/-- **Every count is eventually large.** -/
theorem o_count_floor (a : ℝ) (ha : 0 < a) (θ : E → ℝ) :
    ∃ S : ℕ, Fintype.card E ≤ S ∧ ∀ s, S ≤ s → ∀ ω e,
      max a 1 ≤ Real.sqrt s / (2 * Fintype.card E) ∧
      Real.sqrt s / (2 * Fintype.card E) ≤ Nc (oLearner O) θ P.σ s ω e := by
  set K : ℝ := (Fintype.card E : ℝ) with hKdef
  have hK : 1 ≤ K := by rw [hKdef]; exact_mod_cast Fintype.card_pos
  obtain ⟨S1, hS1⟩ := eventually_inv_sqrt (2 * K * (K - 1 + max a 1)) 1 (by
    have : 0 ≤ K - 1 := by linarith
    have : 0 < max a 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    positivity) one_pos
  refine ⟨max S1 (Fintype.card E), le_max_right _ _, fun s hs ω e => ?_⟩
  have hsK : Fintype.card E ≤ s := le_trans (le_max_right _ _) hs
  have h1 := hS1 s (le_trans (le_max_left _ _) hs)
  have hs1 : (1 : ℝ) ≤ s := by
    have : 1 ≤ s := le_trans Fintype.card_pos hsK
    exact_mod_cast this
  have hsq : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.mpr (by linarith)
  rw [div_le_one hsq] at h1
  have hmx : 0 < max a 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  constructor
  · rw [le_div_iff₀ (by positivity)]
    nlinarith
  · have hc := oCount_ge O θ P.σ ω (s - Fintype.card E) e
    rw [show Fintype.card E + (s - Fintype.card E) = s by omega] at hc
    have hA : 2 * K * (K - 1) ≤ Real.sqrt s := by
      have : 2 * K * (K - 1) ≤ 2 * K * (K - 1 + max a 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    have hB : K - 1 ≤ Real.sqrt s / (2 * K) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have hC : Real.sqrt s / K - Real.sqrt s / (2 * K) = Real.sqrt s / (2 * K) := by
      field_simp; ring
    have : Real.sqrt s / (2 * K) ≤ Real.sqrt s / K - (K - 1) := by linarith
    linarith

theorem o_hpost (θ : E → ℝ) (ω : ℕ → ℝ) (k : ℕ) (e : E) :
    PaperA7Accumulation.target (fun s => O.D (hMu (oRun O θ P.σ s ω))) (rho (E := E)) unif
        (Fintype.card E + k) e = (oWarmRun O θ P.σ ω).v (k + 1) e := by
  show _ = ovRun O θ P.σ ω (k + 1) e
  unfold ovRun
  rw [show Fintype.card E + (k + 1 - 1) = Fintype.card E + k by omega]
  rfl

/-- **Tracking of the run.** -/
theorem o_track (θ : E → ℝ) (ω : ℕ → ℝ) (k : ℕ) :
    ∑ e, |Nc (oLearner O) θ P.σ (Fintype.card E + k) ω e / ((Fintype.card E + k : ℕ) : ℝ)
        - PaperA7Accumulation.avgTarget (fun s => O.D (hMu (oRun O θ P.σ s ω))) (rho (E := E))
            unif (Fintype.card E + k) e|
      ≤ 2 * ((Fintype.card E : ℝ) - 1) / ((Fintype.card E + k : ℕ) : ℝ) :=
  warm_htrack (oWarmRun O θ P.σ ω) _ (rho (E := E)) unif (fun e => rfl) rho_warm
    (o_hpost P O θ ω) k

/-- **The raw mean's radius on the good event.** -/
theorem o_radius_run (a : ℝ) (ha : 0 < a) (θ : E → ℝ) (s : ℕ) (ω : ℕ → ℝ) (b : ℝ) (hb0 : 0 ≤ b)
    (hgood : PaperA7Stream.Qstat a P.σ (Nc (oLearner O) θ P.σ s ω)
      (muHat (oLearner O) θ P.σ s ω) θ ≤ b)
    (Nmin : ℝ) (haN : a ≤ Nmin) (hN : ∀ e, Nmin ≤ Nc (oLearner O) θ P.σ s ω e) (e : E) :
    |muHat (oLearner O) θ P.σ s ω e - θ e| ≤ 2 * smax P * Real.sqrt (b / Nmin) := by
  have hNmin : 0 < Nmin := lt_of_lt_of_le ha haN
  rw [qstat_truth_eq (oLearner O) θ P.σ a P.σ_pos s ω] at hgood
  have hNe : 0 < NF (oLearner O) θ P.σ s (Xp s ω) e := by
    have := lt_of_lt_of_le hNmin (hN e)
    unfold Nc at this
    exact_mod_cast this
  have hr := radius_of_good (oLearner O) θ P.σ a ha P.σ_pos s (Xp s ω) b hgood e hNe
  set N := (NF (oLearner O) θ P.σ s (Xp s ω) e : ℝ) with hNdef
  have hNc : Nc (oLearner O) θ P.σ s ω e = N := rfl
  have hN0 : (0 : ℝ) < N := by rw [hNdef]; exact_mod_cast hNe
  have hNge : Nmin ≤ N := hNc ▸ hN e
  have hmu : muHat (oLearner O) θ P.σ s ω e = Ysum (oLearner O) θ P.σ s (Xp s ω) e / N := rfl
  rw [hmu]
  refine le_trans hr ?_
  have h1 : Real.sqrt (2 * (a + N) * b) ≤ Real.sqrt (4 * N * b) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have h2 : Real.sqrt (4 * N * b) / N = 2 * Real.sqrt (b / N) := by
    rw [show 4 * N * b = 2 ^ 2 * (N * b) by ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num), Real.sqrt_mul hN0.le, Real.sqrt_div' _ hN0.le]
    field_simp
    rw [Real.sq_sqrt hN0.le]
    try ring
  have h3 : Real.sqrt (b / N) ≤ Real.sqrt (b / Nmin) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hb0 hNmin hNge)
  have hσe := le_smax P e
  have hσ0 := P.σ_pos e
  calc P.σ e * Real.sqrt (2 * (a + N) * b) / N
      ≤ P.σ e * Real.sqrt (4 * N * b) / N := by
        apply div_le_div_of_nonneg_right _ hN0.le
        exact mul_le_mul_of_nonneg_left h1 hσ0.le
    _ = P.σ e * (2 * Real.sqrt (b / N)) := by rw [mul_div_assoc, h2]
    _ ≤ smax P * (2 * Real.sqrt (b / Nmin)) := by
        apply mul_le_mul hσe (by linarith) (by positivity) (by linarith)
    _ = 2 * smax P * Real.sqrt (b / Nmin) := by ring

/-! ## 2. The direct lower bound on the statistic -/

theorem hN_oRunG (θ : E → ℝ) (t : ℕ) (ω : ℕ → ℝ) :
    hN (runG P (oLearner O) θ t ω) = Nc (oLearner O) θ P.σ t ω := hN_runG P (oLearner O) θ t ω

/-- **The direct lower bound for any oracle that is eventually informative on the good
event.** -/
theorem oracle_direct (a : ℝ) (ha : 0 < a) (Tst : Ans) (θ : E → ℝ) (Γ : ℝ) (hΓ : 0 < Γ)
    (hΓle : Γ ≤ GamT P Tst θ)
    (hround : ∀ η, 0 < η → ∃ S : ℕ, ∀ s, S ≤ s → ∀ ω, GoodAtO P O a θ s ω →
      Γ - η / 4 ≤ Jval (sc P.σ '' P.Alt Tst) (O.D (hMu (runG P (oLearner O) θ s ω))) (sc P.σ θ))
    (η : ℝ) (hη : 0 < η) :
    ∃ T0 : ℕ, ∀ t : ℕ, T0 ≤ t → ∀ ω ∈ GoodWinO P O a θ t,
      (Γ - η) * t ≤ Zh P a Tst (runG P (oLearner O) θ t ω) := by
  have hZ0 : ∀ t ω, 0 ≤ Zh P a Tst (runG P (oLearner O) θ t ω) := by
    intro t ω
    unfold Zh glr
    exact le_csInf ((P.Alt_ne Tst).image _) (by
      rintro _ ⟨l, -, rfl⟩; exact qAbs_nonneg a ha P.σ _ l)
  rcases le_or_gt Γ η with hηΓ | hηΓ
  · refine ⟨0, fun t _ ω _ => le_trans ?_ (hZ0 t ω)⟩
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg t)
  set K : ℝ := (Fintype.card E : ℝ) with hKdef
  have hK : 1 ≤ K := by rw [hKdef]; exact_mod_cast Fintype.card_pos
  obtain ⟨ν0, hν0⟩ := P.Alt_ne Tst
  set U := Ubd P Tst θ ν0 with hUdef
  have hGU : GamT P Tst θ ≤ U := GamT_le P Tst θ ν0 hν0 θ fun e => by simp
  have hΓU : Γ ≤ U := hΓle.trans hGU
  have hU0 : 0 < U := lt_of_lt_of_le hΓ hΓU
  set C := C1 (Fintype.card E) a
  have hC : 0 ≤ C := C1_nonneg _ _ (Nat.cast_nonneg _)
  set ε1 := η / (8 * (Γ + 1)) with hε1
  have hε1pos : 0 < ε1 := by positivity
  obtain ⟨S, hS⟩ := hround η hη
  obtain ⟨Sc, hScK, hSc⟩ := o_count_floor P O a ha θ
  obtain ⟨T1, hT1⟩ := eventually_inv (Γ * K) (η / 16) (by positivity) (by positivity)
  obtain ⟨T2, hT2⟩ := eventually_inv_sqrt (3 * Γ) (η / 16) (by positivity) (by positivity)
  obtain ⟨T3, hT3⟩ := eventually_inv_sqrt (2 * K * a) ε1 (by positivity) hε1pos
  obtain ⟨T4, hT4⟩ := eventually_inv_sqrt (2 * K * (K - 1)) ε1
    (by have : 0 ≤ K - 1 := by linarith
        positivity) hε1pos
  obtain ⟨T5, hT5⟩ := eventually_inv_sqrt_sqrt (2 * Real.sqrt C * Real.sqrt (2 * U)) (η / 16)
    (by positivity) (by positivity)
  refine ⟨max (max (max (S * S) Sc) (max T1 T2)) (max (max T3 T4) T5), fun t ht ω hω => ?_⟩
  have htS : S * S ≤ t := by omega
  have htSc : Sc ≤ t := by omega
  have htK : Fintype.card E ≤ t := le_trans hScK htSc
  have hn : S ≤ Nat.sqrt t := Nat.le_sqrt.mpr htS
  have ht1' : 1 ≤ t := le_trans Fintype.card_pos htK
  have htR1 : (1 : ℝ) ≤ t := by exact_mod_cast ht1'
  have htR : (0 : ℝ) < t := by linarith
  have ht0 : 0 < t := by omega
  set n := Nat.sqrt t with hndef
  have hnt : n ≤ t := Nat.sqrt_le_self t
  have hgood : ∀ s, n ≤ s → s < t → Γ - η / 4
      ≤ Jval (sc P.σ '' P.Alt Tst) (O.D (hMu (runG P (oLearner O) θ s ω))) (sc P.σ θ) :=
    fun s hns hst => hS s (le_trans hn hns) ω (hω s hns hst.le)
  obtain ⟨hmx, -⟩ := hSc t htSc ω (Classical.arbitrary E)
  have hNall : ∀ e, Real.sqrt t / (2 * K) ≤ Nc (oLearner O) θ P.σ t ω e :=
    fun e => (hSc t htSc ω e).2
  set Nmin := Real.sqrt t / (2 * K) with hNmin
  have haN : a ≤ Nmin := le_trans (le_max_left _ _) hmx
  have hNmin0 : 0 < Nmin := lt_of_lt_of_le ha haN
  set w : ℕ → E → ℝ := fun s => O.D (hMu (runG P (oLearner O) θ s ω)) with hw
  have hwalloc : ∀ s, IsAlloc (w s) := fun s => O.alloc _
  have hρ : ∀ s, 0 ≤ rho (E := E) s ∧ rho (E := E) s ≤ 1 := by
    intro s
    unfold rho
    split_ifs
    · exact ⟨zero_le_one, le_rfl⟩
    · refine ⟨by positivity, ?_⟩
      rw [div_le_one (Real.sqrt_pos.mpr (by positivity))]
      exact Real.one_le_sqrt.mpr (by linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)])
  have hsqt : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.mpr htR
  have htt : Real.sqrt (t : ℝ) * Real.sqrt t = t := Real.mul_self_sqrt htR.le
  have htrack0 := o_track P O θ ω (t - Fintype.card E)
  rw [show Fintype.card E + (t - Fintype.card E) = t by omega] at htrack0
  have hfloor : ∀ e, 1 / (K * Real.sqrt t) ≤
      PaperA7Accumulation.avgTarget w (rho (E := E)) unif t e :=
    fun e => avgTarget_floor w (fun s e => (hwalloc s).1 e) rho (fun s => (hρ s).2)
      (fun s => by
        unfold rho
        split_ifs
        · rw [div_le_one (Real.sqrt_pos.mpr (by positivity))]
          exact Real.one_le_sqrt.mpr (by linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)])
        · exact le_rfl) unif (fun e => rfl) t ht0 e
  have hmult := mult_of_additive (fun e => Nc (oLearner O) θ P.σ t ω e)
    (PaperA7Accumulation.avgTarget w (rho (E := E)) unif t) (t : ℝ)
    (2 * ((Fintype.card E : ℝ) - 1)) (1 / (K * Real.sqrt t)) htR (by positivity) (by linarith)
    hfloor htrack0
  set ε := 2 * ((Fintype.card E : ℝ) - 1) / ((t : ℝ) * (1 / (K * Real.sqrt t))) with hεdef
  have hden : (t : ℝ) * (1 / (K * Real.sqrt t)) = Real.sqrt t / K := by
    calc (t : ℝ) * (1 / (K * Real.sqrt t))
        = (Real.sqrt t * Real.sqrt t) * (1 / (K * Real.sqrt t)) := by rw [htt]
      _ = Real.sqrt t / K := by field_simp
  have hεeq : ε = 2 * K * (K - 1) / Real.sqrt t := by
    rw [hεdef, hden]
    field_simp
    ring
  have hK1 : 0 ≤ K - 1 := by linarith
  have hε0 : 0 ≤ ε := by
    rw [hεeq]
    exact div_nonneg (mul_nonneg (by positivity) hK1) (Real.sqrt_nonneg _)
  have hεle : ε ≤ ε1 := by rw [hεeq]; exact hT4 t (by omega)
  have hε1le : ε1 ≤ 1 := by
    rw [hε1, div_le_one (by positivity)]; nlinarith
  have hNsum : ∑ e, Nc (oLearner O) θ P.σ t ω e = t := by
    have := (oWarmRun O θ P.σ ω).N_sum (t - Fintype.card E)
    have h2 : ∑ e, (oWarmRun O θ P.σ ω).N (t - Fintype.card E) e
        = ∑ e, Nc (oLearner O) θ P.σ t ω e := by
      refine sum_congr rfl fun e _ => ?_
      show Nc (oLearner O) θ P.σ (Fintype.card E + (t - Fintype.card E)) ω e = _
      rw [show Fintype.card E + (t - Fintype.card E) = t by omega]
    rw [h2] at this
    rw [this]; push_cast [Nat.cast_sub htK]; ring
  have hNalloc : IsAlloc (fun e => Nc (oLearner O) θ P.σ t ω e / t) := by
    refine ⟨fun e => div_nonneg (Nat.cast_nonneg _) htR.le, ?_⟩
    rw [← sum_div, hNsum, div_self htR.ne']
  have hU : Jval (sc P.σ '' P.Alt Tst) (fun e => Nc (oLearner O) θ P.σ t ω e / t) (sc P.σ θ)
      ≤ U := le_trans ((GamT_isLUB P Tst θ).1 ⟨_, hNalloc, rfl⟩) hGU
  have hconf := hω t hnt le_rfl
  set b := bthr a ((t : ℝ) ^ 4)⁻¹ (Nc (oLearner O) θ P.σ t ω) with hb
  have hb0 : 0 ≤ b := bthr_nonneg a ha _ (by positivity)
    (inv_le_one_of_one_le₀ (one_le_pow₀ htR1)) _ fun e => Nat.cast_nonneg _
  have hsolver : sInf ((fun l => PaperA7Stream.Qstat a P.σ (Nc (oLearner O) θ P.σ t ω)
      (muHat (oLearner O) θ P.σ t ω) l) '' P.Alt Tst) - t * 0
      ≤ Zh P a Tst (runG P (oLearner O) θ t ω) := by
    rw [mul_zero, sub_zero]
    show _ ≤ glr a P.σ (P.Alt Tst) (hN (runG P (oLearner O) θ t ω), hMu (runG P (oLearner O) θ t ω))
    rw [hN_runG, hMu_runG, (glr_run_measurable (oLearner O) θ P.σ a ha
      (fun e => (P.σ_pos e).ne') (P.Alt Tst) (P.Alt_ne Tst) t).2 ω]
  have hD := direct_lower_free a ha (P.Alt Tst) (P.Alt_ne Tst) P.σ P.σ_pos θ
    (muHat (oLearner O) θ P.σ t ω) Γ n t hnt ht0 w hwalloc rho hρ unif unif_alloc
    (fun _ => η / 4) hgood (fun e => Nc (oLearner O) θ P.σ t ω e) ε hε0
    (le_trans hεle hε1le) hmult Nmin haN hNall U hU b hb0 hconf
    (Zh P a Tst (runG P (oLearner O) θ t ω)) 0 hsolver
  have hacc := acc_lower Γ (η / 4) (by positivity) (by linarith) hΓ.le n t hnt ht0 rho hρ
    (K + 2 * Real.sqrt t) (sum_rho_le t)
  have hn_le : (n : ℝ) ≤ Real.sqrt t := Real.nat_sqrt_le_real_sqrt
  have hAcc : Γ - 3 * η / 8 ≤
      (1 / (t : ℝ)) * ∑ s ∈ Ico n t, (1 - rho (E := E) s) * (Γ - η / 4) :=
    acc_budget Γ η K (Real.sqrt t) t n _ hΓ hsqt htt hn_le hacc (hT1 t (by omega))
      (hT2 t (by omega))
  have hcr : 1 - ε1 ≤ 1 - a / Nmin := by
    have h3 : 2 * K * a / Real.sqrt t ≤ ε1 := hT3 t (by omega)
    have : a / Nmin = 2 * K * a / Real.sqrt t := by
      rw [hNmin]; exact ridge_eq a _ K hsqt (by linarith)
    linarith
  have hcr1 : 1 - a / Nmin ≤ 1 := by have := div_nonneg ha.le hNmin0.le; linarith
  have he : 1 - ε1 ≤ 1 - ε := by linarith
  have haN1 : a / Nmin ≤ 1 := (div_le_one hNmin0).mpr haN
  have hbC : b ≤ C * Real.sqrt t :=
    le_trans (bthr_le a ha t ht1' _ (fun e => Nat.cast_nonneg _) (o_count_le P O θ ω t))
      (mul_le_mul_of_nonneg_left (sqrt_sqrt_le_sqrt t htR1) hC)
  have hss : Real.sqrt (Real.sqrt t) * Real.sqrt (Real.sqrt t) = Real.sqrt t :=
    Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have hssp : 0 < Real.sqrt (Real.sqrt (t : ℝ)) := Real.sqrt_pos.mpr hsqt
  have hRt : Real.sqrt (2 * (1 + a / Nmin) * b) * Real.sqrt (2 * U) / Real.sqrt t ≤ η / 16 :=
    radius_budget (a / Nmin) b C (Real.sqrt t) (Real.sqrt (Real.sqrt t)) U η
      haN1 hb0 hC hbC hssp hss (hT5 t (by omega))
  have hfin := budget Γ η (1 - a / Nmin) (1 - ε)
    ((1 / (t : ℝ)) * ∑ s ∈ Ico n t, (1 - rho (E := E) s) * (Γ - η / 4))
    (Real.sqrt (2 * (1 + a / Nmin) * b) * Real.sqrt (2 * U) / Real.sqrt t)
    hΓ hη hηΓ hcr hcr1 he (by linarith) hAcc (by positivity) hRt
  have hfin2 : Γ - η ≤ Zh P a Tst (runG P (oLearner O) θ t ω) / t := by
    refine le_trans hfin ?_
    have := hD
    rw [sub_zero] at this
    exact this
  rw [le_div_iff₀ htR] at hfin2
  exact hfin2

/-! ## 3. The expected stopping time -/

/-- **The window failure probability** at the truth. -/
theorem o_goodWin_compl_le (a : ℝ) (ha : 0 < a) (θ : E → ℝ) (t : ℕ) (ht : 1 ≤ t) :
    streamMeasure (GoodWinO P O a θ t)ᶜ ≤ ENNReal.ofReal (16 * (1 / (t : ℝ) ^ 2)) := by
  have hn : 1 ≤ Nat.sqrt t := Nat.sqrt_pos.mpr ht
  have hsub : (GoodWinO P O a θ t)ᶜ ⊆ {ω | ∃ j, Nat.sqrt t ≤ j ∧ j ≤ t ∧
      bthr a ((j : ℝ) ^ 4)⁻¹ (Nc (oLearner O) θ P.σ j ω)
        < PaperA7Confidence.Qstat a (Sc (oLearner O) θ P.σ j ω)
            (Nc (oLearner O) θ P.σ j ω)} := by
    intro ω hω
    simp only [GoodWinO, GoodAtO, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_le] at hω
    obtain ⟨j, hnj, hjt, hj⟩ := hω
    refine ⟨j, hnj, hjt, ?_⟩
    rw [← qstat_truth_eq (oLearner O) θ P.σ a P.σ_pos j ω]
    exact hj
  have hreal := good_window_real (oLearner O) θ P.σ a ha (Nat.sqrt t) t hn
  refine le_trans (measure_mono hsub) ?_
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  exact le_trans (ENNReal.ofReal_le_ofReal hreal) (ENNReal.ofReal_le_ofReal (inv_sqrt_pow4_le t ht))

/-- **The expected stopping time of the oracle learner.** -/
theorem oracle_expect_bound (a : ℝ) (ha : 0 < a) (Tst : Ans) (θ : E → ℝ) (Γ : ℝ) (hΓ : 0 < Γ)
    (hΓle : Γ ≤ GamT P Tst θ)
    (hround : ∀ η, 0 < η → ∃ S : ℕ, ∀ s, S ≤ s → ∀ ω, GoodAtO P O a θ s ω →
      Γ - η / 4 ≤ Jval (sc P.σ '' P.Alt Tst) (O.D (hMu (runG P (oLearner O) θ s ω))) (sc P.σ θ))
    (η : ℝ) (hη : 0 < η) (hηΓ : η < Γ) :
    ∃ A : ℝ, ∀ δ, 0 < δ → δ < 1 →
      (∫⁻ ω, (tauG P a δ (oLearner O) θ ω).toENNReal ∂streamMeasure) ≠ ⊤ ∧
      (∫⁻ ω, (tauG P a δ (oLearner O) θ ω).toENNReal ∂streamMeasure).toReal
        ≤ Real.log (1 / δ) / (Γ - η) + A := by
  set K : ℝ := (Fintype.card E : ℝ) with hKdef
  have hK : 0 < K := by rw [hKdef]; exact_mod_cast Fintype.card_pos
  set κ := η / (2 * Γ) with hκ
  have hκ0 : 0 < κ := by positivity
  have hκ1 : κ < 1 := by rw [hκ, div_lt_one (by positivity)]; linarith
  set Gm := Γ - η / 2 with hGm
  have hGm0 : 0 < Gm := by linarith
  have hden : Γ - η ≤ (1 - κ) * Gm := by
    rw [hκ, hGm]
    have h : (1 - η / (2 * Γ)) * (Γ - η / 2) = Γ - η + η ^ 2 / (4 * Γ) := by
      field_simp; ring
    rw [h]
    have : 0 ≤ η ^ 2 / (4 * Γ) := by positivity
    linarith
  have hdenpos : 0 < (1 - κ) * Gm := mul_pos (by linarith) hGm0
  obtain ⟨T0, hT0⟩ := oracle_direct P O a ha Tst θ Γ hΓ hΓle hround (η / 2) (by positivity)
  set T0' := max T0 (Fintype.card E) with hT0'
  set f : ℕ → ℝ := fun t => 16 * (1 / (t : ℝ) ^ 2) with hf
  have hf0 : ∀ t, 0 ≤ f t := fun t => by positivity
  have hfs : Summable f := (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left 16
  have hI0 : 0 ≤ thrI K a κ Gm := thrI_nonneg K a κ Gm hK ha hκ0 hGm0
  refine ⟨(T0' : ℝ) + 3 + thrI K a κ Gm / ((1 - κ) * Gm) + ∑' t, f t, fun δ hδ hδ1 => ?_⟩
  set L := Real.log (1 / δ) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  set Zlo : (ℕ → ℝ) → ℕ → ℝ := fun ω t =>
    if Fintype.card E ≤ t then Zh P a Tst (runG P (oLearner O) θ t ω) else 0 with hZlo
  set thr : (ℕ → ℝ) → ℕ → ℝ := fun ω t => bthr a δ (hN (runG P (oLearner O) θ t ω)) with hthr
  have hfire : ∀ ω t, 1 ∣ t → thr ω t < Zlo ω t → tauG P a δ (oLearner O) θ ω ≤ t := by
    intro ω t _ hlt
    change bthr a δ (hN (runG P (oLearner O) θ t ω))
      < (if Fintype.card E ≤ t then Zh P a Tst (runG P (oLearner O) θ t ω) else 0) at hlt
    split_ifs at hlt with hc
    · unfold tauG
      classical
      exact hitTime_le_of t ⟨hc, Tst, hlt⟩
    · exfalso
      have := bthr_nonneg a ha δ hδ hδ1.le (hN (runG P (oLearner O) θ t ω)) (fun e => by
        rw [hN_runG]; exact Nat.cast_nonneg _)
      linarith
  have hthrle : ∀ ω (t : ℕ), thr ω t ≤ L + (K / 2) * Real.log (1 + t / a) := by
    intro ω t
    change bthr a δ (hN (runG P (oLearner O) θ t ω)) ≤ _
    rw [hN_runG]
    unfold bthr
    exact code_thr_le a ha _ (fun e => Nat.cast_nonneg _) (t : ℝ)
      (fun e => o_count_le P O θ ω t e) L
  have hdirect : ∀ ω t, T0' ≤ t → ω ∈ GoodWinO P O a θ t → Gm * t - 0 ≤ Zlo ω t := by
    intro ω t ht hω
    have hc : Fintype.card E ≤ t := le_trans (le_max_right _ _) ht
    change _ ≤ (if Fintype.card E ≤ t then Zh P a Tst (runG P (oLearner O) θ t ω) else 0)
    rw [ite_cond_eq_true _ _ (eq_true hc), sub_zero]
    exact hT0 t (le_trans (le_max_left _ _) ht) ω hω
  have hwin := win_of_direct Zlo thr (GoodWinO P O a θ) L 0 K a κ Gm hK ha hκ0 hκ1 hGm0 T0'
    hdirect hthrle
  set t1 := max T0' (crossT L 0 K a κ Gm) with ht1
  have hbad : ∀ t, t1 + 1 ≤ t →
      streamMeasure (GoodWinO P O a θ (lastCheck 1 t))ᶜ ≤ ENNReal.ofReal (f t) := by
    intro t ht
    rw [show lastCheck 1 t = t by simp [lastCheck]]
    exact o_goodWin_compl_le P O a ha θ t (by omega)
  have hE := expect_le streamMeasure (tauG P a δ (oLearner O) θ)
    (measurable_tauG P a δ (oLearner O) ha θ) 1 one_pos Zlo thr
    (GoodWinO P O a θ) hfire t1 hwin f hf0 hfs hbad
  have hRHS : ((t1 + 1 : ℕ) : ℝ≥0∞) + ENNReal.ofReal (∑' t, f t) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _, ENNReal.ofReal_ne_top⟩
  refine ⟨ne_top_of_le_ne_top hRHS hE, ?_⟩
  have hreal : (∫⁻ ω, (tauG P a δ (oLearner O) θ ω).toENNReal ∂streamMeasure).toReal
      ≤ ((t1 + 1 : ℕ) : ℝ) + ∑' t, f t := by
    have := ENNReal.toReal_mono hRHS hE
    rwa [ENNReal.toReal_add (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_natCast, ENNReal.toReal_ofReal (tsum_nonneg hf0)] at this
  have hy0 : 0 ≤ (L + 0 + thrI K a κ Gm) / ((1 - κ) * Gm) :=
    div_nonneg (by linarith) hdenpos.le
  have hcross : (crossT L 0 K a κ Gm : ℝ) ≤ (L + 0 + thrI K a κ Gm) / ((1 - κ) * Gm) + 2 := by
    unfold crossT
    push_cast
    have := Nat.ceil_lt_add_one hy0
    linarith
  have ht1R : ((t1 + 1 : ℕ) : ℝ)
      ≤ T0' + ((L + 0 + thrI K a κ Gm) / ((1 - κ) * Gm) + 2) + 1 := by
    have h1 : t1 ≤ T0' + crossT L 0 K a κ Gm :=
      max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
    have h2 : ((t1 : ℕ) : ℝ) ≤ (T0' : ℝ) + (crossT L 0 K a κ Gm : ℝ) := by exact_mod_cast h1
    push_cast
    linarith
  have hLq : L / ((1 - κ) * Gm) ≤ L / (Γ - η) :=
    div_le_div_of_nonneg_left hL0 (by linarith) hden
  have hsplit : (L + 0 + thrI K a κ Gm) / ((1 - κ) * Gm)
      = L / ((1 - κ) * Gm) + thrI K a κ Gm / ((1 - κ) * Gm) := by
    rw [add_zero, add_div]
  linarith

/-- **Correctness at every world**, for every oracle. -/
theorem oracle_correct (a : ℝ) (ha : 0 < a) (δ : ℝ) (hδ : 0 < δ) (Tst : Ans) (θ : E → ℝ)
    (hwrong : ∀ T, T ≠ Tst → θ ∈ P.Alt T) :
    streamMeasure {ω | ∃ t, stopAt P a δ t (runG P (oLearner O) θ t ω)
        ∧ answerAt P a (runG P (oLearner O) θ t ω) ≠ Tst}
      ≤ ((Fintype.card Ans - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal δ :=
  correctG P a δ (oLearner O) ha hδ Tst θ hwrong

/-! ## 4. The fixed design -/

/-- The oracle that ignores the estimate and returns the design `w`. -/
noncomputable def constO (w : E → ℝ) (hw : IsAlloc w) : Oracle E where
  D := fun _ => w
  meas := measurable_const
  alloc := fun _ => hw

/-- The true game at a design, in unit-variance coordinates. -/
noncomputable def Jw (Tst : Ans) (θ w : E → ℝ) : ℝ := Jval (sc P.σ '' P.Alt Tst) w (sc P.σ θ)

theorem Jw_le_GamT (Tst : Ans) (θ w : E → ℝ) (hw : IsAlloc w) : Jw P Tst θ w ≤ GamT P Tst θ :=
  (GamT_isLUB P Tst θ).1 ⟨w, hw, rfl⟩

/-- **The fixed design is attained at its own rate.** -/
theorem fix_expect_bound (a : ℝ) (ha : 0 < a) (Tst : Ans) (θ w : E → ℝ) (hw : IsAlloc w)
    (hJ : 0 < Jw P Tst θ w) (η : ℝ) (hη : 0 < η) (hηJ : η < Jw P Tst θ w) :
    ∃ A : ℝ, ∀ δ, 0 < δ → δ < 1 →
      (∫⁻ ω, (tauG P a δ (oLearner (constO w hw)) θ ω).toENNReal ∂streamMeasure) ≠ ⊤ ∧
      (∫⁻ ω, (tauG P a δ (oLearner (constO w hw)) θ ω).toENNReal ∂streamMeasure).toReal
        ≤ Real.log (1 / δ) / (Jw P Tst θ w - η) + A :=
  oracle_expect_bound P (constO w hw) a ha Tst θ (Jw P Tst θ w) hJ (Jw_le_GamT P Tst θ w hw)
    (fun η' hη' => ⟨0, fun s _ ω _ => by
      show Jw P Tst θ w - η' / 4 ≤ Jw P Tst θ w
      linarith [hη']⟩) η hη hηJ

/-- **The upper rate of the fixed design.** -/
theorem fix_upper_rate (a : ℝ) (ha : 0 < a) (Tst : Ans) (θ w : E → ℝ) (hw : IsAlloc w)
    (hJ : 0 < Jw P Tst θ w) :
    CIGAMF.P13.PaperAEndgame.UpperRate
      (fun δ => (∫⁻ ω, (tauG P a δ (oLearner (constO w hw)) θ ω).toENNReal
        ∂streamMeasure).toReal) (Jw P Tst θ w) :=
  upper_rate_of_bound _ _ hJ fun η hη hηJ => by
    obtain ⟨A, hA⟩ := fix_expect_bound P a ha Tst θ w hw hJ η hη hηJ
    exact ⟨A, fun δ hδ hδ1 => (hA δ hδ hδ1).2⟩

/-! ## 5. The realised design of the fixed-design learner -/

theorem avgTarget_const_ge (w : E → ℝ) (hw : IsAlloc w) (t : ℕ) (ht : 0 < t) (e : E) :
    (1 - (Fintype.card E + 2 * Real.sqrt t) / t) * w e
      ≤ PaperA7Accumulation.avgTarget (fun _ => w) (rho (E := E)) unif t e := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  unfold PaperA7Accumulation.avgTarget PaperA7Accumulation.target
  have h1 : ∑ s ∈ range t, (1 / (t : ℝ)) * ((1 - rho (E := E) s) * w e)
      ≤ ∑ s ∈ range t, (1 / (t : ℝ)) * ((1 - rho (E := E) s) * w e + rho (E := E) s * unif e) := by
    refine sum_le_sum fun s _ => ?_
    have h0 := CIGAMF.P13.PaperA6FixedDesign.rho_nonneg (E := E) s
    have hu : 0 ≤ unif (E := E) e := unif_alloc.1 e
    have : 0 ≤ (1 / (t : ℝ)) * (rho (E := E) s * unif e) := by positivity
    nlinarith
  have h2 : ∑ s ∈ range t, (1 / (t : ℝ)) * ((1 - rho (E := E) s) * w e)
      = w e * (1 - (∑ s ∈ range t, rho (E := E) s) / t) := by
    have : ∑ s ∈ range t, (1 / (t : ℝ)) * ((1 - rho (E := E) s) * w e)
        = (1 / (t : ℝ)) * w e * ∑ s ∈ range t, (1 - rho (E := E) s) := by
      rw [mul_sum]; exact sum_congr rfl fun s _ => by ring
    rw [this, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_one]
    field_simp
  have h3 := sum_rho_le (E := E) t
  have hw0 := hw.1 e
  have h4 : w e * (1 - (Fintype.card E + 2 * Real.sqrt t) / t)
      ≤ w e * (1 - (∑ s ∈ range t, rho (E := E) s) / t) := by
    apply mul_le_mul_of_nonneg_left _ hw0
    have : (∑ s ∈ range t, rho (E := E) s) / t ≤ (Fintype.card E + 2 * Real.sqrt t) / t :=
      div_le_div_of_nonneg_right h3 htR.le
    linarith
  linarith

/-- **The realised design dominates `(1 - ε) w`, on every path, after a deterministic time.** -/
theorem fix_design_floor (θ w : E → ℝ) (hw : IsAlloc w) (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℕ, ∀ t, T ≤ t → ∀ ω e,
      (1 - ε) * w e ≤ Nc (oLearner (constO w hw)) θ P.σ t ω e / t := by
  set K : ℝ := (Fintype.card E : ℝ) with hKdef
  have hK : 1 ≤ K := by rw [hKdef]; exact_mod_cast Fintype.card_pos
  have hK1 : 0 ≤ K - 1 := by linarith
  obtain ⟨T1, hT1⟩ := eventually_inv_sqrt (2 * K * (K - 1)) (ε / 2) (by positivity) (by positivity)
  obtain ⟨T2, hT2⟩ := eventually_inv K (ε / 4) (by linarith) (by positivity)
  obtain ⟨T3, hT3⟩ := eventually_inv_sqrt 2 (ε / 4) (by norm_num) (by positivity)
  refine ⟨max (max T1 T2) (max T3 (Fintype.card E)), fun t ht ω e => ?_⟩
  have htK : Fintype.card E ≤ t := by omega
  have ht0 : 0 < t := lt_of_lt_of_le Fintype.card_pos htK
  have htR : (0 : ℝ) < t := by exact_mod_cast ht0
  have hN0 : 0 ≤ Nc (oLearner (constO w hw)) θ P.σ t ω e / t :=
    div_nonneg (Nat.cast_nonneg _) htR.le
  rcases le_or_gt 1 ε with hε1 | hε1
  · have : (1 - ε) * w e ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (hw.1 e)
    linarith
  have hsqt : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.mpr htR
  have htt : Real.sqrt (t : ℝ) * Real.sqrt t = t := Real.mul_self_sqrt htR.le
  have htrack0 := o_track P (constO w hw) θ ω (t - Fintype.card E)
  rw [show Fintype.card E + (t - Fintype.card E) = t by omega] at htrack0
  have hρ : ∀ s, rho (E := E) s ≤ 1 := fun s => CIGAMF.P13.PaperA6FixedDesign.rho_le_one s
  have hfloor : ∀ e, 1 / (K * Real.sqrt t) ≤
      PaperA7Accumulation.avgTarget (fun _ => w) (rho (E := E)) unif t e :=
    fun e => avgTarget_floor (fun _ => w) (fun s e => hw.1 e) rho hρ
      (fun s => by
        unfold rho
        split_ifs
        · rw [div_le_one (Real.sqrt_pos.mpr (by positivity))]
          exact Real.one_le_sqrt.mpr (by linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)])
        · exact le_rfl) unif (fun e => rfl) t ht0 e
  have hmult := mult_of_additive (fun e => Nc (oLearner (constO w hw)) θ P.σ t ω e)
    (PaperA7Accumulation.avgTarget (fun _ => w) (rho (E := E)) unif t) (t : ℝ)
    (2 * ((Fintype.card E : ℝ) - 1)) (1 / (K * Real.sqrt t)) htR (by positivity) (by linarith)
    hfloor htrack0 e
  have hden : (t : ℝ) * (1 / (K * Real.sqrt t)) = Real.sqrt t / K := by
    calc (t : ℝ) * (1 / (K * Real.sqrt t))
        = (Real.sqrt t * Real.sqrt t) * (1 / (K * Real.sqrt t)) := by rw [htt]
      _ = Real.sqrt t / K := by field_simp
  have hεt : 2 * ((Fintype.card E : ℝ) - 1) / ((t : ℝ) * (1 / (K * Real.sqrt t)))
      = 2 * K * (K - 1) / Real.sqrt t := by
    rw [hden]; field_simp; ring
  rw [hεt] at hmult
  have hε1' : 2 * K * (K - 1) / Real.sqrt t ≤ ε / 2 := hT1 t (by omega)
  have hB : (K + 2 * Real.sqrt t) / t ≤ ε / 2 := by
    have h2 : K / t ≤ ε / 4 := hT2 t (by omega)
    have h3 : 2 / Real.sqrt t ≤ ε / 4 := hT3 t (by omega)
    have e1 : (K + 2 * Real.sqrt t) / t = K / t + 2 / Real.sqrt t := by
      rw [add_div]
      congr 1
      rw [div_eq_div_iff htR.ne' hsqt.ne', mul_assoc, htt]
    linarith
  have havg := avgTarget_const_ge w hw t ht0 e
  have hw0 := hw.1 e
  have hA : (1 - ε / 2) * w e ≤ PaperA7Accumulation.avgTarget (fun _ => w) (rho (E := E)) unif t e := by
    refine le_trans ?_ havg
    exact mul_le_mul_of_nonneg_right (by linarith) hw0
  have hc0 : 0 ≤ 1 - 2 * K * (K - 1) / Real.sqrt t := by linarith
  have hB' : (1 - ε / 2) * ((1 - ε / 2) * w e)
      ≤ (1 - 2 * K * (K - 1) / Real.sqrt t)
        * PaperA7Accumulation.avgTarget (fun _ => w) (rho (E := E)) unif t e := by
    have hprod : (1 - ε / 2) * ((1 - ε / 2) * w e)
        ≤ (1 - 2 * K * (K - 1) / Real.sqrt t) * ((1 - ε / 2) * w e) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (by linarith) hw0)
    exact hprod.trans (mul_le_mul_of_nonneg_left hA hc0)
  have hsq : (1 - ε) * w e ≤ (1 - ε / 2) * ((1 - ε / 2) * w e) := by
    have : (1 - ε) ≤ (1 - ε / 2) * (1 - ε / 2) := by nlinarith
    nlinarith
  exact hsq.trans (hB'.trans hmult)

/-- **A game value is monotone and homogeneous in the design.** -/
theorem Jval_ge_scale (Alt : Set (E → ℝ)) (hne : Alt.Nonempty) (w w' μ : E → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hw : ∀ e, 0 ≤ w e) (hle : ∀ e, c * w e ≤ w' e) :
    c * Jval Alt w μ ≤ Jval Alt w' μ := by
  refine le_csInf (hne.image _) ?_
  rintro _ ⟨ν, hν, rfl⟩
  have h1 : Jval Alt w μ ≤ pen w μ ν := csInf_le (Jval_bddBelow Alt w μ hw) ⟨ν, hν, rfl⟩
  have h2 : c * pen w μ ν ≤ pen w' μ ν := by
    unfold pen
    rw [mul_div_assoc']
    apply div_le_div_of_nonneg_right _ (by norm_num)
    rw [mul_sum]
    exact sum_le_sum fun e _ => by
      have := hle e
      have := sq_nonneg (μ e - ν e)
      nlinarith
  exact (mul_le_mul_of_nonneg_left h1 hc).trans h2

/-- **The realised design enters the budget after a deterministic burn-in**, on every path. -/
theorem fix_budget_eventually (θ w : E → ℝ) (hw : IsAlloc w) (Altf : Set (E → ℝ))
    (hAf : Altf.Nonempty) (Γf : ℝ) (hΓf : 0 < Γf) (b : ℝ)
    (hb : 1 - Jval (sc P.σ '' Altf) w (sc P.σ θ) / Γf < b) :
    ∃ T : ℕ, ∀ t, T ≤ t → ∀ ω,
      1 - Jval (sc P.σ '' Altf) (fun e => Nc (oLearner (constO w hw)) θ P.σ t ω e / t)
        (sc P.σ θ) / Γf ≤ b := by
  set Jf := Jval (sc P.σ '' Altf) w (sc P.σ θ) with hJf
  have hJf0 : 0 ≤ Jf :=
    le_csInf (hAf.image _ |>.image _) (by rintro _ ⟨ν, -, rfl⟩; exact pen_nonneg w _ ν hw.1)
  set gap := b - (1 - Jf / Γf) with hgap
  have hgap0 : 0 < gap := by rw [hgap]; linarith
  set ε := min 1 (gap * Γf / (Jf + 1)) with hε
  have hε0 : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεJ : ε * Jf / Γf ≤ gap := by
    have h1 : ε ≤ gap * Γf / (Jf + 1) := min_le_right _ _
    rw [div_le_iff₀ hΓf]
    calc ε * Jf ≤ gap * Γf / (Jf + 1) * Jf := mul_le_mul_of_nonneg_right h1 hJf0
      _ ≤ gap * Γf := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith [mul_pos hgap0 hΓf]
  obtain ⟨T, hT⟩ := fix_design_floor P θ w hw ε hε0
  refine ⟨T, fun t ht ω => ?_⟩
  have hJ := Jval_ge_scale (sc P.σ '' Altf) (hAf.image _) w
    (fun e => Nc (oLearner (constO w hw)) θ P.σ t ω e / t) (sc P.σ θ) (1 - ε) (by linarith)
    hw.1 (hT t ht ω)
  have : (1 - ε) * Jf / Γf ≤
      Jval (sc P.σ '' Altf) (fun e => Nc (oLearner (constO w hw)) θ P.σ t ω e / t)
        (sc P.σ θ) / Γf := div_le_div_of_nonneg_right hJ hΓf.le
  have e : (1 - ε) * Jf / Γf = Jf / Γf - ε * Jf / Γf := by ring
  linarith

#print axioms o_count_floor
#print axioms o_track
#print axioms o_radius_run
#print axioms oracle_direct
#print axioms o_goodWin_compl_le
#print axioms oracle_expect_bound
#print axioms oracle_correct
#print axioms fix_expect_bound
#print axioms fix_upper_rate
#print axioms avgTarget_const_ge
#print axioms fix_design_floor
#print axioms Jval_ge_scale
#print axioms fix_budget_eventually

end CIGAMF.P13.PaperABudgetUpper
