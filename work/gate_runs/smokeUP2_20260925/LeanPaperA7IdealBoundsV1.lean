import «LeanPaperA7IdealRunV1»
import «LeanPaperA7IdealSelectV1»
import «LeanPaperA7AsymV1»
import «LeanPaperA7UpperChainV1»
import «LeanPaperA7TailV1»

/-!
# Paper A7: the quantitative facts of the ideal learner's run, one round at a time

Deterministic bounds used by the direct lower bound, each with its constant explicit:

* `smin`, `smax` -- the smallest and largest noise scale;
* `bthr_le` -- the code's confidence threshold at level `s^(-4)` is at most `C1 sqrt(sqrt s)`;
* `radius_run` -- on the good event at time `s`, if every count is at least `Nmin >= a`, the
  raw mean is within `2 smax sqrt(b / Nmin)` of the world in every coordinate
  (`radius_of_good` plus `N <= a + N <= 2N`);
* `GamT_le` -- the game value near the world is bounded by a constant `Ubd` built from one
  alternative point (the alternatives are not bounded);
* `sum_rho_le` -- the forcing weights sum to at most `K + 2 sqrt t`;
* `net_factor` -- with `beta = K / sqrt k` the grid factor is at least `1 - (K+1)/sqrt k`.
-/

namespace CIGAMF.P13.PaperA7IdealBounds

open Finset MeasureTheory
open CIGAMF.P13.PaperA7Stream CIGAMF.P13.PaperA7Process CIGAMF.P13.PaperA7Confidence
open CIGAMF.P13.PaperA7Correct CIGAMF.P13.PaperA7IdealLearner CIGAMF.P13.PaperA7IdealStop
open CIGAMF.P13.PaperA7IdealRun CIGAMF.P13.PaperA7IdealSelect CIGAMF.P13.PaperA7DirectLower
open CIGAMF.P13.PaperA7OracleSelect CIGAMF.P13.PaperA7Asym CIGAMF.P13.PaperA7UpperChain

variable {E : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [Nonempty E]
variable {Ans : Type*} [Fintype Ans] [DecidableEq Ans] [Nonempty Ans]
variable (P : Spec E Ans)

/-! ## 1. Noise scales -/

noncomputable def smin : ℝ := univ.inf' univ_nonempty P.σ
noncomputable def smax : ℝ := univ.sup' univ_nonempty P.σ

theorem smin_pos : 0 < smin P := by
  unfold smin
  obtain ⟨e, -, he⟩ := exists_min_image univ P.σ univ_nonempty
  rw [show univ.inf' univ_nonempty P.σ = P.σ e from le_antisymm (inf'_le _ (mem_univ e))
    (le_inf' _ _ fun f _ => he f (mem_univ f))]
  exact P.σ_pos e

theorem smin_le (e : E) : smin P ≤ P.σ e := inf'_le _ (mem_univ e)
theorem le_smax (e : E) : P.σ e ≤ smax P := le_sup' _ (mem_univ e)

/-! ## 2. The threshold -/

theorem bthr_nonneg (a : ℝ) (ha : 0 < a) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (N : E → ℝ)
    (hN : ∀ e, 0 ≤ N e) : 0 ≤ bthr a δ N := by
  unfold bthr
  have h1 : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have h2 : 0 ≤ ∑ e, Real.log (1 + N e / a) :=
    sum_nonneg fun e _ => Real.log_nonneg (by have := hN e; have := div_nonneg this ha.le; linarith)
  positivity

/-- **The confidence threshold at level `s^(-4)`.** -/
theorem bthr_le (a : ℝ) (ha : 0 < a) (s : ℕ) (hs : 1 ≤ s) (N : E → ℝ) (hN0 : ∀ e, 0 ≤ N e)
    (hNs : ∀ e, N e ≤ s) :
    bthr a ((s : ℝ) ^ 4)⁻¹ N ≤ C1 (Fintype.card E) a * Real.sqrt (Real.sqrt s) := by
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hs0 : (0 : ℝ) < s := by linarith
  unfold bthr
  have hlog : Real.log (1 / ((s : ℝ) ^ 4)⁻¹) = 4 * Real.log s := by
    rw [one_div, inv_inv, Real.log_pow]; norm_num
  rw [hlog]
  have hc := code_thr_le a ha N hN0 s hNs (4 * Real.log s)
  have ht := thr_le (Fintype.card E) a s (Nat.cast_nonneg _) ha hsR
  linarith

/-! ## 3. The radius on the good event -/

/-- **The raw mean's radius on the good event.** -/
theorem radius_run (a : ℝ) (ha : 0 < a) (θ : E → ℝ) (s : ℕ) (ω : ℕ → ℝ) (b : ℝ) (hb0 : 0 ≤ b)
    (hgood : PaperA7Stream.Qstat a P.σ (Nc (idealLearner P) θ P.σ s ω)
      (muHat (idealLearner P) θ P.σ s ω) θ ≤ b)
    (Nmin : ℝ) (haN : a ≤ Nmin) (hN : ∀ e, Nmin ≤ Nc (idealLearner P) θ P.σ s ω e) (e : E) :
    |muHat (idealLearner P) θ P.σ s ω e - θ e| ≤ 2 * smax P * Real.sqrt (b / Nmin) := by
  have hNmin : 0 < Nmin := lt_of_lt_of_le ha haN
  rw [qstat_truth_eq (idealLearner P) θ P.σ a P.σ_pos s ω] at hgood
  have hNe : 0 < NF (idealLearner P) θ P.σ s (Xp s ω) e := by
    have := lt_of_lt_of_le hNmin (hN e)
    unfold Nc at this
    exact_mod_cast this
  have hr := radius_of_good (idealLearner P) θ P.σ a ha P.σ_pos s (Xp s ω) b hgood e hNe
  set N := (NF (idealLearner P) θ P.σ s (Xp s ω) e : ℝ) with hNdef
  have hNc : Nc (idealLearner P) θ P.σ s ω e = N := rfl
  have hN0 : (0 : ℝ) < N := by rw [hNdef]; exact_mod_cast hNe
  have hNge : Nmin ≤ N := hNc ▸ hN e
  have hmu : muHat (idealLearner P) θ P.σ s ω e = Ysum (idealLearner P) θ P.σ s (Xp s ω) e / N := rfl
  rw [hmu]
  refine le_trans hr ?_
  -- sqrt(2(a+N)b)/N <= 2 sqrt(b/N) <= 2 sqrt(b/Nmin)
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

/-! ## 4. A bound on the game near the world -/

theorem GamT_le_sum (T : Ans) (x ν0 : E → ℝ) (hν0 : ν0 ∈ P.Alt T) :
    GamT P T x ≤ (∑ e, |sc P.σ x e - sc P.σ ν0 e|) ^ 2 / 2 := by
  refine csSup_le ⟨_, unif, unif_alloc, rfl⟩ ?_
  rintro _ ⟨w, hw, rfl⟩
  refine le_trans (csInf_le (Jval_bddBelow _ _ _ hw.1) ⟨sc P.σ ν0, ⟨ν0, hν0, rfl⟩, rfl⟩) ?_
  exact pen_le_sq w _ _ hw _ fun e =>
    single_le_sum (f := fun e => |sc P.σ x e - sc P.σ ν0 e|) (fun _ _ => abs_nonneg _)
      (mem_univ e)

/-- The game bound. -/
noncomputable def Ubd (T : Ans) (θ ν0 : E → ℝ) : ℝ :=
  (∑ e, |sc P.σ θ e - sc P.σ ν0 e| + (Fintype.card E : ℝ) / smin P) ^ 2 / 2

theorem GamT_le (T : Ans) (θ ν0 : E → ℝ) (hν0 : ν0 ∈ P.Alt T) (x : E → ℝ)
    (hx : ∀ e, |x e - θ e| ≤ 1) : GamT P T x ≤ Ubd P T θ ν0 := by
  refine le_trans (GamT_le_sum P T x ν0 hν0) ?_
  unfold Ubd
  apply div_le_div_of_nonneg_right _ (by norm_num)
  have hclose := sc_close P θ x (smin P) (smin_pos P) (smin_le P) 1 zero_le_one hx
  apply pow_le_pow_left₀ (sum_nonneg fun e _ => abs_nonneg _)
  calc ∑ e, |sc P.σ x e - sc P.σ ν0 e|
      ≤ ∑ e, (|sc P.σ θ e - sc P.σ ν0 e| + 1 / smin P) := by
        refine sum_le_sum fun e _ => ?_
        have := abs_sub_le (sc P.σ x e) (sc P.σ θ e) (sc P.σ ν0 e)
        have := hclose e
        linarith
    _ = ∑ e, |sc P.σ θ e - sc P.σ ν0 e| + (Fintype.card E : ℝ) / smin P := by
        rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]; ring

/-! ## 5. The forcing sum and the grid factor -/

theorem rho_le (s : ℕ) : rho (E := E) s
    ≤ 1 / Real.sqrt ((s : ℝ) + 1) + (if s < Fintype.card E then 1 else 0) := by
  unfold rho
  split_ifs with h
  · have : 0 ≤ 1 / Real.sqrt ((s : ℝ) + 1) := by positivity
    linarith
  · linarith

theorem sum_rho_le (t : ℕ) :
    ∑ s ∈ range t, rho (E := E) s ≤ Fintype.card E + 2 * Real.sqrt t := by
  have h1 := CIGAMF.P13.PaperA7Tail.sum_inv_sqrt_le t
  have h2 : ∑ s ∈ range t, (if s < Fintype.card E then (1 : ℝ) else 0) ≤ Fintype.card E := by
    calc ∑ s ∈ range t, (if s < Fintype.card E then (1 : ℝ) else 0)
        ≤ ∑ s ∈ range (Fintype.card E), (1 : ℝ) := by
          rw [← sum_filter]
          calc ∑ s ∈ (range t).filter (· < Fintype.card E), (1 : ℝ)
              = ((range t).filter (· < Fintype.card E)).card := by simp
            _ ≤ (range (Fintype.card E)).card := by
                exact_mod_cast card_le_card fun s hs => by
                  simp only [mem_filter, mem_range] at hs ⊢; exact hs.2
            _ = ∑ s ∈ range (Fintype.card E), (1 : ℝ) := by simp
      _ = Fintype.card E := by simp
  calc ∑ s ∈ range t, rho (E := E) s
      ≤ ∑ s ∈ range t, (1 / Real.sqrt ((s : ℝ) + 1) + (if s < Fintype.card E then 1 else 0)) :=
        sum_le_sum fun s _ => rho_le s
    _ = ∑ s ∈ range t, 1 / Real.sqrt ((s : ℝ) + 1)
          + ∑ s ∈ range t, (if s < Fintype.card E then (1 : ℝ) else 0) := sum_add_distrib
    _ ≤ 2 * Real.sqrt t + Fintype.card E := by push_cast at h1; linarith
    _ = Fintype.card E + 2 * Real.sqrt t := by ring

/-- **The grid factor with `beta = K / sqrt k`.** -/
theorem net_factor (K k : ℝ) (hK : 1 ≤ K) (hk : K ^ 2 ≤ k) :
    let β := K / Real.sqrt k
    0 < β ∧ β ≤ 1 ∧ K ≤ k * β ∧
      1 - (K + 1) / Real.sqrt k ≤ (1 - K / (k * β)) * (1 - β) := by
  intro β
  have hk0 : 0 < k := lt_of_lt_of_le (by positivity) hk
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk0
  have hKs : K ≤ Real.sqrt k := by
    rw [show K = Real.sqrt (K ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    exact Real.sqrt_le_sqrt hk
  have hkk : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt hk0.le
  have hβ0 : 0 < β := div_pos (by linarith) hsk
  have hβ1 : β ≤ 1 := (div_le_one hsk).mpr hKs
  have hkβ : k * β = K * Real.sqrt k := by
    show k * (K / Real.sqrt k) = K * Real.sqrt k
    rw [mul_div_assoc', div_eq_iff hsk.ne', mul_assoc K, hkk]
    ring
  refine ⟨hβ0, hβ1, ?_, ?_⟩
  · rw [hkβ]; nlinarith [Real.one_le_sqrt.mpr (show (1 : ℝ) ≤ k by nlinarith)]
  · rw [hkβ]
    have h1 : K / (K * Real.sqrt k) = 1 / Real.sqrt k := by field_simp
    rw [h1]
    have hexp : (1 - 1 / Real.sqrt k) * (1 - β) = 1 - (K + 1) / Real.sqrt k + K / k := by
      show (1 - 1 / Real.sqrt k) * (1 - K / Real.sqrt k) = _
      have hKk : K / k = K / (Real.sqrt k * Real.sqrt k) := by rw [hkk]
      rw [hKk]
      field_simp
      ring
    rw [hexp]
    have : 0 ≤ K / k := by positivity
    linarith

#print axioms bthr_le
#print axioms radius_run
#print axioms GamT_le
#print axioms sum_rho_le
#print axioms net_factor

end CIGAMF.P13.PaperA7IdealBounds
