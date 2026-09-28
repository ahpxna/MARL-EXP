import «LeanPaperA6FixedDesignV1»

/-!
# Paper A6: a tracking learner driven by ANY oracle of the estimate

The ideal learner (`LeanPaperA7IdealLearnerV1`) tracks the exact oracle `design P s (hMu h)`;
the fixed-design learner (`LeanPaperA6FixedDesignV1`) tracks a constant.  Here the oracle is an
arbitrary measurable, allocation-valued function `O.D` of the current estimate, which is what a
learner that RE-SOLVES a surrogate at its estimate does.  Same warm start, same forcing
`rho_s = 1/sqrt(s+1)`, same post-warm quota and first maximiser of `W - N`.

* `oLearner O` -- the learner; it reads only the history.
* `oWarmRun` -- its run in any world is a `WarmRun`, so the tracking discrepancy applies.
* `oCount_ge` -- every count is at least `sqrt t / K - (K - 1)` (forcing).
* `oCount_le_bad` -- **a cell's count is at most `2 + badT + 2 sqrt t / K`**, where `badT` counts
  the post-warm rounds at which the oracle put positive weight on that cell.  Forcing and those
  rounds are the only sources of queries.
* `oCount_le_amgm` -- the same in the linear form `2 + badT + (t/s + s)/K`.
-/

namespace CIGAMF.P13.PaperA6OracleLearner

open Finset MeasureTheory
open CIGAMF.P13.PaperA7Stream CIGAMF.P13.PaperA7Process CIGAMF.P13.PaperA7IdealLearner
open CIGAMF.P13.PaperA7WarmTrack CIGAMF.P13.PaperA7Tracking CIGAMF.P13.PaperA7OracleSelect
open CIGAMF.P13.PaperA7IdealRun (histF_restr)
open CIGAMF.P13.PaperA6FixedDesign (rho_nonneg rho_le_one)

variable {E : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [Nonempty E]

/-- **An oracle of the estimate**: measurable and allocation-valued. -/
structure Oracle (E : Type*) [Fintype E] where
  D : (E → ℝ) → (E → ℝ)
  meas : Measurable D
  alloc : ∀ μ, IsAlloc (D μ)

variable (O : Oracle E)

/-! ## 1. The learner -/

/-- The target of round `s`: the oracle at the estimate, mixed toward uniform. -/
noncomputable def oTarget (s : ℕ) (h : Fin s → E × ℝ) : E → ℝ :=
  fun e => (1 - rho (E := E) s) * O.D (hMu h) e + rho (E := E) s * unif e

/-- The post-warm quota through round `t`. -/
noncomputable def oQuota (t : ℕ) (h : Fin t → E × ℝ) (e : E) : ℝ :=
  ∑ s : Fin (t + 1), if Fintype.card E ≤ (s : ℕ) then
    oTarget O s (restr s (Nat.lt_succ_iff.mp s.isLt) h) e else 0

/-- **The pick**: warm start, then the first maximiser of `W - N`. -/
noncomputable def oPick (t : ℕ) (h : Fin t → E × ℝ) : E :=
  if t < Fintype.card E then warmCell t else argmaxCell (fun e => oQuota O t h e - hN h e)

theorem measurable_oTarget (s : ℕ) : Measurable fun h : Fin s → E × ℝ => oTarget O s h := by
  unfold oTarget
  refine measurable_pi_lambda _ fun e => ?_
  refine (measurable_const.mul ?_).add measurable_const
  exact (measurable_pi_apply e).comp (O.meas.comp (measurable_hMu s))

theorem measurable_oQuota (t : ℕ) (e : E) :
    Measurable fun h : Fin t → E × ℝ => oQuota O t h e := by
  unfold oQuota
  refine Finset.measurable_sum _ fun s _ => ?_
  by_cases hs : Fintype.card E ≤ (s : ℕ)
  · simp only [hs, if_true]
    exact (measurable_pi_apply e).comp ((measurable_oTarget O s).comp (measurable_restr _ _))
  · simp only [hs, if_false]
    exact measurable_const

theorem measurable_oPick (t : ℕ) : Measurable (oPick O t) := by
  unfold oPick
  by_cases ht : t < Fintype.card E
  · simp only [ht, if_true]; exact measurable_const
  · simp only [ht, if_false]
    exact measurable_argmaxCell.comp
      (measurable_pi_lambda _ fun e => (measurable_oQuota O t e).sub (measurable_hN t e))

/-- **The oracle-tracking learner.** -/
noncomputable def oLearner : Learner E where
  rule t := oPick O t
  meas t := measurable_oPick O t

theorem oPick_greedy (t : ℕ) (ht : Fintype.card E ≤ t) (h : Fin t → E × ℝ) (e : E) :
    oQuota O t h e - hN h e ≤ oQuota O t h (oPick O t h) - hN h (oPick O t h) := by
  unfold oPick
  rw [if_neg (not_lt.mpr ht)]
  exact argmaxCell_spec (fun e => oQuota O t h e - hN h e) e

theorem oPick_warm (t : ℕ) (ht : t < Fintype.card E) (h : Fin t → E × ℝ) :
    oPick O t h = warmCell t := by
  unfold oPick; rw [if_pos ht]

/-! ## 2. Its run -/

/-- The observed history of `t` rounds in world `theta`, noise `sigma`. -/
noncomputable def oRun (θ σ : E → ℝ) (t : ℕ) (ω : ℕ → ℝ) : Fin t → E × ℝ :=
  histF (oLearner O) θ σ t (Xp t ω)

theorem measurable_oRun (θ σ : E → ℝ) (t : ℕ) : Measurable (oRun O θ σ t) :=
  (measurable_histF _ θ σ t).comp (measurable_Xp t)

theorem restr_oRun (θ σ : E → ℝ) (t s : ℕ) (hs : s ≤ t) (ω : ℕ → ℝ) :
    restr s hs (oRun O θ σ t ω) = oRun O θ σ s ω := by
  unfold oRun
  rw [histF_restr]
  rfl

theorem hN_oRun (θ σ : E → ℝ) (t : ℕ) (ω : ℕ → ℝ) :
    hN (oRun O θ σ t ω) = Nc (oLearner O) θ σ t ω := by
  funext e
  unfold hN oRun Nc NF
  push_cast
  rfl

theorem oNc_succ (θ σ : E → ℝ) (t : ℕ) (ω : ℕ → ℝ) (e : E) :
    Nc (oLearner O) θ σ (t + 1) ω e
      = Nc (oLearner O) θ σ t ω e + if e = oPick O t (oRun O θ σ t ω) then 1 else 0 := by
  have hq : qF (oLearner O) θ σ t (Xp t ω) = oPick O t (oRun O θ σ t ω) := rfl
  unfold Nc
  rw [Xp_succ, NF_snoc, hq]
  push_cast
  by_cases h : e = oPick O t (oRun O θ σ t ω)
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem oNc_zero (θ σ : E → ℝ) (ω : ℕ → ℝ) (e : E) : Nc (oLearner O) θ σ 0 ω e = 0 := by
  unfold Nc NF; simp

theorem oNc_warm_le (θ σ : E → ℝ) (ω : ℕ → ℝ) :
    ∀ t, t ≤ Fintype.card E → ∀ e,
      Nc (oLearner O) θ σ t ω e = if ((Fintype.equivFin E e : Fin _) : ℕ) < t then 1 else 0
  | 0, _, e => by rw [oNc_zero]; simp
  | t + 1, ht, e => by
      rw [oNc_succ, oNc_warm_le θ σ ω t (by omega) e, oPick_warm O t (by omega)]
      have hw : warmCell (E := E) t = (Fintype.equivFin E).symm ⟨t, by omega⟩ := by
        unfold warmCell
        congr 2
        exact Nat.mod_eq_of_lt (by omega)
      rw [hw]
      have hiff : e = (Fintype.equivFin E).symm ⟨t, by omega⟩
          ↔ ((Fintype.equivFin E e : Fin _) : ℕ) = t := by
        constructor
        · intro h; rw [h]; simp
        · intro h
          apply (Fintype.equivFin E).injective
          rw [Equiv.apply_symm_apply]
          exact Fin.ext h
      by_cases h1 : ((Fintype.equivFin E e : Fin _) : ℕ) = t
      · rw [if_pos (hiff.mpr h1), if_neg (by omega), if_pos (by omega)]; norm_num
      · rw [if_neg (fun h => h1 (hiff.mp h))]
        by_cases h2 : ((Fintype.equivFin E e : Fin _) : ℕ) < t
        · rw [if_pos h2, if_pos (by omega)]; norm_num
        · rw [if_neg h2, if_neg (by omega)]; norm_num

theorem oNc_warm (θ σ : E → ℝ) (ω : ℕ → ℝ) (e : E) :
    Nc (oLearner O) θ σ (Fintype.card E) ω e = 1 := by
  rw [oNc_warm_le O θ σ ω _ le_rfl e, if_pos (Fintype.equivFin E e).isLt]

/-! ## 3. The run is a warm-started tracking run -/

theorem oTarget_alloc (s : ℕ) (h : Fin s → E × ℝ) : IsAlloc (oTarget O s h) := by
  have hK : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  have hρ0 := rho_nonneg (E := E) s
  have hρ1 := rho_le_one (E := E) s
  have hd := O.alloc (hMu h)
  refine ⟨fun e => ?_, ?_⟩
  · unfold oTarget unif
    exact add_nonneg (mul_nonneg (by linarith) (hd.1 e)) (mul_nonneg hρ0 (by positivity))
  · unfold oTarget unif
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, hd.2, sum_const, card_univ, nsmul_eq_mul]
    field_simp
    ring

/-- The run's post-warm targets. -/
noncomputable def ovRun (θ σ : E → ℝ) (ω : ℕ → ℝ) (j : ℕ) : E → ℝ :=
  oTarget O (Fintype.card E + (j - 1)) (oRun O θ σ (Fintype.card E + (j - 1)) ω)

theorem oQuota_run' (θ σ : E → ℝ) (ω : ℕ → ℝ) (t : ℕ) (e : E) :
    oQuota O t (oRun O θ σ t ω) e = ∑ s : Fin (t + 1),
      if Fintype.card E ≤ (s : ℕ) then oTarget O s (oRun O θ σ s ω) e else 0 := by
  unfold oQuota
  refine sum_congr rfl fun s _ => ?_
  rw [restr_oRun]

theorem oQuota_run (θ σ : E → ℝ) (ω : ℕ → ℝ) (k : ℕ) (e : E) :
    oQuota O (Fintype.card E + k) (oRun O θ σ (Fintype.card E + k) ω) e
      = W (ovRun O θ σ ω) (k + 1) e := by
  rw [oQuota_run' O θ σ ω]
  unfold W ovRun
  rw [Fin.sum_univ_eq_sum_range (fun s => if Fintype.card E ≤ s then
      oTarget O s (oRun O θ σ s ω) e else 0) (Fintype.card E + k + 1)]
  rw [show Fintype.card E + k + 1 = Fintype.card E + (k + 1) by ring, sum_range_add]
  have hwarm : ∑ x ∈ range (Fintype.card E),
      (if Fintype.card E ≤ x then oTarget O x (oRun O θ σ x ω) e else 0) = 0 :=
    sum_eq_zero fun x hx => if_neg (by have := mem_range.mp hx; omega)
  rw [hwarm, zero_add]
  refine sum_congr rfl fun j _ => ?_
  rw [if_pos (by omega)]
  rfl

/-- **The run as a warm-started tracking run.** -/
noncomputable def oWarmRun (θ σ : E → ℝ) (ω : ℕ → ℝ) : WarmRun E where
  v := ovRun O θ σ ω
  N k e := Nc (oLearner O) θ σ (Fintype.card E + k) ω e
  pick j := oPick O (Fintype.card E + (j - 1)) (oRun O θ σ (Fintype.card E + (j - 1)) ω)
  vnn s e := (oTarget_alloc O _ _).1 e
  vsum s := (oTarget_alloc O _ _).2
  N0 e := oNc_warm O θ σ ω e
  Nstep t e := by
    show Nc (oLearner O) θ σ (Fintype.card E + (t + 1)) ω e
      = Nc (oLearner O) θ σ (Fintype.card E + t) ω e
        + if e = oPick O (Fintype.card E + t) (oRun O θ σ (Fintype.card E + t) ω) then 1 else 0
    rw [show Fintype.card E + (t + 1) = (Fintype.card E + t) + 1 by ring, oNc_succ]
  greedy t e := by
    have hg := oPick_greedy O (Fintype.card E + t) (by omega)
      (oRun O θ σ (Fintype.card E + t) ω) e
    rw [oQuota_run, oQuota_run, hN_oRun] at hg
    exact hg

/-! ## 4. Counts -/

/-- **Every count grows like `sqrt` of the time.** -/
theorem oCount_ge (θ σ : E → ℝ) (ω : ℕ → ℝ) (k : ℕ) (e : E) :
    Real.sqrt ((Fintype.card E + k : ℕ) : ℝ) / Fintype.card E - ((Fintype.card E : ℝ) - 1)
      ≤ Nc (oLearner O) θ σ (Fintype.card E + k) ω e := by
  refine warm_count_ge (oWarmRun O θ σ ω) e (fun j => ?_) k
  show _ ≤ ovRun O θ σ ω (j + 1) e
  unfold ovRun oTarget unif
  rw [show Fintype.card E + (j + 1 - 1) = Fintype.card E + j by omega]
  have hrho : rho (E := E) (Fintype.card E + j)
      = 1 / Real.sqrt (((Fintype.card E + j : ℕ) : ℝ) + 1) := by
    unfold rho; rw [if_neg (by omega)]
  rw [hrho]
  exact code_target_floor _ unif ((O.alloc _).1) (fun e => rfl) (Fintype.card E + j) e

/-- No count exceeds its quota by more than two. -/
theorem oCount_le_quota (θ σ : E → ℝ) (ω : ℕ → ℝ) (k : ℕ) (e : E) :
    Nc (oLearner O) θ σ (Fintype.card E + k) ω e ≤ 2 + W (ovRun O θ σ ω) k e := by
  have h := ((oWarmRun O θ σ ω).discrepancy k e).2
  have : (oWarmRun O θ σ ω).N k e = Nc (oLearner O) θ σ (Fintype.card E + k) ω e := rfl
  have hv : (oWarmRun O θ σ ω).v = ovRun O θ σ ω := rfl
  rw [this, hv] at h
  linarith

/-- The number of post-warm rounds before `t` at which the oracle weighted cell `e`. -/
noncomputable def badT (θ σ : E → ℝ) (ω : ℕ → ℝ) (t : ℕ) (e : E) : ℝ :=
  ∑ s ∈ range t, if Fintype.card E ≤ s ∧ O.D (hMu (oRun O θ σ s ω)) e ≠ 0 then 1 else 0

theorem badT_nonneg (θ σ : E → ℝ) (ω : ℕ → ℝ) (t : ℕ) (e : E) : 0 ≤ badT O θ σ ω t e :=
  sum_nonneg fun s _ => by split_ifs <;> norm_num

theorem badT_mono (θ σ : E → ℝ) (ω : ℕ → ℝ) (e : E) {t t' : ℕ} (h : t ≤ t') :
    badT O θ σ ω t e ≤ badT O θ σ ω t' e := by
  unfold badT
  exact sum_le_sum_of_subset_of_nonneg (range_mono h) fun s _ _ => by
    split_ifs <;> norm_num

theorem D_le_one (μ : E → ℝ) (e : E) : O.D μ e ≤ 1 := by
  have h := O.alloc μ
  rw [← h.2]
  exact single_le_sum (fun i _ => h.1 i) (mem_univ e)

/-- **The quota of a cell is the forcing plus the rounds at which the oracle weighted it.** -/
theorem oQuota_le_bad (θ σ : E → ℝ) (ω : ℕ → ℝ) (k : ℕ) (e : E) :
    W (ovRun O θ σ ω) k e
      ≤ badT O θ σ ω (Fintype.card E + k) e
        + 2 * Real.sqrt ((Fintype.card E + k : ℕ) : ℝ) / Fintype.card E := by
  have hK : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  unfold W
  have hterm : ∀ j ∈ range k, ovRun O θ σ ω (j + 1) e
      ≤ (if O.D (hMu (oRun O θ σ (Fintype.card E + j) ω)) e ≠ 0 then 1 else 0)
        + 1 / Real.sqrt (((Fintype.card E + j : ℕ) : ℝ) + 1) * (1 / (Fintype.card E : ℝ)) := by
    intro j _
    unfold ovRun oTarget unif
    rw [show Fintype.card E + (j + 1 - 1) = Fintype.card E + j by omega]
    have hrho : rho (E := E) (Fintype.card E + j)
        = 1 / Real.sqrt (((Fintype.card E + j : ℕ) : ℝ) + 1) := by
      unfold rho; rw [if_neg (by omega)]
    rw [hrho]
    have hρ0 : 0 ≤ 1 / Real.sqrt (((Fintype.card E + j : ℕ) : ℝ) + 1) := by positivity
    have hρ1 : 1 / Real.sqrt (((Fintype.card E + j : ℕ) : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (Real.sqrt_pos.mpr (by positivity))]
      exact Real.one_le_sqrt.mpr (by linarith [(Nat.cast_nonneg (Fintype.card E + j) : (0 : ℝ) ≤ _)])
    have hD0 := (O.alloc (hMu (oRun O θ σ (Fintype.card E + j) ω))).1 e
    have hD1 := D_le_one O (hMu (oRun O θ σ (Fintype.card E + j) ω)) e
    by_cases hz : O.D (hMu (oRun O θ σ (Fintype.card E + j) ω)) e = 0
    · rw [if_neg (not_not.mpr hz), hz]
      simp
    · rw [if_pos hz]
      nlinarith
  refine le_trans (sum_le_sum hterm) ?_
  rw [sum_add_distrib, ← sum_mul]
  have hbad : ∑ j ∈ range k,
      (if O.D (hMu (oRun O θ σ (Fintype.card E + j) ω)) e ≠ 0 then (1 : ℝ) else 0)
      = badT O θ σ ω (Fintype.card E + k) e := by
    unfold badT
    rw [sum_range_add]
    have hwarm : ∑ x ∈ range (Fintype.card E), (if Fintype.card E ≤ x ∧
        O.D (hMu (oRun O θ σ x ω)) e ≠ 0 then (1 : ℝ) else 0) = 0 :=
      sum_eq_zero fun x hx => if_neg (by have := mem_range.mp hx; omega)
    rw [hwarm, zero_add]
    refine sum_congr rfl fun j _ => ?_
    by_cases hz : O.D (hMu (oRun O θ σ (Fintype.card E + j) ω)) e ≠ 0
    · rw [if_pos hz, if_pos ⟨by omega, hz⟩]
    · rw [if_neg hz, if_neg (fun h => hz h.2)]
  rw [hbad]
  have hsum : ∑ j ∈ range k, 1 / Real.sqrt (((Fintype.card E + j : ℕ) : ℝ) + 1)
      ≤ ∑ s ∈ range (Fintype.card E + k), 1 / Real.sqrt ((s : ℝ) + 1) := by
    rw [sum_range_add]
    have h0 : 0 ≤ ∑ s ∈ range (Fintype.card E), 1 / Real.sqrt ((s : ℝ) + 1) :=
      sum_nonneg fun s _ => by positivity
    have : ∑ j ∈ range k, 1 / Real.sqrt (((Fintype.card E + j : ℕ) : ℝ) + 1)
        = ∑ x ∈ range k, 1 / Real.sqrt (((Fintype.card E + x : ℕ) : ℝ) + 1) := rfl
    linarith
  have h2 := CIGAMF.P13.PaperA7Tail.sum_inv_sqrt_le (Fintype.card E + k)
  have hle := le_trans hsum h2
  have : (∑ j ∈ range k, 1 / Real.sqrt (((Fintype.card E + j : ℕ) : ℝ) + 1))
      * (1 / (Fintype.card E : ℝ))
      ≤ 2 * Real.sqrt ((Fintype.card E + k : ℕ) : ℝ) / Fintype.card E := by
    rw [div_eq_mul_one_div (2 * _)]
    exact mul_le_mul_of_nonneg_right hle (by positivity)
  linarith

/-- **A cell's count: forcing plus the rounds at which the oracle weighted it.** -/
theorem oCount_le_bad (θ σ : E → ℝ) (ω : ℕ → ℝ) (e : E) (t : ℕ) :
    Nc (oLearner O) θ σ t ω e
      ≤ 2 + badT O θ σ ω t e + 2 * Real.sqrt (t : ℝ) / Fintype.card E := by
  have hK : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  have hs : 0 ≤ 2 * Real.sqrt (t : ℝ) / Fintype.card E := by positivity
  have hb := badT_nonneg O θ σ ω t e
  rcases Nat.lt_or_ge t (Fintype.card E) with ht | ht
  · rw [oNc_warm_le O θ σ ω t ht.le e]
    split_ifs <;> linarith
  · obtain ⟨k, rfl⟩ : ∃ k, t = Fintype.card E + k := ⟨t - Fintype.card E, by omega⟩
    have h1 := oCount_le_quota O θ σ ω k e
    have h2 := oQuota_le_bad O θ σ ω k e
    push_cast at h2 ⊢
    linarith

/-- The same bound, linear in `t`. -/
theorem oCount_le_amgm (θ σ : E → ℝ) (ω : ℕ → ℝ) (e : E) (t : ℕ) (s : ℝ) (hs : 0 < s) :
    Nc (oLearner O) θ σ t ω e
      ≤ 2 + badT O θ σ ω t e + ((t : ℝ) / s + s) / Fintype.card E := by
  have hK : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  have h := oCount_le_bad O θ σ ω e t
  have hamgm : 2 * Real.sqrt (t : ℝ) ≤ (t : ℝ) / s + s := by
    have hsq : Real.sqrt (t : ℝ) * Real.sqrt t = t := Real.mul_self_sqrt (Nat.cast_nonneg t)
    have h0 : 0 ≤ (Real.sqrt (t : ℝ) - s) ^ 2 := sq_nonneg _
    rw [div_add' _ _ _ hs.ne', le_div_iff₀ hs]
    nlinarith
  have : 2 * Real.sqrt (t : ℝ) / Fintype.card E ≤ ((t : ℝ) / s + s) / Fintype.card E :=
    div_le_div_of_nonneg_right hamgm hK.le
  linarith

#print axioms oWarmRun
#print axioms oCount_ge
#print axioms oCount_le_bad
#print axioms oCount_le_amgm

end CIGAMF.P13.PaperA6OracleLearner
