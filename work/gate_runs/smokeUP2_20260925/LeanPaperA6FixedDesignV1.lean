import «LeanPaperA7IdealRunV1»
import «LeanPaperA7TailV1»

/-!
# Paper A6: a tracking learner that follows a FIXED design, and what it spends on a cell the
design ignores

The allocation rule of the surrogate learner of Paper A6, with its design held at a fixed
allocation `w`: the same warm start, forcing `rho_s = 1/sqrt(s+1)` toward the uniform design,
post-warm quota `W` and first maximiser of `W - N` as the ideal learner
(`LeanPaperA7IdealLearnerV1`); only the oracle is replaced by the constant `w`.

* `fixLearner w` -- the learner; it reads only the history of (query, observation) pairs;
* `fWarmRun` -- its run in any world is a `WarmRun`, so the tracking discrepancy of
  `LeanPaperA7WarmTrackV1` applies;
* `fCount_le_sqrt` -- **on a cell with `w e = 0` the count is at most `2 + 2 sqrt t / K` at
  every time `t`**, pathwise.  Only the forcing samples it.
* `fCount_le_amgm` -- the same bound in the linear form `2 + (t/s + s)/K`, for any `s > 0`,
  which is what an expectation argument consumes.

When `w` is the frozen surrogate's optimum at the true world (the four anchor cells), this is
the design the surrogate oracle returns once its estimate is accurate; using it makes the
learner an ORACLE-ALLOCATION diagnostic (the true extrema enter the design), and Paper A6 says
so.
-/

namespace CIGAMF.P13.PaperA6FixedDesign

open Finset MeasureTheory
open CIGAMF.P13.PaperA7Stream CIGAMF.P13.PaperA7Process CIGAMF.P13.PaperA7IdealLearner
open CIGAMF.P13.PaperA7WarmTrack CIGAMF.P13.PaperA7Tracking CIGAMF.P13.PaperA7OracleSelect

variable {E : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [Nonempty E]
variable (w : E → ℝ)

/-! ## 1. The learner -/

/-- The target of round `s`: the fixed design, mixed toward uniform. -/
noncomputable def fTarget (s : ℕ) : E → ℝ :=
  fun e => (1 - rho (E := E) s) * w e + rho (E := E) s * unif e

/-- The post-warm quota through round `t` (the code's `W`, which starts at `0`). -/
noncomputable def fQuota (t : ℕ) (e : E) : ℝ :=
  ∑ s ∈ range (t + 1), if Fintype.card E ≤ s then fTarget w s e else 0

/-- **The pick**: warm start, then the first maximiser of `W - N`. -/
noncomputable def fPick (t : ℕ) (h : Fin t → E × ℝ) : E :=
  if t < Fintype.card E then warmCell t else argmaxCell (fun e => fQuota w t e - hN h e)

theorem measurable_fPick (t : ℕ) : Measurable (fPick w t) := by
  unfold fPick
  by_cases ht : t < Fintype.card E
  · simp only [ht, if_true]; exact measurable_const
  · simp only [ht, if_false]
    exact measurable_argmaxCell.comp
      (measurable_pi_lambda _ fun e => measurable_const.sub (measurable_hN t e))

/-- **The fixed-design tracking learner.** -/
noncomputable def fixLearner : Learner E where
  rule t := fPick w t
  meas t := measurable_fPick w t

/-! ## 2. Its run -/

/-- The observed history of `t` rounds in world `theta`, noise `sigma`. -/
noncomputable def fRun (θ σ : E → ℝ) (t : ℕ) (ω : ℕ → ℝ) : Fin t → E × ℝ :=
  histF (fixLearner w) θ σ t (Xp t ω)

theorem hN_fRun (θ σ : E → ℝ) (t : ℕ) (ω : ℕ → ℝ) :
    hN (fRun w θ σ t ω) = Nc (fixLearner w) θ σ t ω := by
  funext e
  unfold hN fRun Nc NF
  push_cast
  rfl

theorem fNc_succ (θ σ : E → ℝ) (t : ℕ) (ω : ℕ → ℝ) (e : E) :
    Nc (fixLearner w) θ σ (t + 1) ω e
      = Nc (fixLearner w) θ σ t ω e + if e = fPick w t (fRun w θ σ t ω) then 1 else 0 := by
  have hq : qF (fixLearner w) θ σ t (Xp t ω) = fPick w t (fRun w θ σ t ω) := rfl
  unfold Nc
  rw [Xp_succ, NF_snoc, hq]
  push_cast
  by_cases h : e = fPick w t (fRun w θ σ t ω)
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem fNc_zero (θ σ : E → ℝ) (ω : ℕ → ℝ) (e : E) : Nc (fixLearner w) θ σ 0 ω e = 0 := by
  unfold Nc NF; simp

theorem fPick_warm (t : ℕ) (ht : t < Fintype.card E) (h : Fin t → E × ℝ) :
    fPick w t h = warmCell t := by
  unfold fPick; rw [if_pos ht]

/-- During the warm start the counts are the indicator of the cells already visited. -/
theorem fNc_warm_le (θ σ : E → ℝ) (ω : ℕ → ℝ) :
    ∀ t, t ≤ Fintype.card E → ∀ e,
      Nc (fixLearner w) θ σ t ω e = if ((Fintype.equivFin E e : Fin _) : ℕ) < t then 1 else 0
  | 0, _, e => by rw [fNc_zero]; simp
  | t + 1, ht, e => by
      rw [fNc_succ, fNc_warm_le θ σ ω t (by omega) e, fPick_warm w t (by omega)]
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

theorem fNc_warm (θ σ : E → ℝ) (ω : ℕ → ℝ) (e : E) :
    Nc (fixLearner w) θ σ (Fintype.card E) ω e = 1 := by
  rw [fNc_warm_le w θ σ ω _ le_rfl e, if_pos (Fintype.equivFin E e).isLt]

/-! ## 3. The run is a warm-started tracking run -/

theorem rho_nonneg (s : ℕ) : 0 ≤ rho (E := E) s := by unfold rho; split_ifs <;> positivity

theorem rho_le_one (s : ℕ) : rho (E := E) s ≤ 1 := by
  unfold rho; split_ifs
  · exact le_rfl
  · rw [div_le_one (Real.sqrt_pos.mpr (by positivity))]
    exact Real.one_le_sqrt.mpr (by linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)])

theorem fTarget_alloc (hw : IsAlloc w) (s : ℕ) : IsAlloc (fTarget w s) := by
  have hK : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  have hρ0 := rho_nonneg (E := E) s
  have hρ1 := rho_le_one (E := E) s
  refine ⟨fun e => ?_, ?_⟩
  · unfold fTarget unif
    exact add_nonneg (mul_nonneg (by linarith) (hw.1 e)) (mul_nonneg hρ0 (by positivity))
  · unfold fTarget unif
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, hw.2, sum_const, card_univ, nsmul_eq_mul]
    field_simp
    ring

/-- The run's post-warm targets. -/
noncomputable def fv (j : ℕ) : E → ℝ := fTarget w (Fintype.card E + (j - 1))

theorem fQuota_eq (k : ℕ) (e : E) :
    fQuota w (Fintype.card E + k) e = W (fv w) (k + 1) e := by
  unfold fQuota W fv
  rw [show Fintype.card E + k + 1 = Fintype.card E + (k + 1) by ring, sum_range_add]
  have hwarm : ∑ x ∈ range (Fintype.card E),
      (if Fintype.card E ≤ x then fTarget w x e else 0) = 0 :=
    sum_eq_zero fun x hx => if_neg (by have := mem_range.mp hx; omega)
  rw [hwarm, zero_add]
  refine sum_congr rfl fun j _ => ?_
  rw [if_pos (by omega)]
  rfl

/-- **The run as a warm-started tracking run.** -/
noncomputable def fWarmRun (hw : IsAlloc w) (θ σ : E → ℝ) (ω : ℕ → ℝ) : WarmRun E where
  v := fv w
  N k e := Nc (fixLearner w) θ σ (Fintype.card E + k) ω e
  pick j := fPick w (Fintype.card E + (j - 1)) (fRun w θ σ (Fintype.card E + (j - 1)) ω)
  vnn s e := (fTarget_alloc w hw _).1 e
  vsum s := (fTarget_alloc w hw _).2
  N0 e := fNc_warm w θ σ ω e
  Nstep t e := by
    show Nc (fixLearner w) θ σ (Fintype.card E + (t + 1)) ω e
      = Nc (fixLearner w) θ σ (Fintype.card E + t) ω e
        + if e = fPick w (Fintype.card E + t) (fRun w θ σ (Fintype.card E + t) ω) then 1 else 0
    rw [show Fintype.card E + (t + 1) = (Fintype.card E + t) + 1 by ring, fNc_succ]
  greedy t e := by
    have hg := argmaxCell_spec
      (fun e => fQuota w (Fintype.card E + t) e - hN (fRun w θ σ (Fintype.card E + t) ω) e) e
    have hp : fPick w (Fintype.card E + t) (fRun w θ σ (Fintype.card E + t) ω)
        = argmaxCell (fun e => fQuota w (Fintype.card E + t) e
            - hN (fRun w θ σ (Fintype.card E + t) ω) e) := by
      unfold fPick; rw [if_neg (by omega)]
    show W (fv w) (t + 1) e - Nc (fixLearner w) θ σ (Fintype.card E + t) ω e
      ≤ W (fv w) (t + 1) (fPick w (Fintype.card E + t) (fRun w θ σ (Fintype.card E + t) ω))
        - Nc (fixLearner w) θ σ (Fintype.card E + t) ω
            (fPick w (Fintype.card E + t) (fRun w θ σ (Fintype.card E + t) ω))
    rw [hp, ← fQuota_eq, ← fQuota_eq, ← hN_fRun]
    exact hg

/-! ## 4. The count of an ignored cell -/

/-- The tracking discrepancy, from above: no count exceeds its quota by more than two. -/
theorem fCount_le_quota (hw : IsAlloc w) (θ σ : E → ℝ) (ω : ℕ → ℝ) (k : ℕ) (e : E) :
    Nc (fixLearner w) θ σ (Fintype.card E + k) ω e ≤ 2 + W (fv w) k e := by
  have h := ((fWarmRun w hw θ σ ω).discrepancy k e).2
  have : (fWarmRun w hw θ σ ω).N k e = Nc (fixLearner w) θ σ (Fintype.card E + k) ω e := rfl
  have hv : (fWarmRun w hw θ σ ω).v = fv w := rfl
  rw [this, hv] at h
  linarith

/-- The quota of an ignored cell is the forcing only. -/
theorem fQuota_ignored (he : w e = 0) (k : ℕ) :
    W (fv w) k e ≤ 2 * Real.sqrt ((Fintype.card E + k : ℕ) : ℝ) / Fintype.card E := by
  have hK : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  unfold W
  have hterm : ∀ j ∈ range k, fv w (j + 1) e
      = 1 / Real.sqrt (((Fintype.card E + j : ℕ) : ℝ) + 1) * (1 / (Fintype.card E : ℝ)) := by
    intro j _
    unfold fv fTarget unif rho
    rw [he, show Fintype.card E + (j + 1 - 1) = Fintype.card E + j by omega,
      if_neg (by omega)]
    push_cast
    ring
  rw [sum_congr rfl hterm, ← sum_mul]
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
  rw [div_eq_mul_one_div (2 * _)]
  exact mul_le_mul_of_nonneg_right hle (by positivity)

/-- **The count of a cell the design ignores is at most `2 + 2 sqrt t / K`, at every time.** -/
theorem fCount_le_sqrt (hw : IsAlloc w) (θ σ : E → ℝ) (ω : ℕ → ℝ) (e : E) (he : w e = 0)
    (t : ℕ) :
    Nc (fixLearner w) θ σ t ω e ≤ 2 + 2 * Real.sqrt (t : ℝ) / Fintype.card E := by
  have hK : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  have hs : 0 ≤ 2 * Real.sqrt (t : ℝ) / Fintype.card E := by positivity
  rcases Nat.lt_or_ge t (Fintype.card E) with ht | ht
  · rw [fNc_warm_le w θ σ ω t ht.le e]
    split_ifs <;> linarith
  · obtain ⟨k, rfl⟩ : ∃ k, t = Fintype.card E + k := ⟨t - Fintype.card E, by omega⟩
    have h1 := fCount_le_quota w hw θ σ ω k e
    have h2 := fQuota_ignored w he k
    push_cast at h2 ⊢
    linarith

/-- The same bound, linear in `t`: `2 sqrt t <= t / s + s`. -/
theorem fCount_le_amgm (hw : IsAlloc w) (θ σ : E → ℝ) (ω : ℕ → ℝ) (e : E) (he : w e = 0)
    (t : ℕ) (s : ℝ) (hs : 0 < s) :
    Nc (fixLearner w) θ σ t ω e ≤ 2 + ((t : ℝ) / s + s) / Fintype.card E := by
  have hK : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  have h := fCount_le_sqrt w hw θ σ ω e he t
  have hamgm : 2 * Real.sqrt (t : ℝ) ≤ (t : ℝ) / s + s := by
    have hsq : Real.sqrt (t : ℝ) * Real.sqrt t = t := Real.mul_self_sqrt (Nat.cast_nonneg t)
    have h0 : 0 ≤ (Real.sqrt (t : ℝ) - s) ^ 2 := sq_nonneg _
    rw [div_add' _ _ _ hs.ne', le_div_iff₀ hs]
    nlinarith
  have : 2 * Real.sqrt (t : ℝ) / Fintype.card E ≤ ((t : ℝ) / s + s) / Fintype.card E :=
    div_le_div_of_nonneg_right hamgm hK.le
  linarith

#print axioms fWarmRun
#print axioms fCount_le_sqrt
#print axioms fCount_le_amgm

end CIGAMF.P13.PaperA6FixedDesign
