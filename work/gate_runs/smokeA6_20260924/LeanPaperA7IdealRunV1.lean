import «LeanPaperA7IdealStopV1»
import «LeanPaperA7WarmTrackV1»

/-!
# Paper A7: the ideal learner's run IS a warm-started tracking run

Along every run of the ideal learner (`LeanPaperA7IdealLearnerV1`) in any world `theta`:

* `restr_runH` -- the history is prefix-consistent: the first `s` rounds of the run to `t` are
  the run to `s`.  So the quota the learner reads at round `t` is the sum of the targets it
  actually used (`quota_runH`);
* `Nc_succ_run` -- each round adds one sample to the cell the rule picked;
* `Nc_warm` -- after the warm start every cell has exactly one sample;
* `warmRunOf` -- hence the post-warm counts, targets and picks form a
  `LeanPaperA7WarmTrackV1.WarmRun`, with the greedy property coming from `pick_greedy`.

Consequences for the analysis (`run_track`, `run_count_ge`, `run_count_le`): the counts
track the average target within `2(K-1)/T` in `l1`, every count is at least
`sqrt T / K - (K - 1)`, and none exceeds `T`.
-/

namespace CIGAMF.P13.PaperA7IdealRun

open Finset MeasureTheory
open CIGAMF.P13.PaperA7Stream CIGAMF.P13.PaperA7Process CIGAMF.P13.PaperA7IdealLearner
open CIGAMF.P13.PaperA7IdealStop CIGAMF.P13.PaperA7WarmTrack CIGAMF.P13.PaperA7Tracking
open CIGAMF.P13.PaperA7OracleSelect

variable {E : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [Nonempty E]
variable {Ans : Type*} [Fintype Ans] [DecidableEq Ans] [Nonempty Ans]
variable (P : Spec E Ans)

/-! ## 1. Prefix consistency -/

theorem histF_restr (L : Learner E) (θ σ : E → ℝ) :
    ∀ (t s : ℕ) (hs : s ≤ t) (z : Fin t → ℝ),
      restr s hs (histF L θ σ t z) = histF L θ σ s (fun i => z (Fin.castLE hs i))
  | 0, s, hs, z => by
      have : s = 0 := by omega
      subst this
      funext i; exact i.elim0
  | t + 1, s, hs, z => by
      rcases Nat.lt_or_ge s (t + 1) with hlt | hge
      · have hst : s ≤ t := by omega
        have := histF_restr L θ σ t s hst (Fin.init z)
        funext i
        have hi : (Fin.castLE hs i : Fin (t + 1)) = Fin.castSucc (Fin.castLE hst i) := Fin.ext rfl
        unfold restr
        rw [hi]
        simp only [histF, Fin.snoc_castSucc]
        have h2 := congrFun this i
        unfold restr at h2
        rw [h2]
        rfl
      · have hst : s = t + 1 := by omega
        subst hst
        funext i
        unfold restr
        rfl

theorem restr_runH (θ : E → ℝ) (t s : ℕ) (hs : s ≤ t) (ω : ℕ → ℝ) :
    restr s hs (runH P θ t ω) = runH P θ s ω := by
  unfold runH
  rw [histF_restr]
  rfl

/-! ## 2. One round -/

theorem query_run (θ : E → ℝ) (t : ℕ) (ω : ℕ → ℝ) :
    qF (idealLearner P) θ P.σ t (Xp t ω) = pick P t (runH P θ t ω) := rfl

theorem Nc_succ_run (θ : E → ℝ) (t : ℕ) (ω : ℕ → ℝ) (e : E) :
    Nc (idealLearner P) θ P.σ (t + 1) ω e
      = Nc (idealLearner P) θ P.σ t ω e + if e = pick P t (runH P θ t ω) then 1 else 0 := by
  unfold Nc
  rw [Xp_succ, NF_snoc, query_run]
  push_cast
  by_cases h : e = pick P t (runH P θ t ω)
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem Nc_zero (θ : E → ℝ) (ω : ℕ → ℝ) (e : E) : Nc (idealLearner P) θ P.σ 0 ω e = 0 := by
  unfold Nc NF; simp

/-- During the warm start the counts are the indicator of the cells already visited. -/
theorem Nc_warm_le (θ : E → ℝ) (ω : ℕ → ℝ) :
    ∀ t, t ≤ Fintype.card E → ∀ e,
      Nc (idealLearner P) θ P.σ t ω e = if ((Fintype.equivFin E e : Fin _) : ℕ) < t then 1 else 0
  | 0, _, e => by rw [Nc_zero]; simp
  | t + 1, ht, e => by
      rw [Nc_succ_run, Nc_warm_le θ ω t (by omega) e, pick_warm P t (by omega)]
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

theorem Nc_warm (θ : E → ℝ) (ω : ℕ → ℝ) (e : E) :
    Nc (idealLearner P) θ P.σ (Fintype.card E) ω e = 1 := by
  rw [Nc_warm_le P θ ω _ le_rfl e, if_pos (Fintype.equivFin E e).isLt]

/-! ## 3. The quota the learner reads -/

theorem target_alloc (s : ℕ) (h : Fin s → E × ℝ) : IsAlloc (PaperA7IdealLearner.target P s h) := by
  have hK : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  have hρ0 : 0 ≤ rho (E := E) s := by unfold rho; split_ifs <;> positivity
  have hρ1 : rho (E := E) s ≤ 1 := by
    unfold rho; split_ifs
    · exact le_rfl
    · rw [div_le_one (Real.sqrt_pos.mpr (by positivity))]
      exact Real.one_le_sqrt.mpr (by linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)])
  have hd := design_alloc P s (hMu h)
  refine ⟨fun e => ?_, ?_⟩
  · unfold PaperA7IdealLearner.target unif
    exact add_nonneg (mul_nonneg (by linarith) (hd.1 e)) (mul_nonneg hρ0 (by positivity))
  · unfold PaperA7IdealLearner.target unif
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, hd.2, sum_const, card_univ, nsmul_eq_mul]
    field_simp
    ring

/-- The run's post-warm targets. -/
noncomputable def vRun (θ : E → ℝ) (ω : ℕ → ℝ) (j : ℕ) : E → ℝ :=
  PaperA7IdealLearner.target P (Fintype.card E + (j - 1)) (runH P θ (Fintype.card E + (j - 1)) ω)

theorem quota_runH' (θ : E → ℝ) (ω : ℕ → ℝ) (t : ℕ) (e : E) :
    quota P t (runH P θ t ω) e = ∑ s : Fin (t + 1),
      if Fintype.card E ≤ (s : ℕ) then PaperA7IdealLearner.target P s (runH P θ s ω) e else 0 := by
  unfold quota
  refine sum_congr rfl fun s _ => ?_
  rw [restr_runH]

theorem quota_runH (θ : E → ℝ) (ω : ℕ → ℝ) (k : ℕ) (e : E) :
    quota P (Fintype.card E + k) (runH P θ (Fintype.card E + k) ω) e
      = W (vRun P θ ω) (k + 1) e := by
  rw [quota_runH' P θ ω]
  unfold W vRun
  rw [Fin.sum_univ_eq_sum_range (fun s => if Fintype.card E ≤ s then
      PaperA7IdealLearner.target P s (runH P θ s ω) e else 0) (Fintype.card E + k + 1)]
  rw [show Fintype.card E + k + 1 = Fintype.card E + (k + 1) by ring, sum_range_add]
  have hwarm : ∑ x ∈ range (Fintype.card E),
      (if Fintype.card E ≤ x then PaperA7IdealLearner.target P x (runH P θ x ω) e else 0) = 0 :=
    sum_eq_zero fun x hx => if_neg (by have := mem_range.mp hx; omega)
  rw [hwarm, zero_add]
  refine sum_congr rfl fun j _ => ?_
  rw [if_pos (by omega)]
  rfl

/-! ## 4. The warm run -/

/-- **The run as a warm-started tracking run.** -/
noncomputable def warmRunOf (θ : E → ℝ) (ω : ℕ → ℝ) : WarmRun E where
  v := vRun P θ ω
  N k e := Nc (idealLearner P) θ P.σ (Fintype.card E + k) ω e
  pick j := pick P (Fintype.card E + (j - 1)) (runH P θ (Fintype.card E + (j - 1)) ω)
  vnn s e := (target_alloc P _ _).1 e
  vsum s := (target_alloc P _ _).2
  N0 e := Nc_warm P θ ω e
  Nstep t e := by
    show Nc (idealLearner P) θ P.σ (Fintype.card E + (t + 1)) ω e
      = Nc (idealLearner P) θ P.σ (Fintype.card E + t) ω e
        + if e = pick P (Fintype.card E + t) (runH P θ (Fintype.card E + t) ω) then 1 else 0
    rw [show Fintype.card E + (t + 1) = (Fintype.card E + t) + 1 by ring, Nc_succ_run]
  greedy t e := by
    have hg := pick_greedy P (Fintype.card E + t) (by omega) (runH P θ (Fintype.card E + t) ω) e
    rw [quota_runH, quota_runH, hN_runH] at hg
    exact hg

/-- The average target of the accumulation analysis is the learner's. -/
theorem hpost_run (θ : E → ℝ) (ω : ℕ → ℝ) (k : ℕ) (e : E) :
    PaperA7Accumulation.target (fun s => design P s (hMu (runH P θ s ω))) (rho (E := E)) unif
        (Fintype.card E + k) e = (warmRunOf P θ ω).v (k + 1) e := by
  show _ = vRun P θ ω (k + 1) e
  unfold vRun PaperA7Accumulation.target PaperA7IdealLearner.target
  rfl

theorem rho_warm (s : ℕ) (hs : s < Fintype.card E) : rho (E := E) s = 1 := by
  unfold rho; rw [if_pos hs]

/-- **Tracking of the actual run.** -/
theorem run_track (θ : E → ℝ) (ω : ℕ → ℝ) (k : ℕ) :
    ∑ e, |Nc (idealLearner P) θ P.σ (Fintype.card E + k) ω e / ((Fintype.card E + k : ℕ) : ℝ)
        - PaperA7Accumulation.avgTarget (fun s => design P s (hMu (runH P θ s ω))) (rho (E := E))
            unif (Fintype.card E + k) e|
      ≤ 2 * ((Fintype.card E : ℝ) - 1) / ((Fintype.card E + k : ℕ) : ℝ) :=
  warm_htrack (warmRunOf P θ ω) _ (rho (E := E)) unif (fun e => rfl) rho_warm (hpost_run P θ ω) k

/-- **Every count grows like `sqrt` of the time.** -/
theorem run_count_ge (θ : E → ℝ) (ω : ℕ → ℝ) (k : ℕ) (e : E) :
    Real.sqrt ((Fintype.card E + k : ℕ) : ℝ) / Fintype.card E - ((Fintype.card E : ℝ) - 1)
      ≤ Nc (idealLearner P) θ P.σ (Fintype.card E + k) ω e := by
  refine warm_count_ge (warmRunOf P θ ω) e (fun j => ?_) k
  show _ ≤ vRun P θ ω (j + 1) e
  unfold vRun PaperA7IdealLearner.target unif
  show _ ≤ (1 - rho (E := E) (Fintype.card E + j)) * design P (Fintype.card E + j)
      (hMu (runH P θ (Fintype.card E + j) ω)) e + rho (E := E) (Fintype.card E + j)
      * (1 / (Fintype.card E : ℝ))
  have hrho : rho (E := E) (Fintype.card E + j) = 1 / Real.sqrt (((Fintype.card E + j : ℕ) : ℝ) + 1) := by
    unfold rho; rw [if_neg (by omega)]
  rw [hrho]
  exact code_target_floor _ unif ((design_alloc P _ _).1) (fun e => rfl) (Fintype.card E + j) e

/-- No count exceeds the number of rounds. -/
theorem run_count_le (θ : E → ℝ) (ω : ℕ → ℝ) (t : ℕ) (e : E) :
    Nc (idealLearner P) θ P.σ t ω e ≤ t := by
  unfold Nc NF
  have : ∑ i : Fin t, (if (histF (idealLearner P) θ P.σ t (Xp t ω) i).1 = e then (1 : ℕ) else 0)
      ≤ ∑ _i : Fin t, (1 : ℕ) := sum_le_sum fun i _ => by split_ifs <;> norm_num
  rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at this
  exact_mod_cast this

#print axioms histF_restr
#print axioms Nc_warm
#print axioms warmRunOf
#print axioms run_track
#print axioms run_count_ge

end CIGAMF.P13.PaperA7IdealRun
