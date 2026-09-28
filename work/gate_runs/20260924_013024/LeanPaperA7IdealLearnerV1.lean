import «LeanPaperA7NetOracleV1»
import «LeanPaperA7DirectLowerV1»
import «LeanPaperA7ProcessV1»

/-!
# Paper A7: the ideal learner, as a measurable function of the observed history

The learner whose rate Theorem II is about.  It is `scripts/EXP_paperA7_learner.py` with the
two numerical approximations the code cannot certify replaced by mathematical objects:

* warm start: round `t < K` queries the `t`-th cell (`warmCell`), so after `K` rounds every
  cell has one sample, as in the code;
* at every later round the raw means `hMu` of the history are fed to the ORACLE: among all
  pairs (answer `T`, grid design `w` in `netSet k_t`), the first maximiser of
  `J_T(w, mu_hat)` in unit-variance coordinates (`oracle`, `argmaxIdx`) -- a measurable choice
  with a vanishing loss (`LeanPaperA7NetOracleV1`), in place of the code's floored bracket;
* forcing `rho_t = 1/sqrt(t+1)` toward the uniform design (`rho`, `target`), the quota `W` of
  POST-warm targets only (`quota`, `W = 0` after the warm start, as in the code), and the first
  maximiser of `W - N` (`pick`), as in the code's `argmax(W - N)`.

The world is not an argument of anything here: `rule` reads only the history of
(query, observation) pairs.  `idealLearner` packages it as a `Learner`, with its measurability
proved (`measurable_pick`).  The stopping rule and the analysis are in later modules.
-/

namespace CIGAMF.P13.PaperA7IdealLearner

open Finset MeasureTheory
open CIGAMF.P13.PaperA7OracleSelect CIGAMF.P13.PaperA7NetOracle CIGAMF.P13.PaperA7DirectLower
open CIGAMF.P13.PaperA7Process

variable {E : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [Nonempty E]
variable {Ans : Type*} [Fintype Ans] [DecidableEq Ans] [Nonempty Ans]

/-- The learner's fixed ingredients: known noise scales, the alternative of each answer, and
the grid schedule. -/
structure Spec (E Ans : Type*) where
  σ : E → ℝ
  σ_pos : ∀ e, 0 < σ e
  Alt : Ans → Set (E → ℝ)
  Alt_ne : ∀ T, (Alt T).Nonempty
  kf : ℕ → ℕ
  kf_pos : ∀ s, 0 < kf s

variable (P : Spec E Ans)

/-! ## 1. The history's counts, sums and means -/

def restr {t : ℕ} (s : ℕ) (hs : s ≤ t) (h : Fin t → E × ℝ) : Fin s → E × ℝ :=
  fun i => h (Fin.castLE hs i)

noncomputable def hN {t : ℕ} (h : Fin t → E × ℝ) (e : E) : ℝ :=
  ∑ i : Fin t, if (h i).1 = e then 1 else 0

noncomputable def hY {t : ℕ} (h : Fin t → E × ℝ) (e : E) : ℝ :=
  ∑ i : Fin t, if (h i).1 = e then (h i).2 else 0

noncomputable def hMu {t : ℕ} (h : Fin t → E × ℝ) (e : E) : ℝ := hY h e / hN h e

theorem measurable_restr {t : ℕ} (s : ℕ) (hs : s ≤ t) :
    Measurable (restr (E := E) s hs) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

theorem measurable_hN (t : ℕ) (e : E) : Measurable fun h : Fin t → E × ℝ => hN h e := by
  unfold hN
  refine Finset.measurable_sum _ fun i _ => Measurable.ite ?_ measurable_const measurable_const
  exact (measurable_fst.comp (measurable_pi_apply i)) (measurableSet_singleton e)

theorem measurable_hY (t : ℕ) (e : E) : Measurable fun h : Fin t → E × ℝ => hY h e := by
  unfold hY
  refine Finset.measurable_sum _ fun i _ => Measurable.ite ?_ ?_ measurable_const
  · exact (measurable_fst.comp (measurable_pi_apply i)) (measurableSet_singleton e)
  · exact measurable_snd.comp (measurable_pi_apply i)

theorem measurable_hMu (t : ℕ) : Measurable fun h : Fin t → E × ℝ => hMu h :=
  measurable_pi_lambda _ fun e => (measurable_hY t e).div (measurable_hN t e)

/-! ## 2. The oracle -/

/-- The oracle's candidates at grid size `k`: an answer and a grid design. -/
abbrev Pairs (E Ans : Type*) [Fintype E] [DecidableEq E] (k : ℕ) :=
  Ans × {w : E → ℝ // w ∈ netSet k}

theorem netSet_nonempty (k : ℕ) (hk : 0 < k) : (netSet (E := E) k).Nonempty := by
  have hK : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  have hu : IsAlloc (fun _ : E => 1 / (Fintype.card E : ℝ)) := by
    refine ⟨fun e => by positivity, ?_⟩
    rw [sum_const, card_univ, nsmul_eq_mul]; field_simp
  obtain ⟨w, hw, -⟩ := round_down k hk _ hu
  exact ⟨w, hw⟩

theorem card_pairs_pos (k : ℕ) (hk : 0 < k) : 0 < Fintype.card (Pairs E Ans k) := by
  obtain ⟨w, hw⟩ := netSet_nonempty (E := E) k hk
  obtain ⟨T⟩ := (inferInstance : Nonempty Ans)
  exact Fintype.card_pos_iff.mpr ⟨(T, ⟨w, hw⟩)⟩

/-- The score of candidate `i` at the estimate `mu`: its information in unit-variance
coordinates. -/
noncomputable def score (k : ℕ) (i : Fin (Fintype.card (Pairs E Ans k))) (μ : E → ℝ) : ℝ :=
  Jval (sc P.σ '' P.Alt ((Fintype.equivFin (Pairs E Ans k)).symm i).1)
    ((Fintype.equivFin (Pairs E Ans k)).symm i).2.val (sc P.σ μ)

theorem continuous_sc : Continuous (sc (E := E) P.σ) :=
  continuous_pi fun e => (continuous_apply e).div_const _

theorem measurable_score (k : ℕ) (hk : 0 < k) (i : Fin (Fintype.card (Pairs E Ans k))) :
    Measurable (score P k i) := by
  unfold score
  set p := (Fintype.equivFin (Pairs E Ans k)).symm i
  have halloc : IsAlloc p.2.val := netSet_alloc k hk p.2.val p.2.property
  exact ((continuous_Jval _ ((P.Alt_ne p.1).image _) p.2.val halloc).comp
    (continuous_sc P)).measurable

/-- **The oracle's choice**: the first maximiser among the candidates. -/
noncomputable def oracle (k : ℕ) (hk : 0 < k) (μ : E → ℝ) : Pairs E Ans k :=
  (Fintype.equivFin (Pairs E Ans k)).symm (argmaxIdx (card_pairs_pos k hk) (score P k) μ)

theorem oracle_spec (k : ℕ) (hk : 0 < k) (μ : E → ℝ) (p : Pairs E Ans k) :
    Jval (sc P.σ '' P.Alt p.1) p.2.val (sc P.σ μ)
      ≤ Jval (sc P.σ '' P.Alt (oracle P k hk μ).1) (oracle P k hk μ).2.val (sc P.σ μ) := by
  have h := argmaxIdx_spec (card_pairs_pos (E := E) (Ans := Ans) k hk) (score P k) μ
    (Fintype.equivFin (Pairs E Ans k) p)
  unfold score at h
  simp only [Equiv.symm_apply_apply] at h
  exact h

/-- The design the oracle returns at round `s`. -/
noncomputable def design (s : ℕ) (μ : E → ℝ) : E → ℝ :=
  (oracle P (P.kf s) (P.kf_pos s) μ).2.val

theorem design_alloc (s : ℕ) (μ : E → ℝ) : IsAlloc (design P s μ) :=
  netSet_alloc _ (P.kf_pos s) _ (oracle P (P.kf s) (P.kf_pos s) μ).2.property

theorem measurable_design (s : ℕ) : Measurable (design (Ans := Ans) P s) := by
  unfold design oracle
  have hidx := measurable_argmaxIdx (card_pairs_pos (E := E) (Ans := Ans) (P.kf s) (P.kf_pos s))
    (score P (P.kf s)) fun i => measurable_score P (P.kf s) (P.kf_pos s) i
  exact (Measurable.of_discrete (f := fun i : Fin (Fintype.card (Pairs E Ans (P.kf s))) =>
    ((Fintype.equivFin (Pairs E Ans (P.kf s))).symm i).2.val)).comp hidx

/-! ## 3. Forcing, targets, quota and the pick -/

/-- The forcing weight: `1` during the warm start, `1/sqrt(t+1)` after. -/
noncomputable def rho (s : ℕ) : ℝ :=
  if s < Fintype.card E then 1 else 1 / Real.sqrt ((s : ℝ) + 1)

/-- The uniform design. -/
noncomputable def unif : E → ℝ := fun _ => 1 / (Fintype.card E : ℝ)

/-- The target of round `s`, from the history of its first `s` rounds. -/
noncomputable def target (s : ℕ) (h : Fin s → E × ℝ) : E → ℝ :=
  fun e => (1 - rho (E := E) s) * design P s (hMu h) e + rho (E := E) s * unif e

/-- The post-warm quota through round `t` (the code's `W`, which starts at `0`). -/
noncomputable def quota (t : ℕ) (h : Fin t → E × ℝ) (e : E) : ℝ :=
  ∑ s : Fin (t + 1), if Fintype.card E ≤ (s : ℕ) then
    target P s (restr s (Nat.lt_succ_iff.mp s.isLt) h) e else 0

/-- The `t`-th cell of a fixed enumeration (the warm start). -/
noncomputable def warmCell (t : ℕ) : E :=
  (Fintype.equivFin E).symm ⟨t % Fintype.card E, Nat.mod_lt _ Fintype.card_pos⟩

/-- The first maximiser of a score vector over the cells. -/
noncomputable def argmaxCell (v : E → ℝ) : E :=
  (Fintype.equivFin E).symm
    (argmaxIdx Fintype.card_pos (fun i (x : E → ℝ) => x ((Fintype.equivFin E).symm i)) v)

theorem argmaxCell_spec (v : E → ℝ) (e : E) : v e ≤ v (argmaxCell v) := by
  have h := argmaxIdx_spec (Fintype.card_pos (α := E))
    (fun i (x : E → ℝ) => x ((Fintype.equivFin E).symm i)) v (Fintype.equivFin E e)
  simp only [Equiv.symm_apply_apply] at h
  exact h

theorem measurable_argmaxCell : Measurable (argmaxCell (E := E)) := by
  unfold argmaxCell
  have hidx := measurable_argmaxIdx (Fintype.card_pos (α := E))
    (fun i (x : E → ℝ) => x ((Fintype.equivFin E).symm i)) fun i => measurable_pi_apply _
  exact (Measurable.of_discrete (f := fun i : Fin (Fintype.card E) =>
    (Fintype.equivFin E).symm i)).comp hidx

/-- **The pick**: warm start, then the first maximiser of `W - N`. -/
noncomputable def pick (t : ℕ) (h : Fin t → E × ℝ) : E :=
  if t < Fintype.card E then warmCell t else argmaxCell (fun e => quota P t h e - hN h e)

theorem measurable_target (s : ℕ) : Measurable fun h : Fin s → E × ℝ => target P s h := by
  unfold target
  refine measurable_pi_lambda _ fun e => ?_
  refine (measurable_const.mul ?_).add measurable_const
  exact (measurable_pi_apply e).comp ((measurable_design P s).comp (measurable_hMu s))

theorem measurable_quota (t : ℕ) (e : E) : Measurable fun h : Fin t → E × ℝ => quota P t h e := by
  unfold quota
  refine Finset.measurable_sum _ fun s _ => ?_
  by_cases hs : Fintype.card E ≤ (s : ℕ)
  · simp only [hs, if_true]
    exact (measurable_pi_apply e).comp ((measurable_target P s).comp (measurable_restr _ _))
  · simp only [hs, if_false]
    exact measurable_const

/-- **The rule is measurable.** -/
theorem measurable_pick (t : ℕ) : Measurable (pick P t) := by
  unfold pick
  by_cases ht : t < Fintype.card E
  · simp only [ht, if_true]; exact measurable_const
  · simp only [ht, if_false]
    exact measurable_argmaxCell.comp
      (measurable_pi_lambda _ fun e => (measurable_quota P t e).sub (measurable_hN t e))

/-- **The ideal learner.** -/
noncomputable def idealLearner : Learner E where
  rule t := pick P t
  meas t := measurable_pick P t

/-- The pick after the warm start is greedy for `W - N`. -/
theorem pick_greedy (t : ℕ) (ht : Fintype.card E ≤ t) (h : Fin t → E × ℝ) (e : E) :
    quota P t h e - hN h e ≤ quota P t h (pick P t h) - hN h (pick P t h) := by
  unfold pick
  rw [if_neg (not_lt.mpr ht)]
  exact argmaxCell_spec (fun e => quota P t h e - hN h e) e

theorem pick_warm (t : ℕ) (ht : t < Fintype.card E) (h : Fin t → E × ℝ) :
    pick P t h = warmCell t := by
  unfold pick; rw [if_pos ht]

#print axioms measurable_design
#print axioms oracle_spec
#print axioms measurable_pick
#print axioms pick_greedy

end CIGAMF.P13.PaperA7IdealLearner
