import «LeanPaperA7IdealLearnerV1»

/-!
# Paper A7: the ideal oracle selects the right answer, and its design is informative

At a round where the raw means `mu` are within `r` of the true world `theta` (coordinatewise),
and `theta` lies in the alternative of every answer except `Tst` (so `Tst` is the correct one
and every other answer's game is zero at `theta`):

* `GamT T mu` -- the game value of answer `T` at `mu`, in unit-variance coordinates; it is the
  least upper bound of the designs' information (`GamT_isLUB`) -- the alternatives are
  UNBOUNDED, only one alternative point is needed to bound it;
* `oracle_ge_game` -- the grid oracle's value is at least `c GamT Tst mu`, where
  `c = (1 - K/(k beta))(1 - beta)` is the grid factor of `net_value_ge`;
* `oracle_selects` -- every candidate of a wrong answer has value at most `r'^2/2`
  (`r' = r / sigma_min`), so once `r'^2/2 < c (Gamma - r' sqrt(2 Gamma))` the oracle picks
  `Tst`;
* `round_info` -- then the design used at this round has TRUE information at least
  `Gamma(theta) - (1 - c) U - 2 r' sqrt(2U)` for the correct answer.

This is the per-round input `hgood` of the accumulation theorem, derived from the learner's
own rule; nothing is assumed about the oracle beyond its definition.
-/

namespace CIGAMF.P13.PaperA7IdealSelect

open Finset
open CIGAMF.P13.PaperA7OracleSelect CIGAMF.P13.PaperA7NetOracle CIGAMF.P13.PaperA7DirectLower
open CIGAMF.P13.PaperA7IdealLearner CIGAMF.P13.PaperA7SqrtLip

variable {E : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [Nonempty E]
variable {Ans : Type*} [Fintype Ans] [DecidableEq Ans] [Nonempty Ans]
variable (P : Spec E Ans)

omit [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
theorem pen_le_sq (w x ν : E → ℝ) (hw : IsAlloc w) (D : ℝ) (hD : ∀ e, |x e - ν e| ≤ D) :
    pen w x ν ≤ D ^ 2 / 2 := by
  unfold pen
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc ∑ e, w e * (x e - ν e) ^ 2 ≤ ∑ e, w e * D ^ 2 := by
        refine sum_le_sum fun e _ => mul_le_mul_of_nonneg_left ?_ (hw.1 e)
        have := hD e
        have h0 := abs_nonneg (x e - ν e)
        rw [← sq_abs]
        exact pow_le_pow_left₀ h0 this 2
    _ = D ^ 2 := by rw [← sum_mul, hw.2, one_mul]

theorem unif_alloc : IsAlloc (unif (E := E)) := by
  have hK : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  refine ⟨fun e => by unfold unif; positivity, ?_⟩
  unfold unif
  rw [sum_const, card_univ, nsmul_eq_mul]; field_simp

/-- The game value of answer `T` at `mu`, in unit-variance coordinates. -/
noncomputable def GamT (T : Ans) (μ : E → ℝ) : ℝ :=
  sSup {v : ℝ | ∃ w : E → ℝ, IsAlloc w ∧ v = Jval (sc P.σ '' P.Alt T) w (sc P.σ μ)}

theorem GamT_isLUB (T : Ans) (μ : E → ℝ) :
    IsLUB {v : ℝ | ∃ w : E → ℝ, IsAlloc w ∧ v = Jval (sc P.σ '' P.Alt T) w (sc P.σ μ)}
      (GamT P T μ) := by
  obtain ⟨ν0, hν0⟩ := P.Alt_ne T
  refine isLUB_csSup ⟨_, unif, unif_alloc, rfl⟩ ⟨(∑ e, |sc P.σ μ e - sc P.σ ν0 e|) ^ 2 / 2, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  refine le_trans (csInf_le (Jval_bddBelow _ _ _ hw.1) ⟨sc P.σ ν0, ⟨ν0, hν0, rfl⟩, rfl⟩) ?_
  exact pen_le_sq w _ _ hw _ fun e =>
    single_le_sum (f := fun e => |sc P.σ μ e - sc P.σ ν0 e|) (fun _ _ => abs_nonneg _)
      (mem_univ e)

/-- **The oracle's value dominates the grid factor times the game.** -/
theorem oracle_ge_game (s : ℕ) (μ : E → ℝ) (Tst : Ans) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hkβ : (Fintype.card E : ℝ) ≤ P.kf s * β)
    (hc : 0 < (1 - (Fintype.card E : ℝ) / (P.kf s * β)) * (1 - β)) :
    (1 - (Fintype.card E : ℝ) / (P.kf s * β)) * (1 - β) * GamT P Tst μ
      ≤ Jval (sc P.σ '' P.Alt (oracle P (P.kf s) (P.kf_pos s) μ).1)
          (oracle P (P.kf s) (P.kf_pos s) μ).2.val (sc P.σ μ) := by
  set c := (1 - (Fintype.card E : ℝ) / (P.kf s * β)) * (1 - β) with hcdef
  set V := Jval (sc P.σ '' P.Alt (oracle P (P.kf s) (P.kf_pos s) μ).1)
    (oracle P (P.kf s) (P.kf_pos s) μ).2.val (sc P.σ μ) with hV
  have hub : ∀ v ∈ {v : ℝ | ∃ w : E → ℝ, IsAlloc w ∧ v = Jval (sc P.σ '' P.Alt Tst) w (sc P.σ μ)},
      v ≤ V / c := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨w', hw'mem, hw'⟩ := net_value_ge (sc P.σ '' P.Alt Tst) ((P.Alt_ne Tst).image _)
      (sc P.σ μ) (P.kf s) (P.kf_pos s) β hβ0 hβ1 hkβ w hw
    have hor := oracle_spec P (P.kf s) (P.kf_pos s) μ (Tst, ⟨w', hw'mem⟩)
    rw [le_div_iff₀ hc]
    have : c * Jval (sc P.σ '' P.Alt Tst) w (sc P.σ μ) ≤ V := le_trans (by rw [hcdef]; exact hw') hor
    linarith
  have := (GamT_isLUB P Tst μ).2 hub
  rw [le_div_iff₀ hc] at this
  linarith

/-- **A wrong answer's candidates carry at most the squared radius.** -/
theorem wrong_value_le (T : Ans) (θ μ : E → ℝ) (hθ : θ ∈ P.Alt T) (w : E → ℝ) (hw : IsAlloc w)
    (r' : ℝ) (hclose : ∀ e, |sc P.σ μ e - sc P.σ θ e| ≤ r') :
    Jval (sc P.σ '' P.Alt T) w (sc P.σ μ) ≤ r' ^ 2 / 2 :=
  le_trans (csInf_le (Jval_bddBelow _ _ _ hw.1) ⟨sc P.σ θ, ⟨θ, hθ, rfl⟩, rfl⟩)
    (pen_le_sq w _ _ hw r' hclose)

theorem sc_close (θ μ : E → ℝ) (σmin : ℝ) (hσmin : 0 < σmin) (hσ : ∀ e, σmin ≤ P.σ e) (r : ℝ)
    (hr0 : 0 ≤ r) (hr : ∀ e, |μ e - θ e| ≤ r) :
    ∀ e, |sc P.σ μ e - sc P.σ θ e| ≤ r / σmin := by
  have h := sc_radius (σmin ^ 2) (by positivity) P.σ P.σ_pos
    (fun e => pow_le_pow_left₀ hσmin.le (hσ e) 2) μ θ r hr0 hr
  rwa [Real.sqrt_sq hσmin.le] at h

/-- **Per-round information of the ideal learner's design, at the true world.** -/
theorem round_info (Tst : Ans) (θ : E → ℝ) (hwrong : ∀ T, T ≠ Tst → θ ∈ P.Alt T) (s : ℕ)
    (μ : E → ℝ) (σmin : ℝ) (hσmin : 0 < σmin) (hσ : ∀ e, σmin ≤ P.σ e) (r : ℝ) (hr0 : 0 ≤ r)
    (hr : ∀ e, |μ e - θ e| ≤ r) (U : ℝ) (hU1 : GamT P Tst θ ≤ U) (hU2 : GamT P Tst μ ≤ U)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hkβ : (Fintype.card E : ℝ) ≤ P.kf s * β)
    (hc : 0 < (1 - (Fintype.card E : ℝ) / (P.kf s * β)) * (1 - β))
    (hsel : (r / σmin) ^ 2 / 2 < (1 - (Fintype.card E : ℝ) / (P.kf s * β)) * (1 - β)
        * (GamT P Tst θ - (r / σmin) * Real.sqrt (2 * GamT P Tst θ))) :
    GamT P Tst θ - (1 - (1 - (Fintype.card E : ℝ) / (P.kf s * β)) * (1 - β)) * U
        - 2 * (r / σmin) * Real.sqrt (2 * U)
      ≤ Jval (sc P.σ '' P.Alt Tst) (design P s μ) (sc P.σ θ) := by
  set c := (1 - (Fintype.card E : ℝ) / (P.kf s * β)) * (1 - β) with hcdef
  set r' := r / σmin with hr'
  have hr'0 : 0 ≤ r' := div_nonneg hr0 hσmin.le
  have hclose := sc_close P θ μ σmin hσmin hσ r hr0 hr
  set Gt := GamT P Tst θ
  set Gh := GamT P Tst μ
  -- the estimated game is close to the true one
  have hG := Gamma_ge_of_close (sc P.σ '' P.Alt Tst) ((P.Alt_ne Tst).image _) (sc P.σ θ)
    (sc P.σ μ) r' hr'0 hclose Gt Gh (GamT_isLUB P Tst θ) (GamT_isLUB P Tst μ) ⟨unif, unif_alloc⟩
  -- the oracle's value
  have hV := oracle_ge_game P s μ Tst β hβ0 hβ1 hkβ hc
  set p := oracle P (P.kf s) (P.kf_pos s) μ with hp
  have hpalloc : IsAlloc p.2.val := netSet_alloc _ (P.kf_pos s) _ p.2.property
  -- the oracle selects the correct answer
  have hsel' : p.1 = Tst := by
    by_contra hne
    have hlow := wrong_value_le P p.1 θ μ (hwrong p.1 hne) p.2.val hpalloc r' hclose
    have : c * (Gt - r' * Real.sqrt (2 * Gt)) ≤ c * Gh := mul_le_mul_of_nonneg_left hG hc.le
    linarith
  -- the design's true information
  have hdes : design P s μ = p.2.val := rfl
  have hc1 : c ≤ 1 := by
    have h1 : (Fintype.card E : ℝ) / (P.kf s * β) ≥ 0 := by
      have : (0 : ℝ) < P.kf s := by exact_mod_cast P.kf_pos s
      positivity
    have : (1 - (Fintype.card E : ℝ) / (P.kf s * β)) ≤ 1 := by linarith
    have h2 : 1 - β ≤ 1 := by linarith
    have h3 : 0 ≤ 1 - β := by linarith
    calc c = (1 - (Fintype.card E : ℝ) / (P.kf s * β)) * (1 - β) := rfl
      _ ≤ 1 * 1 := by
          apply mul_le_mul this h2 h3 (by norm_num)
      _ = 1 := one_mul 1
  rw [hsel'] at hV
  have hpert := oracle_perturbation_free (sc P.σ '' P.Alt Tst) ((P.Alt_ne Tst).image _) p.2.val
    (sc P.σ θ) (sc P.σ μ) hpalloc r' hr'0 hclose Gt Gh (GamT_isLUB P Tst θ) (GamT_isLUB P Tst μ)
    U hU1 hU2 (c * Gh) ((1 - c) * Gh) hV (by linarith)
  rw [hdes]
  have hGh0 : 0 ≤ Gh := le_trans (Jval_nonneg' _ ((P.Alt_ne Tst).image _) _ _ unif_alloc.1)
    ((GamT_isLUB P Tst μ).1 ⟨unif, unif_alloc, rfl⟩)
  have : (1 - c) * Gh ≤ (1 - c) * U := mul_le_mul_of_nonneg_left hU2 (by linarith)
  linarith

#print axioms GamT_isLUB
#print axioms oracle_ge_game
#print axioms round_info

end CIGAMF.P13.PaperA7IdealSelect
