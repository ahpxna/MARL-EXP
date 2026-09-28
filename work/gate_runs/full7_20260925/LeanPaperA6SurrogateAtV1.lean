import «LeanPaperA6OracleLearnerV1»
import «LeanPaperACentredV1»

/-!
# Paper A6: the frozen surrogate RE-SOLVED at an estimate

A learner that uses the frozen surrogate computes it at its current estimate `mu`: it freezes
the estimate's extremum cells and solves the surrogate game there.  When the estimate's
extrema are the four anchors (`AnchorsExtreme mu`) and it retains `A`
(`0 < margin mu`, the frozen range gap), that game is

    frozenAt M mu w = inf over the frozen alternatives `FrozenAltC` of the energy at `mu`.

Proved here, at EVERY such estimate, not only at `thetaC`:

* `frozenAt_le` -- `frozenAt M mu w <= margin(mu)^2/32 * aMass w` (the shift of the four anchors
  by `(+g/4, -g/4, -g/4, +g/4)`);
* `frozenAt_unif_ge` -- the uniform-anchor design attains `margin(mu)^2 / 32`;
* `frozenGameAt_eq` -- the surrogate game's value at `mu` is `margin(mu)^2 / 32`;
* `starvation_at` -- **every exact optimum of the surrogate at `mu` puts zero weight on every
  middle cell**;
* `close_extreme` -- an estimate within `1/16` of `thetaC` in every cell has the anchors as its
  extrema and retains `A`.

The concrete oracle `surOracle`: the uniform-anchor design when the estimate's extrema are the
anchors and it retains `A` -- where that design is an exact optimum of the surrogate re-solved
at the estimate (`surD_exact`) -- and the uniform design otherwise.  Its middle weight vanishes
whenever the estimate is within `1/16` of the truth (`surD_middle_zero`).
-/

namespace CIGAMF.P13.PaperA6SurrogateAt

open Finset MeasureTheory
open CIGAMF.P13.PaperACentred
open CIGAMF.P13.PaperARPair (Cell energy pairVar IsAlloc)
open CIGAMF.P13.PaperA6OracleLearner (Oracle)

variable {r : ℕ}

/-! ## 1. The frozen margin and the anchors as extrema -/

/-- `A`'s frozen range minus `B`'s, the anchors frozen. -/
def margin (μ : Cell r → ℝ) : ℝ :=
  (μ (Sum.inl 1) - μ (Sum.inl 0)) - (μ (Sum.inl 3) - μ (Sum.inl 2))

/-- The estimate's extrema, in both arms, are the four anchors. -/
def AnchorsExtreme (μ : Cell r → ℝ) : Prop :=
  μ (Sum.inl 0) < μ (Sum.inl 1) ∧ μ (Sum.inl 2) < μ (Sum.inl 3) ∧
    ∀ p : Fin r × Bool, μ (Sum.inl 2) < μ (Sum.inr p) ∧ μ (Sum.inr p) < μ (Sum.inl 3)

theorem measurable_coord (e : Cell r) : Measurable fun μ : Cell r → ℝ => μ e :=
  measurable_pi_apply e

theorem measurable_margin : Measurable (margin (r := r)) := by
  unfold margin
  exact ((measurable_coord _).sub (measurable_coord _)).sub
    ((measurable_coord _).sub (measurable_coord _))

theorem measurableSet_good :
    MeasurableSet {μ : Cell r → ℝ | AnchorsExtreme μ ∧ 0 < margin μ} := by
  have hS : MeasurableSet
      (({μ : Cell r → ℝ | μ (Sum.inl 0) < μ (Sum.inl 1)} ∩ ({μ | μ (Sum.inl 2) < μ (Sum.inl 3)}
        ∩ ⋂ p : Fin r × Bool, ({μ | μ (Sum.inl 2) < μ (Sum.inr p)}
          ∩ {μ | μ (Sum.inr p) < μ (Sum.inl 3)}))) ∩ {μ | 0 < margin μ}) :=
    ((measurableSet_lt (measurable_coord _) (measurable_coord _)).inter
      ((measurableSet_lt (measurable_coord _) (measurable_coord _)).inter
        (MeasurableSet.iInter fun p =>
          (measurableSet_lt (measurable_coord _) (measurable_coord _)).inter
            (measurableSet_lt (measurable_coord _) (measurable_coord _))))).inter
      (measurableSet_lt measurable_const measurable_margin)
  convert hS using 1
  ext μ
  simp only [AnchorsExtreme, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]

/-- **An estimate within `1/16` of `thetaC` has the anchors as extrema and retains `A`.** -/
theorem close_extreme (μ : Cell r → ℝ) (hμ : ∀ e, |μ e - thetaC r e| < 1 / 16) :
    AnchorsExtreme μ ∧ 0 < margin μ := by
  have h0 := abs_lt.mp (hμ (Sum.inl 0))
  have h1 := abs_lt.mp (hμ (Sum.inl 1))
  have h2 := abs_lt.mp (hμ (Sum.inl 2))
  have h3 := abs_lt.mp (hμ (Sum.inl 3))
  rw [thetaC_0] at h0
  rw [thetaC_1] at h1
  rw [thetaC_2] at h2
  rw [thetaC_3] at h3
  refine ⟨⟨by linarith [h0.2, h1.1], by linarith [h2.2, h3.1], fun p => ?_⟩, ?_⟩
  · have hp := abs_lt.mp (hμ (Sum.inr p))
    rw [thetaC_pair] at hp
    exact ⟨by linarith [h2.2, hp.1], by linarith [hp.2, h3.1]⟩
  · unfold margin
    linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

/-! ## 2. The surrogate game at the estimate -/

/-- The frozen surrogate's value of design `w`, re-solved at the estimate `μ`. -/
noncomputable def frozenAt (M : ℝ) (μ w : Cell r → ℝ) : ℝ :=
  ⨅ lam : FrozenAltC r, energy w (pairVar M) μ (lam : Cell r → ℝ)

/-- The frozen surrogate's game at the estimate `μ`. -/
noncomputable def frozenGameAt (r : ℕ) (M : ℝ) (μ : Cell r → ℝ) : ℝ :=
  ⨆ w : {w : Cell r → ℝ // IsAlloc w}, frozenAt M μ (w : Cell r → ℝ)

theorem energyAt_nonneg (M : ℝ) (hM : 0 < M) (μ w lam : Cell r → ℝ) (hw : ∀ e, 0 ≤ w e) :
    0 ≤ energy w (pairVar M) μ lam := by
  unfold energy
  have h : 0 ≤ ∑ e, w e * (lam e - μ e) ^ 2 / pairVar M e :=
    Finset.sum_nonneg fun e _ =>
      div_nonneg (mul_nonneg (hw e) (sq_nonneg _)) (pairVarC_pos M hM e).le
  linarith

theorem bddBelowAt (M : ℝ) (hM : 0 < M) (μ w : Cell r → ℝ) (hw : ∀ e, 0 ≤ w e) :
    BddBelow (Set.range (fun lam : FrozenAltC r => energy w (pairVar M) μ (lam : Cell r → ℝ))) :=
  ⟨0, by rintro x ⟨lam, rfl⟩; exact energyAt_nonneg M hM μ w _ hw⟩

/-- The anchors shifted by `(+g/4, -g/4, -g/4, +g/4)`, `g` the margin. -/
noncomputable def witAt (μ : Cell r → ℝ) : Cell r → ℝ :=
  fun e => μ e + Sum.elim (![margin μ / 4, -(margin μ / 4), -(margin μ / 4), margin μ / 4] :
    Fin 4 → ℝ) (fun _ => 0) e

theorem witAt_mem (μ : Cell r → ℝ) : witAt μ ∈ FrozenAltC r := by
  show (witAt μ (Sum.inl 1) - witAt μ (Sum.inl 0)) - (witAt μ (Sum.inl 3) - witAt μ (Sum.inl 2))
    ≤ 0
  simp only [witAt, Sum.elim_inl, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  unfold margin
  linarith

theorem energy_witAt (M : ℝ) (μ w : Cell r → ℝ) :
    energy w (pairVar M) μ (witAt μ) = margin μ ^ 2 / 32 * aMass w := by
  unfold energy aMass
  rw [Fintype.sum_sum_type]
  have hmid : ∑ p : Fin r × Bool, w (Sum.inr p) * (witAt μ (Sum.inr p) - μ (Sum.inr p)) ^ 2
      / pairVar M (Sum.inr p) = 0 :=
    Finset.sum_eq_zero fun p _ => by simp [witAt]
  rw [hmid, add_zero, Fin.sum_univ_four, Fin.sum_univ_four]
  simp only [witAt, Sum.elim_inl, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three, add_sub_cancel_left]
  have hv : ∀ i : Fin 4, pairVar M (Sum.inl i : Cell r) = 1 := fun _ => rfl
  rw [hv, hv, hv, hv]
  ring

/-- **At most `margin^2/32` times the anchor mass.** -/
theorem frozenAt_le (M : ℝ) (hM : 0 < M) (μ w : Cell r → ℝ) (hw : ∀ e, 0 ≤ w e) :
    frozenAt M μ w ≤ margin μ ^ 2 / 32 * aMass w := by
  have h := ciInf_le (bddBelowAt M hM μ w hw) (⟨witAt μ, witAt_mem μ⟩ : FrozenAltC r)
  rw [energy_witAt] at h
  exact h

theorem energy_unifAt (M : ℝ) (μ lam : Cell r → ℝ) :
    energy (wUnifC r) (pairVar M) μ lam
      = ((lam (Sum.inl 0) - μ (Sum.inl 0)) ^ 2 + (lam (Sum.inl 1) - μ (Sum.inl 1)) ^ 2
        + (lam (Sum.inl 2) - μ (Sum.inl 2)) ^ 2 + (lam (Sum.inl 3) - μ (Sum.inl 3)) ^ 2) / 8 := by
  unfold energy
  rw [Fintype.sum_sum_type]
  have hmid : ∑ p : Fin r × Bool, wUnifC r (Sum.inr p) * (lam (Sum.inr p) - μ (Sum.inr p)) ^ 2
      / pairVar M (Sum.inr p) = 0 :=
    Finset.sum_eq_zero fun p _ => by simp [wUnifC]
  rw [hmid, add_zero, Fin.sum_univ_four]
  have hv : ∀ i : Fin 4, pairVar M (Sum.inl i : Cell r) = 1 := fun _ => rfl
  have hw : ∀ i : Fin 4, wUnifC r (Sum.inl i) = 1 / 4 := fun _ => rfl
  rw [hv, hv, hv, hv, hw, hw, hw, hw]
  ring

/-- **The uniform-anchor design attains `margin^2/32`.** -/
theorem frozenAt_unif_ge (M : ℝ) (μ : Cell r → ℝ) (hg : 0 ≤ margin μ) :
    margin μ ^ 2 / 32 ≤ frozenAt M μ (wUnifC r) := by
  refine le_ciInf fun lam => ?_
  obtain ⟨lam, hlam⟩ := lam
  show margin μ ^ 2 / 32 ≤ energy (wUnifC r) (pairVar M) μ lam
  rw [energy_unifAt]
  have hcon : (lam (Sum.inl 1) - lam (Sum.inl 0)) - (lam (Sum.inl 3) - lam (Sum.inl 2)) ≤ 0 :=
    hlam
  have h4 := four_sq_lower_gen (lam (Sum.inl 0) - μ (Sum.inl 0)) (lam (Sum.inl 1) - μ (Sum.inl 1))
    (lam (Sum.inl 3) - μ (Sum.inl 3)) (lam (Sum.inl 2) - μ (Sum.inl 2)) (margin μ) hg
    (by unfold margin; linarith)
  linarith

theorem bddAboveAt (M : ℝ) (hM : 0 < M) (μ : Cell r → ℝ) :
    BddAbove (Set.range (fun w : {w : Cell r → ℝ // IsAlloc w} =>
      frozenAt M μ (w : Cell r → ℝ))) := by
  refine ⟨margin μ ^ 2 / 32, ?_⟩
  rintro x ⟨w, rfl⟩
  have h := frozenAt_le M hM μ (w : Cell r → ℝ) w.2.1
  have ha := aMass_le_one (w : Cell r → ℝ) w.2
  have hg : 0 ≤ margin μ ^ 2 / 32 := by positivity
  nlinarith

/-- **The surrogate game at the estimate is `margin^2/32`.** -/
theorem frozenGameAt_eq (M : ℝ) (hM : 0 < M) (μ : Cell r → ℝ) (hg : 0 ≤ margin μ) :
    frozenGameAt r M μ = margin μ ^ 2 / 32 := by
  refine le_antisymm (ciSup_le fun w => ?_) ?_
  · have h := frozenAt_le M hM μ (w : Cell r → ℝ) w.2.1
    have ha := aMass_le_one (w : Cell r → ℝ) w.2
    have hg2 : 0 ≤ margin μ ^ 2 / 32 := by positivity
    nlinarith
  · exact le_trans (frozenAt_unif_ge M μ hg)
      (le_ciSup (bddAboveAt M hM μ) ⟨wUnifC r, wUnifC_isAlloc r⟩)

/-- **Every exact optimum of the surrogate re-solved at the estimate starves every middle
cell.** -/
theorem starvation_at (M : ℝ) (hM : 0 < M) (μ : Cell r → ℝ) (hg : 0 < margin μ)
    (w : Cell r → ℝ) (hw : IsAlloc w) (hopt : frozenAt M μ w = frozenGameAt r M μ) :
    ∀ p : Fin r × Bool, w (Sum.inr p) = 0 := by
  rw [frozenGameAt_eq M hM μ hg.le] at hopt
  have hle := frozenAt_le M hM μ w hw.1
  rw [hopt] at hle
  have hpos : 0 < margin μ ^ 2 / 32 := by positivity
  have ha1 : 1 ≤ aMass w := by
    by_contra hc
    push_neg at hc
    nlinarith
  have hmid : ∑ p : Fin r × Bool, w (Sum.inr p) = 0 := by
    have := aMass_add_middle w hw
    have := aMass_le_one w hw
    linarith
  intro p
  exact (Finset.sum_eq_zero_iff_of_nonneg fun q _ => hw.1 (Sum.inr q)).mp hmid p (mem_univ p)

/-! ## 3. The oracle that re-solves the surrogate at the estimate -/

open Classical in
/-- The uniform-anchor design where it is the surrogate's exact optimum at the estimate, and
the uniform design elsewhere. -/
noncomputable def surD (μ : Cell r → ℝ) : Cell r → ℝ :=
  if AnchorsExtreme μ ∧ 0 < margin μ then wUnifC r else fun _ => 1 / (Fintype.card (Cell r) : ℝ)

theorem measurable_surD : Measurable (surD (r := r)) := by
  classical
  unfold surD
  exact Measurable.ite measurableSet_good measurable_const measurable_const

theorem surD_alloc (μ : Cell r → ℝ) : IsAlloc (surD μ) := by
  classical
  unfold surD
  split_ifs
  · exact wUnifC_isAlloc r
  · have hK : (0 : ℝ) < Fintype.card (Cell r) := by exact_mod_cast Fintype.card_pos
    refine ⟨fun _ => by positivity, ?_⟩
    rw [sum_const, card_univ, nsmul_eq_mul]
    field_simp

/-- **The surrogate oracle**, as an `Oracle` of the tracking learner. -/
noncomputable def surOracle (r : ℕ) : Oracle (Cell r) where
  D := surD
  meas := measurable_surD
  alloc := surD_alloc

/-- **Where it answers, it is the surrogate's exact optimum at the estimate.** -/
theorem surD_exact (M : ℝ) (hM : 0 < M) (μ : Cell r → ℝ) (hμ : AnchorsExtreme μ ∧ 0 < margin μ) :
    frozenAt M μ (surD μ) = frozenGameAt r M μ := by
  classical
  have hs : surD μ = wUnifC r := by unfold surD; rw [if_pos hμ]
  rw [hs, frozenGameAt_eq M hM μ hμ.2.le]
  refine le_antisymm ?_ (frozenAt_unif_ge M μ hμ.2.le)
  have h := frozenAt_le M hM μ (wUnifC r) (wUnifC_isAlloc r).1
  have ha : aMass (wUnifC r) = 1 := by
    unfold aMass wUnifC; simp
  rw [ha, mul_one] at h
  exact h

/-- **Close to the truth, the surrogate oracle puts nothing on the middles.** -/
theorem surD_middle_zero (μ : Cell r → ℝ) (hμ : ∀ e, |μ e - thetaC r e| < 1 / 16)
    (p : Fin r × Bool) : surD μ (Sum.inr p) = 0 := by
  classical
  have hs : surD μ = wUnifC r := by unfold surD; rw [if_pos (close_extreme μ hμ)]
  rw [hs]; rfl

/-- **The same for ANY oracle that returns an exact surrogate optimum where the anchors are the
estimate's extrema** -- the property is the surrogate's, not this implementation's. -/
theorem optimal_oracle_middle_zero (M : ℝ) (hM : 0 < M) (O : Oracle (Cell r))
    (hO : ∀ μ, AnchorsExtreme μ ∧ 0 < margin μ → frozenAt M μ (O.D μ) = frozenGameAt r M μ)
    (μ : Cell r → ℝ) (hμ : ∀ e, |μ e - thetaC r e| < 1 / 16) (p : Fin r × Bool) :
    O.D μ (Sum.inr p) = 0 := by
  have hc := close_extreme μ hμ
  exact starvation_at M hM μ hc.2 (O.D μ) (O.alloc μ) (hO μ hc) p

#print axioms close_extreme
#print axioms frozenGameAt_eq
#print axioms starvation_at
#print axioms surD_exact
#print axioms optimal_oracle_middle_zero

end CIGAMF.P13.PaperA6SurrogateAt
