import «LeanPaperA6SurrogateAtV1»

/-!
# Paper A6: two surrogates that agree at the truth and differ elsewhere

The audit of 2026-09-24 found that the manuscript used one name for two objects.

* The **centred surrogate at the truth**: `frozenValueC₀ M w`, the infimum over
  `FrozenAltC₀ = FrozenAltC ∩ Centred` of the energy at `thetaC`.  This is the object of the
  separation theorems (`centred_separation`, `frontier_two_sided`, and the sacrifice law).
* The **unrestricted surrogate at an estimate**: `frozenAt M mu w`, the infimum over
  `FrozenAltC` of the energy at `mu`, with no centring.  This is what the A6'' learner re-solves
  (`surOracle`, `est_cost_log_sq`).

This module proves what connects them and what separates them.

* `frozenGameAt_thetaC`: at the truth the two games have the same value, `9/512`.
* `frozenAt_unif_shift`: shift both A cells of the truth by `u`.  The unrestricted surrogate of
  the uniform-anchor design is still `9/512`, since the frozen margin does not see a common shift.
* `centred_unif_shift_ge`: the centred surrogate at the same estimate is at least
  `9/512 + u^2/4`.  The centring constraint `x_0 + x_1 = 0` must be restored, and restoring it
  costs `u^2/4`.
* `two_surrogates_differ`: for every `u /= 0` the two values differ.

So statements about A6'' concern the unrestricted surrogate re-solved at the estimate.  They
must not be transferred to the centred game without an argument.  Nothing here changes a
proved theorem; it fixes which object each theorem is about.
-/

namespace CIGAMF.P13.PaperA6TwoSurrogates

open Finset
open CIGAMF.P13.PaperACentred
open CIGAMF.P13.PaperARPair (Cell energy pairVar IsAlloc)
open CIGAMF.P13.PaperA6SurrogateAt

variable {r : ℕ}

/-- The CENTRED surrogate re-solved at an estimate: alternatives in `FrozenAltC₀`. -/
noncomputable def frozenCentredAt (M : ℝ) (μ w : Cell r → ℝ) : ℝ :=
  ⨅ lam : FrozenAltC₀ r, energy w (pairVar M) μ (lam : Cell r → ℝ)

/-- The truth with both `A` cells shifted by `u`. -/
noncomputable def muShift (r : ℕ) (u : ℝ) : Cell r → ℝ :=
  fun e => thetaC r e + Sum.elim (![u, u, 0, 0] : Fin 4 → ℝ) (fun _ => 0) e

theorem margin_thetaC : margin (thetaC r) = 3 / 4 := by
  unfold margin
  rw [thetaC_0, thetaC_1, thetaC_2, thetaC_3]
  norm_num

theorem margin_muShift (u : ℝ) : margin (muShift r u) = 3 / 4 := by
  unfold margin muShift
  simp only [Sum.elim_inl, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  rw [thetaC_0, thetaC_1, thetaC_2, thetaC_3]
  norm_num

/-- **At the truth the two games agree**: both are `9/512`. -/
theorem frozenGameAt_thetaC (M : ℝ) (hM : 0 < M) :
    frozenGameAt r M (thetaC r) = frozenGameC₀ r M := by
  rw [frozenGameAt_eq M hM _ (by rw [margin_thetaC]; norm_num), margin_thetaC,
    frozenGameC₀_eq r M hM]
  norm_num

theorem aMass_wUnifC : aMass (wUnifC r) = 1 := by
  unfold aMass wUnifC
  simp

/-- **The unrestricted surrogate does not see a common shift of the `A` cells.** -/
theorem frozenAt_unif_shift (M : ℝ) (hM : 0 < M) (u : ℝ) :
    frozenAt M (muShift r u) (wUnifC r) = 9 / 512 := by
  refine le_antisymm ?_ ?_
  · have h := frozenAt_le M hM (muShift r u) (wUnifC r) (wUnifC_isAlloc r).1
    rw [margin_muShift, aMass_wUnifC] at h
    linarith
  · have h := frozenAt_unif_ge M (muShift r u) (by rw [margin_muShift]; norm_num)
    rw [margin_muShift] at h
    linarith

/-- The energy of the uniform-anchor design is `(1/8)` of the squared displacement of the four
anchors. -/
theorem energy_unif (M : ℝ) (μ lam : Cell r → ℝ) :
    energy (wUnifC r) (pairVar M) μ lam
      = ((lam (Sum.inl 0) - μ (Sum.inl 0)) ^ 2 + (lam (Sum.inl 1) - μ (Sum.inl 1)) ^ 2
        + (lam (Sum.inl 2) - μ (Sum.inl 2)) ^ 2 + (lam (Sum.inl 3) - μ (Sum.inl 3)) ^ 2) / 8 := by
  unfold energy wUnifC pairVar
  rw [Fintype.sum_sum_type]
  simp [Fin.sum_univ_four]
  ring

/-- **The centred surrogate pays for restoring the centring**: at least `9/512 + u^2/4`. -/
theorem centred_unif_shift_ge (M : ℝ) (u : ℝ) [Nonempty (FrozenAltC₀ r)] :
    9 / 512 + u ^ 2 / 4 ≤ frozenCentredAt M (muShift r u) (wUnifC r) := by
  refine le_ciInf fun lam => ?_
  obtain ⟨lam, hfr, hc⟩ := lam
  show 9 / 512 + u ^ 2 / 4 ≤ energy (wUnifC r) (pairVar M) (muShift r u) lam
  rw [energy_unif]
  have hc0 := hc.1
  have hf : (lam (Sum.inl 1) - lam (Sum.inl 0)) - (lam (Sum.inl 3) - lam (Sum.inl 2)) ≤ 0 := hfr
  have e0 : muShift r u (Sum.inl 0) = -(1 / 2) + u := by
    simp [muShift, thetaC_0]
  have e1 : muShift r u (Sum.inl 1) = 1 / 2 + u := by
    simp [muShift, thetaC_1]
  have e2 : muShift r u (Sum.inl 2) = -(1 / 8) := by simp [muShift, thetaC_2]
  have e3 : muShift r u (Sum.inl 3) = 1 / 8 := by simp [muShift, thetaC_3]
  rw [e0, e1, e2, e3]
  set x0 := lam (Sum.inl 0)
  set x1 := lam (Sum.inl 1)
  set x2 := lam (Sum.inl 2)
  set x3 := lam (Sum.inl 3)
  -- d0 + d1 = -2u, and (d0 - d1) - d2 + d3 >= 3/4; Cauchy-Schwarz with weights (1/2, 1, 1)
  have hsum : (x0 - (-(1 / 2) + u)) + (x1 - (1 / 2 + u)) = -2 * u := by linarith [hc0]
  have hcon : 3 / 4 ≤ ((x0 - (-(1 / 2) + u)) - (x1 - (1 / 2 + u))) - (x2 - -(1 / 8))
      + (x3 - 1 / 8) := by linarith [hf]
  have key : ∀ X Y Z : ℝ, 3 / 4 ≤ X - Y + Z → 9 / 64 ≤ X ^ 2 / 2 + Y ^ 2 + Z ^ 2 := by
    intro X Y Z h
    have hsos : (X - Y + Z) ^ 2 ≤ 4 * (X ^ 2 / 2 + Y ^ 2 + Z ^ 2) := by
      nlinarith [sq_nonneg (X + Y - Z), sq_nonneg (Y + Z)]
    have hsq : 9 / 16 ≤ (X - Y + Z) ^ 2 := by nlinarith
    linarith
  have hk := key _ _ _ hcon
  have hsplit : ∀ a b : ℝ, a ^ 2 + b ^ 2 = ((a + b) ^ 2 + (a - b) ^ 2) / 2 := by
    intro a b; ring
  rw [hsplit (x0 - (-(1 / 2) + u)) (x1 - (1 / 2 + u)), hsum]
  nlinarith [hk]

/-- **The two surrogates differ off the truth.** -/
theorem two_surrogates_differ (M : ℝ) (hM : 0 < M) (u : ℝ) (hu : u ≠ 0)
    [Nonempty (FrozenAltC₀ r)] :
    frozenAt M (muShift r u) (wUnifC r) < frozenCentredAt M (muShift r u) (wUnifC r) := by
  rw [frozenAt_unif_shift M hM u]
  have h := centred_unif_shift_ge (r := r) M u
  have hu2 : 0 < u ^ 2 := by positivity
  linarith

instance (r : ℕ) : Nonempty (FrozenAltC₀ r) := ⟨⟨lamStar r, lamStar_frozenC₀ r⟩⟩

#print axioms frozenGameAt_thetaC
#print axioms frozenAt_unif_shift
#print axioms centred_unif_shift_ge
#print axioms two_surrogates_differ

end CIGAMF.P13.PaperA6TwoSurrogates
