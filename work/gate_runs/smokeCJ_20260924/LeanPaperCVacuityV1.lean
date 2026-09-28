import «LeanPaperCFinalV1»

/-!
# Paper C: `CountFeasible` is empty, and the reduction built on it is vacuous

`CountFeasible` asks a layered flow to be supported on legal one-item steps **at every**
`k : ℕ`.  That condition has no unit flow at all, and this module proves it rather than
noting it.

The argument is a conservation count.  Write `served v = sum_tau v_tau` for the number of
items already served in the state `v`.  A legal step increases it by exactly one
(`served_step`), the flow's own `inflow`/`outflow` make the total mass one at every layer
(`mass_one`), and therefore

    E_k[served] = E_0[served] + k                                    (`served_grows`)

grows without bound -- while `served v <= d m` always (`served_le`).  Taking `k = dm+1`
gives `countFeasible_empty`.

**Consequences, stated plainly.**  `pathDecomposition_count_states` (`LeanPaperCFinalV1`)
and `pathDecomposition_at_count_states` (`LeanPaperCPathV1`) are conditionals whose
hypothesis is unsatisfiable, so neither says anything about any flow.  The gate stayed clean
throughout, because a conditional with contradictory hypotheses is still a theorem; that is
precisely why this file exists.

**The repair, not done here.**  Legality must be required only for `k < m`, with the flow
continued by self-loops afterwards, and the start/end conditions must be DERIVED from the
LP's own constraints (`0 <= v_j <= c_j`, `sum_j v_j = k`) rather than assumed.  The
combinatorial lemmas `legal_path_realised`, `matchPerm` and `hsec_count_states` survive that
change; the bridges `trajLaw_stepC` and the section need finite-horizon versions.
-/

namespace CIGAMF.P13.PaperCVacuity

open Finset
open CIGAMF.P13.PaperCBreakpoint
open CIGAMF.P13.CFinal

variable {d m : ℕ}

/-- How many items the state has served. -/
noncomputable def served (v : CState d m) : ℝ := ∑ τ, ((v τ : ℕ) : ℝ)

theorem served_nonneg (v : CState d m) : 0 ≤ served v :=
  Finset.sum_nonneg (fun _ _ => by positivity)

/-- **The count is bounded by the graph's size.** -/
theorem served_le (v : CState d m) : served v ≤ (d : ℝ) * (m : ℝ) := by
  unfold served
  have hterm : ∀ τ : Fin d, ((v τ : ℕ) : ℝ) ≤ (m : ℝ) := by
    intro τ
    have : ((v τ : ℕ)) ≤ m := by omega
    exact_mod_cast this
  calc ∑ τ : Fin d, ((v τ : ℕ) : ℝ)
      ≤ ∑ _τ : Fin d, (m : ℝ) := Finset.sum_le_sum (fun τ _ => hterm τ)
    _ = (d : ℝ) * (m : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **A legal step serves exactly one more item.** -/
theorem served_step (v w : CState d m) (h : StepC v w) : served w = served v + 1 := by
  classical
  obtain ⟨τ, hτ, hrest⟩ := h
  unfold served
  rw [← Finset.add_sum_erase _ (fun σ => ((w σ : ℕ) : ℝ)) (Finset.mem_univ τ),
    ← Finset.add_sum_erase _ (fun σ => ((v σ : ℕ) : ℝ)) (Finset.mem_univ τ)]
  have hsame : ∑ σ ∈ Finset.univ.erase τ, ((w σ : ℕ) : ℝ)
      = ∑ σ ∈ Finset.univ.erase τ, ((v σ : ℕ) : ℝ) := by
    refine Finset.sum_congr rfl (fun σ hσ => ?_)
    rw [hrest σ (Finset.ne_of_mem_erase hσ)]
  rw [hsame]
  have hcast : ((w τ : ℕ) : ℝ) = ((v τ : ℕ) : ℝ) + 1 := by
    rw [hτ]; push_cast; ring
  rw [hcast]
  ring

/-- **The total mass is one at every layer**, from `inflow` and `outflow` alone. -/
theorem mass_one (F : LayeredFlow (CState d m)) (h0 : ∑ v, F.x 0 v = 1) :
    ∀ k, ∑ v, F.x k v = 1 := by
  intro k
  induction k with
  | zero => exact h0
  | succ k ih =>
      have hstep : ∑ w, F.x (k + 1) w = ∑ v, F.x k v := by
        have hl : ∀ w, F.x (k + 1) w = ∑ v, F.f k v w := fun w => (F.inflow k w).symm
        rw [Finset.sum_congr rfl (fun w _ => hl w), Finset.sum_comm]
        exact Finset.sum_congr rfl (fun v _ => F.outflow k v)
      rw [hstep, ih]

/-- **So the expected count grows by one per layer, without bound.** -/
theorem served_grows (F : LayeredFlow (CState d m))
    (hF : ∀ k v w, ¬ StepC v w → F.f k v w = 0) (h0 : ∑ v, F.x 0 v = 1) :
    ∀ k, ∑ v, served v * F.x k v = (∑ v, served v * F.x 0 v) + (k : ℝ) := by
  classical
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have hexpand : ∑ w, served w * F.x (k + 1) w
          = ∑ u, (served u + 1) * F.x k u := by
        have hl : ∀ w, served w * F.x (k + 1) w = ∑ u, served w * F.f k u w := by
          intro w
          rw [← Finset.mul_sum, F.inflow k w]
        rw [Finset.sum_congr rfl (fun w _ => hl w), Finset.sum_comm]
        refine Finset.sum_congr rfl (fun u _ => ?_)
        have hterm : ∀ w, served w * F.f k u w = (served u + 1) * F.f k u w := by
          intro w
          by_cases hs : StepC u w
          · rw [served_step u w hs]
          · rw [hF k u w hs, mul_zero, mul_zero]
        rw [Finset.sum_congr rfl (fun w _ => hterm w), ← Finset.mul_sum, F.outflow k u]
      rw [hexpand]
      have hsplit : ∑ u, (served u + 1) * F.x k u
          = (∑ u, served u * F.x k u) + ∑ u, F.x k u := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun u _ => by ring)
      rw [hsplit, ih, mass_one F h0 k]
      push_cast
      ring

/-- **`CountFeasible` has no unit flow.**  Requiring legality at every `k` is inconsistent
with unit mass, so every theorem conditioned on it is vacuous. -/
theorem countFeasible_empty (ty : Fin m → Fin d) (F : LayeredFlow (CState d m))
    (h : CountFeasible ty F) : False := by
  obtain ⟨⟨h0, _⟩, hF, -⟩ := h
  set K : ℕ := d * m + 1 with hK
  have hgrow := served_grows F hF h0 K
  have hle : ∑ v, served v * F.x K v ≤ (d : ℝ) * (m : ℝ) := by
    calc ∑ v, served v * F.x K v
        ≤ ∑ v, ((d : ℝ) * (m : ℝ)) * F.x K v :=
          Finset.sum_le_sum (fun v _ =>
            mul_le_mul_of_nonneg_right (served_le v) (F.xnn K v))
      _ = (d : ℝ) * (m : ℝ) := by rw [← Finset.mul_sum, mass_one F h0 K, mul_one]
  have hnn : 0 ≤ ∑ v, served v * F.x 0 v :=
    Finset.sum_nonneg (fun v _ => mul_nonneg (served_nonneg v) (F.xnn 0 v))
  have hKR : ((K : ℕ) : ℝ) = (d : ℝ) * (m : ℝ) + 1 := by
    rw [hK]; push_cast; ring
  rw [hKR] at hgrow
  linarith [hgrow, hle, hnn]

/-! ## Audit -/

#print axioms served_le
#print axioms served_step
#print axioms mass_one
#print axioms served_grows
#print axioms countFeasible_empty

end CIGAMF.P13.PaperCVacuity
