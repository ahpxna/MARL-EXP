import «LeanPaperCHorizonSecV1»
import «LeanPaperCNamingV1»

/-!
# Paper C: the ranking law's own flow, landing inside the repaired domain

`LeanPaperCNamingV1` builds `flowX` / `flowF` from a ranking law and proves conservation and
transport, but it never assembles them into a `LayeredFlow`, and it never says which feasible
set the result lands in.  That is the missing half of the reduction: without it, "the flow
problem is the same problem" is a statement about two collections nobody has connected.

`rankingFlow` assembles them, with the same self-loop continuation past the horizon that
`CountFeasibleH` uses, and `rankingFlow_feasible` proves the assembled object is feasible.
Both of the non-trivial conditions are proved rather than assumed:

* legality, from `rankLayer_step` -- moving from budget `k` to `k+1` serves the single item
  `ω k`, so exactly one coordinate rises;
* the LP capacity, from `rankLayer_le_mult` -- the count of a type among the first `k` items
  cannot exceed that type's multiplicity, since a permutation visits each item once.

Together with `exists_rank_section_H` in the other direction, the two maps now run between
the same two sets.  `rankingFlow_budget_vector` carries the WHOLE budget vector across, not
one aggregate, which is what a maximum over budgets needs.
-/

namespace CIGAMF.P13.PaperCRankFlow

open Finset
open CIGAMF.P13.PaperCFlow
open CIGAMF.P13.PaperCBreakpoint
open CIGAMF.P13.CFinal
open CIGAMF.P13.PaperCNaming
open CIGAMF.P13.PaperCHorizon
open CIGAMF.P13.PaperCVacuity

variable {d m : ℕ}

/-! ## Counting facts about a ranking's layers -/

theorem layerCount_mono (s : Fin m → Fin d) (i j : ℕ) (hij : i ≤ j) (τ : Fin d) :
    layerCount m s i τ ≤ layerCount m s j τ := by
  unfold layerCount
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => Nat.zero_le _)
  intro x hx
  exact Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hx) hij)

theorem layerCount_full (s : Fin m → Fin d) (τ : Fin d) :
    layerCount m s m τ = (univ.filter (fun j : Fin m => s j = τ)).card := by
  classical
  unfold layerCount
  rw [Finset.card_filter, ← Fin.sum_univ_eq_sum_range
    (fun k => if h : k < m then (if s ⟨k, h⟩ = τ then 1 else 0) else 0) m]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [dif_pos i.isLt]

/-- **A permutation serves each item once**, so its full layer count is the multiplicity. -/
theorem layerCount_full_perm (ty : Fin m → Fin d) (ω : Equiv.Perm (Fin m)) (τ : Fin d) :
    layerCount m (fun k => ty (ω k)) m τ = mult ty τ := by
  classical
  rw [layerCount_full]
  unfold mult
  refine Finset.card_bij' (fun j _ => ω j) (fun j _ => ω.symm j) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj ⊢
    exact hj
  · intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj ⊢
    rwa [Equiv.apply_symm_apply]
  · intro j _; exact Equiv.symm_apply_apply _ _
  · intro j _; exact Equiv.apply_symm_apply _ _

/-- **The LP capacity constraint, for a ranking.** -/
theorem rankLayer_le_mult (ty : Fin m → Fin d) (i : Fin (m + 1)) (ω : Equiv.Perm (Fin m))
    (τ : Fin d) : ((rankLayer ty i ω τ : Fin (m + 1)) : ℕ) ≤ mult ty τ := by
  have h : ((rankLayer ty i ω τ : Fin (m + 1)) : ℕ)
      = layerCount m (fun k => ty (ω k)) (i : ℕ) τ := rfl
  rw [h, ← layerCount_full_perm ty ω τ]
  exact layerCount_mono _ (i : ℕ) m (Nat.lt_succ_iff.mp i.isLt) τ

/-- **Serving the next item raises exactly one count**, so a ranking's consecutive layers are
a legal step. -/
theorem rankLayer_step (ty : Fin m → Fin d) (i : Fin m) (ω : Equiv.Perm (Fin m)) :
    StepC (rankLayer ty i.castSucc ω) (rankLayer ty i.succ ω) := by
  classical
  set s : Fin m → Fin d := fun k => ty (ω k) with hs
  refine ⟨s i, ?_, ?_⟩
  · show layerCount m s ((i.succ : Fin (m + 1)) : ℕ) (s i)
      = layerCount m s ((i.castSucc : Fin (m + 1)) : ℕ) (s i) + 1
    have e1 : ((i.succ : Fin (m + 1)) : ℕ) = (i : ℕ) + 1 := by simp
    have e2 : ((i.castSucc : Fin (m + 1)) : ℕ) = (i : ℕ) := by simp
    have hii : (⟨(i : ℕ), i.isLt⟩ : Fin m) = i := rfl
    rw [e1, e2, layerCount_succ m s (i : ℕ) i.isLt (s i), hii, if_pos rfl]
  · intro τ' hτ'
    apply Fin.ext
    show layerCount m s ((i.succ : Fin (m + 1)) : ℕ) τ'
      = layerCount m s ((i.castSucc : Fin (m + 1)) : ℕ) τ'
    have e1 : ((i.succ : Fin (m + 1)) : ℕ) = (i : ℕ) + 1 := by simp
    have e2 : ((i.castSucc : Fin (m + 1)) : ℕ) = (i : ℕ) := by simp
    have hii : (⟨(i : ℕ), i.isLt⟩ : Fin m) = i := rfl
    rw [e1, e2, layerCount_succ m s (i : ℕ) i.isLt τ', hii, if_neg (fun h => hτ' h.symm),
      add_zero]

/-! ## The assembled flow -/

/-- The budget index, clamped at the horizon. -/
def clampIdx (m k : ℕ) : Fin (m + 1) := ⟨min k m, by omega⟩

theorem clampIdx_lt (m k : ℕ) (hk : k < m) : clampIdx m k = (⟨k, hk⟩ : Fin m).castSucc :=
  Fin.ext (by simp [clampIdx]; omega)

theorem clampIdx_succ_lt (m k : ℕ) (hk : k < m) :
    clampIdx m (k + 1) = (⟨k, hk⟩ : Fin m).succ :=
  Fin.ext (by simp [clampIdx]; omega)

theorem clampIdx_ge (m k : ℕ) (hk : m ≤ k) : clampIdx m (k + 1) = clampIdx m k :=
  Fin.ext (by simp [clampIdx]; omega)

/-- **The ranking law's flow**, as an object of the same type the feasible set is about. -/
noncomputable def rankingFlow (P : Equiv.Perm (Fin m) → ℝ) (hP : ∀ x, 0 ≤ P x)
    (ty : Fin m → Fin d) : LayeredFlow (CState d m) where
  x := fun k v => flowX P ty (clampIdx m k) v
  f := fun k v w =>
    if hk : k < m then flowF P ty ⟨k, hk⟩ v w
    else if v = w then flowX P ty (clampIdx m k) v else 0
  xnn := fun k v => flowX_nonneg P hP ty _ v
  fnn := by
    intro k v w
    by_cases hk : k < m
    · rw [dif_pos hk]; exact flowF_nonneg P hP ty ⟨k, hk⟩ v w
    · rw [dif_neg hk]
      split_ifs
      · exact flowX_nonneg P hP ty _ v
      · exact le_refl 0
  outflow := by
    intro k v
    by_cases hk : k < m
    · simp only [dif_pos hk]
      rw [flow_conservation_out P ty ⟨k, hk⟩ v, clampIdx_lt m k hk]
    · simp only [dif_neg hk]
      simp
  inflow := by
    intro k w
    by_cases hk : k < m
    · simp only [dif_pos hk]
      rw [flow_conservation_in P ty ⟨k, hk⟩ w, clampIdx_succ_lt m k hk]
    · simp only [dif_neg hk]
      have hge : m ≤ k := by omega
      rw [clampIdx_ge m k hge]
      simp

/-- **(#15, ranking → flow.)**  A ranking law's flow is feasible on the REPAIRED domain.
Neither legality nor the capacity is assumed; both are proved from the ranking. -/
theorem rankingFlow_feasible (P : Equiv.Perm (Fin m) → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hsum : ∑ x, P x = 1) (ty : Fin m → Fin d) :
    CountFeasibleH ty (rankingFlow P hP ty) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ∑ v, flowX P ty (clampIdx m 0) v = 1
    rw [flowX_total P ty (clampIdx m 0), hsum]
  · intro k hk v w hstep
    show (if h : k < m then flowF P ty ⟨k, h⟩ v w
      else if v = w then flowX P ty (clampIdx m k) v else 0) = 0
    rw [dif_pos hk]
    unfold flowF joint
    refine Finset.sum_eq_zero (fun ω hω => ?_)
    simp only [mem_filter, mem_univ, true_and] at hω
    exact absurd (hω.1 ▸ hω.2 ▸ rankLayer_step ty ⟨k, hk⟩ ω) hstep
  · intro k hk v w hne
    show (if h : k < m then flowF P ty ⟨k, h⟩ v w
      else if v = w then flowX P ty (clampIdx m k) v else 0) = 0
    rw [dif_neg (by omega), if_neg hne]
  · intro k v hx τ
    have hne : flowX P ty (clampIdx m k) v ≠ 0 := hx
    unfold flowX occ at hne
    have hex : ∃ ω ∈ Finset.univ.filter
        (fun ω => rankLayer ty (clampIdx m k) ω = v), P ω ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hne (Finset.sum_eq_zero (fun ω hω => hcon ω hω))
    obtain ⟨ω, hω, -⟩ := hex
    simp only [mem_filter, mem_univ, true_and] at hω
    rw [← hω]
    exact rankLayer_le_mult ty (clampIdx m k) ω τ

/-- **The whole budget vector crosses with the flow.**  Not one aggregate: budget by budget,
which is what a maximum over budgets requires. -/
theorem rankingFlow_budget_vector (P : Equiv.Perm (Fin m) → ℝ) (hP : ∀ x, 0 ≤ P x)
    (ty : Fin m → Fin d) (g : Fin (m + 1) → CState d m → ℝ) (k : Fin (m + 1)) :
    ∑ ω : Equiv.Perm (Fin m), P ω * g k (rankLayer ty k ω)
      = ∑ v : CState d m, (rankingFlow P hP ty).x (k : ℕ) v * g k v := by
  have hidx : clampIdx m (k : ℕ) = k :=
    Fin.ext (by simp [clampIdx]; omega)
  show ∑ ω : Equiv.Perm (Fin m), P ω * g k (rankLayer ty k ω)
    = ∑ v : CState d m, flowX P ty (clampIdx m (k : ℕ)) v * g k v
  rw [hidx]
  exact budget_vector_transports P ty g k

/-! ## Audit -/

#print axioms layerCount_mono
#print axioms layerCount_full
#print axioms layerCount_full_perm
#print axioms rankLayer_le_mult
#print axioms rankLayer_step
#print axioms rankingFlow_feasible
#print axioms rankingFlow_budget_vector

end CIGAMF.P13.PaperCRankFlow
