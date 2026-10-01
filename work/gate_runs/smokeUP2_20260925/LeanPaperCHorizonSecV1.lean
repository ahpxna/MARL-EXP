import «LeanPaperCHorizonV1»

/-!
# Paper C: the section, rebuilt on the repaired flow domain

`countFeasible_empty` showed the old domain `CountFeasible` has no unit flow, so
`exists_rank_section` and `pathDecomposition_count_states` -- which quantify over it -- say
nothing.  `CountFeasibleH` is the repair and `horizon_flow` shows it is inhabited.  What is
missing is the section on the NEW domain, and that is what this module supplies.

Three things have to be redone, and none of them may quietly reuse the old hypothesis
`∀ k v w, ¬ StepC v w → F.f k v w = 0`, which is exactly the assumption that emptied the
domain:

* `kernel_stepSupported_at` and `trajLaw_stepC_lt` -- the legality transfer, at one layer and
  then along a trajectory, with legality assumed only BELOW the horizon.  The induction never
  looks above layer `n - 1`, so the bounded hypothesis is enough; that is the whole point.
* `occupied_of_trajLaw` -- positive trajectory mass implies positive occupancy at every
  layer, read off `trajLaw_marginal_all`.  This is what lets `start_empty` and `end_full`
  apply to a trajectory rather than to a state named in advance.
* `hsec_count_states_H` and `exists_rank_section_H` -- the section itself.  Its two endpoint
  hypotheses are no longer assumed: they are DERIVED from `CountFeasibleH` through the
  previous item, so `exists_rank_section_H` takes the flow's feasibility and nothing else.
-/

namespace CIGAMF.P13.PaperCHorizonSec

open Finset
open CIGAMF.P13.PaperCBreakpoint
open CIGAMF.P13.CFinal
open CIGAMF.P13.PaperCVacuity
open CIGAMF.P13.PaperCHorizon

variable {d m : ℕ}

/-! ## Legality transfer, below the horizon only -/

/-- The kernel is step-supported at one layer, from legality at that layer alone. -/
theorem kernel_stepSupported_at (F : LayeredFlow (CState d m)) (k : ℕ)
    (hF : ∀ v w, ¬ StepC v w → F.f k v w = 0) :
    ∀ v w, ¬ StepC v w → F.kernel k v w = 0 := by
  intro v w h
  unfold LayeredFlow.kernel
  by_cases hx : F.x k v = 0
  · rw [if_pos hx]
  · rw [if_neg hx, hF v w h, zero_div]

/-- **Positive trajectory mass forces every step to be legal**, needing legality only at the
layers the trajectory actually crosses. -/
theorem trajLaw_stepC_lt (F : LayeredFlow (CState d m)) (N : ℕ)
    (hF : ∀ k, k < N → ∀ v w, ¬ StepC v w → F.f k v w = 0) :
    ∀ (n : ℕ), n ≤ N → ∀ t : Fin (n + 1) → CState d m, F.trajLaw n t ≠ 0 →
      ∀ i : Fin n, StepC (t i.castSucc) (t i.succ) := by
  intro n
  induction n with
  | zero => intro _ t _ i; exact absurd i.isLt (by omega)
  | succ n ih =>
      intro hn t ht i
      rw [LayeredFlow.trajLaw_succ] at ht
      have h1 : F.trajLaw n (Fin.init t) ≠ 0 := fun h => ht (by rw [h, zero_mul])
      have h2 : F.kernel n (Fin.init t (Fin.last n)) (t (Fin.last (n + 1))) ≠ 0 :=
        fun h => ht (by rw [h, mul_zero])
      by_cases hlast : (i : ℕ) = n
      · have e1 : (Fin.init t) (Fin.last n) = t i.castSucc := by
          simp only [Fin.init]
          congr 1
          exact Fin.ext (by simp [hlast])
        have e2 : t (Fin.last (n + 1)) = t i.succ := by
          congr 1
          exact Fin.ext (by simp [hlast])
        rw [e1, e2] at h2
        by_contra hc
        exact h2 (kernel_stepSupported_at F n (hF n (by omega)) _ _ hc)
      · have hi : (i : ℕ) < n := by omega
        have hstep := ih (by omega) (Fin.init t) h1 ⟨(i : ℕ), hi⟩
        have e1 : (Fin.init t) (⟨(i : ℕ), hi⟩ : Fin n).castSucc = t i.castSucc := by
          simp only [Fin.init]
          congr 1
        have e2 : (Fin.init t) (⟨(i : ℕ), hi⟩ : Fin n).succ = t i.succ := by
          simp only [Fin.init]
          congr 1
        rwa [e1, e2] at hstep

/-! ## A trajectory of positive mass occupies every layer it passes through -/

/-- **Positive trajectory mass gives positive occupancy**, layer by layer.  Without this the
endpoint facts would have to be assumed about the trajectory instead of derived. -/
theorem occupied_of_trajLaw (F : LayeredFlow (CState d m)) (n : ℕ)
    (t : Fin (n + 1) → CState d m) (ht : F.trajLaw n t ≠ 0) (i : Fin (n + 1)) :
    F.x (i : ℕ) (t i) ≠ 0 := by
  classical
  have hmarg := F.trajLaw_marginal_all n i (t i)
  have hpos : 0 < F.trajLaw n t :=
    lt_of_le_of_ne (F.trajLaw_nonneg n t) (Ne.symm ht)
  have hterms : ∀ s : Fin (n + 1) → CState d m,
      0 ≤ F.trajLaw n s * (if s i = t i then (1 : ℝ) else 0) := by
    intro s
    refine mul_nonneg (F.trajLaw_nonneg n s) ?_
    split_ifs <;> norm_num
  have hle : F.trajLaw n t * (if t i = t i then (1 : ℝ) else 0)
      ≤ ∑ s : Fin (n + 1) → CState d m,
          F.trajLaw n s * (if s i = t i then (1 : ℝ) else 0) :=
    Finset.single_le_sum (fun s _ => hterms s) (Finset.mem_univ t)
  rw [if_pos rfl, mul_one, hmarg] at hle
  exact fun h => absurd (h ▸ hle) (by simpa using hpos.not_ge)

/-! ## The section on the repaired domain -/

/-- **The type sequence behind a positive-mass trajectory**, on `CountFeasibleH`.  The start
condition is derived from the flow, not assumed. -/
theorem hsec_count_states_H (ty : Fin m → Fin d) (F : LayeredFlow (CState d m))
    (hFeas : CountFeasibleH ty F)
    (t : Fin (m + 1) → CState d m) (ht : F.trajLaw m t ≠ 0) :
    ∃ s : Fin m → Fin d, ∀ (i : ℕ) (hi : i ≤ m), layerState s i hi = t ⟨i, by omega⟩ := by
  classical
  have hlegal := hFeas.2.1
  have hsteps := trajLaw_stepC_lt F m hlegal m le_rfl t ht
  have h0 : ∀ τ, ((t 0) τ : ℕ) = 0 := by
    intro τ
    have hocc := occupied_of_trajLaw F m t ht 0
    exact start_empty ty F hFeas (t 0) (by simpa using hocc) τ
  choose sτ hup hrest using fun i : Fin m => hsteps i
  refine ⟨sτ, ?_⟩
  set T : ℕ → Fin d → ℕ := fun i τ => if h : i ≤ m then ((t ⟨i, by omega⟩) τ : ℕ) else 0
    with hT
  have hT0 : ∀ τ, T 0 τ = 0 := by
    intro τ; rw [hT]; simp only [dif_pos (Nat.zero_le m)]; exact h0 τ
  have hTup : ∀ (i : ℕ) (hi : i < m), T (i + 1) (sτ ⟨i, hi⟩) = T i (sτ ⟨i, hi⟩) + 1 := by
    intro i hi
    have hA : i ≤ m := by omega
    have hB : i + 1 ≤ m := by omega
    rw [hT]
    simp only [dif_pos hA, dif_pos hB]
    have h := hup ⟨i, hi⟩
    have e1 : (⟨i, hi⟩ : Fin m).castSucc = (⟨i, by omega⟩ : Fin (m + 1)) := Fin.ext (by simp)
    have e2 : (⟨i, hi⟩ : Fin m).succ = (⟨i + 1, by omega⟩ : Fin (m + 1)) := Fin.ext (by simp)
    rwa [e1, e2] at h
  have hTrest : ∀ (i : ℕ) (hi : i < m) (τ : Fin d), τ ≠ sτ ⟨i, hi⟩ →
      T (i + 1) τ = T i τ := by
    intro i hi τ hne
    have hA : i ≤ m := by omega
    have hB : i + 1 ≤ m := by omega
    rw [hT]
    simp only [dif_pos hA, dif_pos hB]
    have h := hrest ⟨i, hi⟩ τ hne
    have e1 : (⟨i, hi⟩ : Fin m).castSucc = (⟨i, by omega⟩ : Fin (m + 1)) := Fin.ext (by simp)
    have e2 : (⟨i, hi⟩ : Fin m).succ = (⟨i + 1, by omega⟩ : Fin (m + 1)) := Fin.ext (by simp)
    rw [e1, e2] at h
    exact congrArg Fin.val h
  have hreal := legal_path_realised m T sτ hT0 hTup hTrest
  intro i hi
  funext τ
  have h := hreal i hi τ
  rw [hT] at h
  simp only [dif_pos hi] at h
  exact Fin.ext h

/-- **(#15, the section with no endpoint hypotheses.)**  Every positive-mass trajectory of a
feasible flow is realised by a genuine permutation of the items.  Both endpoint conditions
that `exists_rank_section` took as hypotheses are discharged here from `CountFeasibleH`. -/
theorem exists_rank_section_H (ty : Fin m → Fin d) (F : LayeredFlow (CState d m))
    (hFeas : CountFeasibleH ty F)
    (t : Fin (m + 1) → CState d m) (ht : F.trajLaw m t ≠ 0) :
    ∃ ω : Equiv.Perm (Fin m), ∀ i : Fin (m + 1), rankLayer ty i ω = t i := by
  classical
  obtain ⟨s, hs⟩ := hsec_count_states_H ty F hFeas t ht
  have hend : ∀ τ, ((t (Fin.last m)) τ : ℕ) = mult ty τ := by
    intro τ
    have hocc := occupied_of_trajLaw F m t ht (Fin.last m)
    have hlast : ((Fin.last m : Fin (m + 1)) : ℕ) = m := rfl
    rw [hlast] at hocc
    exact end_full ty F hFeas (t (Fin.last m)) hocc τ
  have hsm : ∀ τ, layerCount m s m τ = mult ty τ := by
    intro τ
    have h := congrFun (hs m le_rfl) τ
    have h2 : (layerState s m le_rfl τ : ℕ) = ((t ⟨m, by omega⟩) τ : ℕ) := by rw [h]
    have h3 : (⟨m, by omega⟩ : Fin (m + 1)) = Fin.last m := rfl
    rw [h3] at h2
    rw [← hend τ, ← h2]
    rfl
  have hcard : ∀ τ, Fintype.card {k : Fin m // s k = τ}
      = Fintype.card {j : Fin m // ty j = τ} := by
    intro τ
    rw [Fintype.card_subtype, Fintype.card_subtype]
    rw [card_filter_eq_layerCount m s τ, hsm τ]
    rfl
  refine ⟨matchPerm m s ty hcard, ?_⟩
  intro i
  have hcomp : (fun k => ty (matchPerm m s ty hcard k)) = s := by
    funext k; exact matchPerm_type m s ty hcard k
  unfold rankLayer
  rw [hcomp]
  have h := hs (i : ℕ) (Nat.lt_succ_iff.mp i.isLt)
  rw [h]

/-! ## Audit -/

#print axioms kernel_stepSupported_at
#print axioms trajLaw_stepC_lt
#print axioms occupied_of_trajLaw
#print axioms hsec_count_states_H
#print axioms exists_rank_section_H

end CIGAMF.P13.PaperCHorizonSec
