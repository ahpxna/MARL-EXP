import «LeanPaperCRankFlowV1»

/-!
# Paper C: flow → ranking, and the two optimisation problems are one

`rankingFlow_feasible` sends a ranking law into the repaired feasible set; `exists_rank_section_H`
sends each positive-mass trajectory back to a permutation.  Neither yet says the two problems
have the same answer, and "the flow formulation is the same optimisation" is empty until they
do.  This module closes it.

`flowLaw` is the missing map: push the flow's own trajectory law forward along the section.
`flowLaw_occ` is the one computation that matters --

    occ (flowLaw ty F) (rankLayer ty k) v = F.x k v,

the pushed-forward ranking law reproduces the flow's occupancy at EVERY layer, not only at
the endpoints.  Its proof is the fibre regrouping plus the section identity, and the section
identity is available exactly where the trajectory carries mass, which is exactly where the
indicator is not already zero.

`objective_vectors_agree` then states the reduction as an equality of the two sets of
achievable objective VECTORS.  That is deliberately stronger than equating one scalar: the
objective here is a maximum over budgets, so two problems agreeing on some aggregate would
not make them the same problem.  Agreeing on the whole vector does, and
`values_agree` reads off that every functional of the vector -- the max over budgets among
them -- has the same infimum on both sides.
-/

namespace CIGAMF.P13.PaperCFlowLaw

open Finset
open CIGAMF.P13.PaperCFlow
open CIGAMF.P13.PaperCBreakpoint
open CIGAMF.P13.CFinal
open CIGAMF.P13.PaperCNaming
open CIGAMF.P13.PaperCHorizon
open CIGAMF.P13.PaperCVacuity
open CIGAMF.P13.PaperCHorizonSec
open CIGAMF.P13.PaperCRankFlow

variable {d m : ℕ}

/-! ## The section as a total function, and the pushed-forward law -/

open scoped Classical in
/-- The section: a permutation realising the trajectory where one exists, and the identity
elsewhere, where its value is never read. -/
noncomputable def secH (ty : Fin m → Fin d) (t : Fin (m + 1) → CState d m) :
    Equiv.Perm (Fin m) :=
  if h : ∃ ω : Equiv.Perm (Fin m), ∀ i : Fin (m + 1), rankLayer ty i ω = t i
  then h.choose else 1

theorem secH_spec (ty : Fin m → Fin d) (F : LayeredFlow (CState d m))
    (hFeas : CountFeasibleH ty F) (t : Fin (m + 1) → CState d m) (ht : F.trajLaw m t ≠ 0)
    (i : Fin (m + 1)) : rankLayer ty i (secH ty t) = t i := by
  classical
  have hex := exists_rank_section_H ty F hFeas t ht
  unfold secH
  rw [dif_pos hex]
  exact hex.choose_spec i

open scoped Classical in
/-- **The flow's own ranking law**: the trajectory law, pushed forward along the section. -/
noncomputable def flowLaw (ty : Fin m → Fin d) (F : LayeredFlow (CState d m)) :
    Equiv.Perm (Fin m) → ℝ :=
  fun ω => ∑ t ∈ univ.filter (fun t : Fin (m + 1) → CState d m => secH ty t = ω),
    F.trajLaw m t

theorem flowLaw_nonneg (ty : Fin m → Fin d) (F : LayeredFlow (CState d m)) (ω) :
    0 ≤ flowLaw ty F ω :=
  Finset.sum_nonneg (fun t _ => F.trajLaw_nonneg m t)

theorem flowLaw_sum (ty : Fin m → Fin d) (F : LayeredFlow (CState d m))
    (h0 : ∑ v, F.x 0 v = 1) : ∑ ω, flowLaw ty F ω = 1 := by
  classical
  unfold flowLaw
  rw [Finset.sum_fiberwise_of_maps_to (fun t _ => Finset.mem_univ (secH ty t))
    (fun t => F.trajLaw m t)]
  exact F.trajLaw_sum m h0 (fun j => by rw [mass_one F h0 (j + 1), mass_one F h0 j])

/-- **The pushed-forward law reproduces the flow's occupancy at every layer.**  This is the
identity the reduction rests on. -/
theorem flowLaw_occ (ty : Fin m → Fin d) (F : LayeredFlow (CState d m))
    (hFeas : CountFeasibleH ty F) (k : Fin (m + 1)) (v : CState d m) :
    occ (flowLaw ty F) (rankLayer ty k) v = F.x (k : ℕ) v := by
  classical
  have hind : ∀ ω : Equiv.Perm (Fin m),
      (if rankLayer ty k ω = v then flowLaw ty F ω else 0)
        = ∑ t ∈ univ.filter (fun t : Fin (m + 1) → CState d m => secH ty t = ω),
            (if rankLayer ty k (secH ty t) = v then F.trajLaw m t else 0) := by
    intro ω
    unfold flowLaw
    by_cases hc : rankLayer ty k ω = v
    · rw [if_pos hc]
      refine Finset.sum_congr rfl (fun t ht => ?_)
      simp only [mem_filter, mem_univ, true_and] at ht
      rw [ht, if_pos hc]
    · rw [if_neg hc]
      refine (Finset.sum_eq_zero (fun t ht => ?_)).symm
      simp only [mem_filter, mem_univ, true_and] at ht
      rw [ht, if_neg hc]
  have hstep : ∀ t : Fin (m + 1) → CState d m,
      (if rankLayer ty k (secH ty t) = v then F.trajLaw m t else 0)
        = F.trajLaw m t * (if t k = v then (1 : ℝ) else 0) := by
    intro t
    by_cases ht : F.trajLaw m t = 0
    · rw [ht, zero_mul]
      split_ifs <;> rfl
    · rw [secH_spec ty F hFeas t ht k]
      split_ifs <;> simp
  calc occ (flowLaw ty F) (rankLayer ty k) v
      = ∑ ω, (if rankLayer ty k ω = v then flowLaw ty F ω else 0) := by
        unfold occ
        rw [Finset.sum_filter]
    _ = ∑ ω, ∑ t ∈ univ.filter (fun t : Fin (m + 1) → CState d m => secH ty t = ω),
          (if rankLayer ty k (secH ty t) = v then F.trajLaw m t else 0) :=
        Finset.sum_congr rfl (fun ω _ => hind ω)
    _ = ∑ t : Fin (m + 1) → CState d m,
          (if rankLayer ty k (secH ty t) = v then F.trajLaw m t else 0) :=
        Finset.sum_fiberwise_of_maps_to (fun t _ => Finset.mem_univ (secH ty t)) _
    _ = ∑ t : Fin (m + 1) → CState d m,
          F.trajLaw m t * (if t k = v then (1 : ℝ) else 0) :=
        Finset.sum_congr rfl (fun t _ => hstep t)
    _ = F.x (k : ℕ) v := F.trajLaw_marginal_all m k v

/-! ## The two problems -/

/-- A ranking law is feasible when it is a probability law over the permutations. -/
def RankingLaw (P : Equiv.Perm (Fin m) → ℝ) : Prop :=
  (∀ ω, 0 ≤ P ω) ∧ (∑ ω, P ω = 1)

/-- The objective VECTOR of a ranking law: one entry per budget. -/
noncomputable def rankObj (ty : Fin m → Fin d) (c : Fin (m + 1) → CState d m → ℝ)
    (P : Equiv.Perm (Fin m) → ℝ) : Fin (m + 1) → ℝ :=
  fun k => ∑ ω, P ω * c k (rankLayer ty k ω)

/-- The objective vector of a flow. -/
noncomputable def flowObj (c : Fin (m + 1) → CState d m → ℝ)
    (F : LayeredFlow (CState d m)) : Fin (m + 1) → ℝ :=
  fun k => ∑ v, F.x (k : ℕ) v * c k v

/-- **(#15) The two problems have the same achievable objective vectors.**  Not the same
optimum of one aggregate -- the same vector, budget by budget, which is what an objective
that maximises over budgets requires. -/
theorem objective_vectors_agree (ty : Fin m → Fin d) (c : Fin (m + 1) → CState d m → ℝ) :
    {y : Fin (m + 1) → ℝ | ∃ P, RankingLaw P ∧ rankObj ty c P = y}
      = {y : Fin (m + 1) → ℝ | ∃ F, CountFeasibleH ty F ∧ flowObj c F = y} := by
  classical
  ext y
  constructor
  · rintro ⟨P, ⟨hP, hsum⟩, rfl⟩
    refine ⟨rankingFlow P hP ty, rankingFlow_feasible P hP hsum ty, ?_⟩
    funext k
    exact (rankingFlow_budget_vector P hP ty c k).symm
  · rintro ⟨F, hFeas, rfl⟩
    refine ⟨flowLaw ty F, ⟨flowLaw_nonneg ty F, flowLaw_sum ty F hFeas.1⟩, ?_⟩
    funext k
    show ∑ ω, flowLaw ty F ω * c k (rankLayer ty k ω) = ∑ v, F.x (k : ℕ) v * c k v
    rw [objective_transports (flowLaw ty F) ty k (c k)]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [show flowX (flowLaw ty F) ty k v = occ (flowLaw ty F) (rankLayer ty k) v from rfl,
      flowLaw_occ ty F hFeas k v]

/-- **Every functional of the objective vector has the same range, hence the same infimum,
on both sides.**  Taking `Φ` to be the maximum over a set of budgets is the case Paper C
uses, so the reduction is value-preserving for the actual objective. -/
theorem values_agree (ty : Fin m → Fin d) (c : Fin (m + 1) → CState d m → ℝ)
    (Φ : (Fin (m + 1) → ℝ) → ℝ) :
    Φ '' {y : Fin (m + 1) → ℝ | ∃ P, RankingLaw P ∧ rankObj ty c P = y}
      = Φ '' {y : Fin (m + 1) → ℝ | ∃ F, CountFeasibleH ty F ∧ flowObj c F = y} := by
  rw [objective_vectors_agree ty c]

/-- The infima agree, which is the statement the manuscript makes. -/
theorem infima_agree (ty : Fin m → Fin d) (c : Fin (m + 1) → CState d m → ℝ)
    (Φ : (Fin (m + 1) → ℝ) → ℝ) :
    sInf (Φ '' {y : Fin (m + 1) → ℝ | ∃ P, RankingLaw P ∧ rankObj ty c P = y})
      = sInf (Φ '' {y : Fin (m + 1) → ℝ | ∃ F, CountFeasibleH ty F ∧ flowObj c F = y}) :=
  congrArg sInf (values_agree ty c Φ)

/-- **Neither side is empty.**  `countFeasible_empty` is the reason this has to be said: an
equality between two empty problems is not a reduction. -/
theorem both_sides_nonempty (ty : Fin m → Fin d) (c : Fin (m + 1) → CState d m → ℝ) :
    {y : Fin (m + 1) → ℝ | ∃ F, CountFeasibleH ty F ∧ flowObj c F = y}.Nonempty :=
  ⟨flowObj c (horizonFlow ty), ⟨horizonFlow ty, horizon_flow ty, rfl⟩⟩

/-! ## Audit -/

#print axioms secH_spec
#print axioms flowLaw_sum
#print axioms flowLaw_occ
#print axioms objective_vectors_agree
#print axioms values_agree
#print axioms infima_agree
#print axioms both_sides_nonempty

end CIGAMF.P13.PaperCFlowLaw
