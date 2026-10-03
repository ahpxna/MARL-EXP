import «LeanPaperCBudgetAwareV1»

/-!
# MARL P2 / M4: commitment, budget-aware and recourse values for an ARBITRARY set cost

Paper C (`LeanPaperCBudgetAwareV1`) defines three values for its signed objective `subCost g`:
`trueValue` (U: one ranking law serves every budget), `awareValue` (B: a subset law per budget)
and `recourseValue` (V^(R): commit a ranking law, then edit the budget-`k` prefix by at most `R`
exchanges once `k` is revealed). The order relations there use only that the cost is a function
of the budget and the final set. This module re-defines the three values for an arbitrary set
cost and re-proves them.

**The cost.** A set cost is any `c : Fin (m+1) → Finset (Fin m) → ℝ` (`SetCost m`): ending
budget `k` with the set `S` costs `c k S`. No sign, monotonicity, submodularity or symmetry is
assumed. Every theorem below holds for every such `c`. The intended use is the REGRET form
`regretOf ℓ k S = ℓ k S - optLoss ℓ k`, where `optLoss ℓ k` is the minimum of the team loss `ℓ k`
over `k`-sets; then B, U and V^(R) are prices measured from the per-budget optimum
(`regretOf_nonneg`, `optLoss_regretOf`).

**The band.** The exposure band `η` is kept as a parameter: C's `FeasibleAt id η` for the committed
ranking law and C's `SubFeasible k η` / `PlanFeasible P k R η` for the final laws, unchanged.
It is vacuous once `η ≥ m` (`feasibleAt_vacuous_iff`, `subFeasible_vacuous_iff`,
`planFeasible_vacuous_iff`): every probability law is admitted. At a vacuous band the budget-aware
layer is the plain per-budget optimum (`genLayer_vacuous`), and B of a regret cost is `0`
(`genAware_vacuous_regret`).

**Order relations (every cost, every band `η ≥ 0`, `m ≠ 0`):**
* `aware_le_true`: `B ≤ U`;
* `aware_le_recourse`: `B ≤ V^(R)`;
* `recourse_le_true`: `V^(R) ≤ U`;
* `recourse_zero`: `V^(0) = U`;
* `recourse_mono`: `V^(R') ≤ V^(R)` for `R ≤ R'`;
* `recourse_full`: if `min(k, m-k) ≤ R` at every budget of `K`, then `V^(R) = B`.

**C is an instance.** `subCost_eq_regretOf`: C's objective is the regret form of
`ℓ k S = |Σ_{i∈S} g_i| / ‖g‖₁`. `trueValue_eq_gen`, `layerValue_eq_gen`, `awareValue_eq_gen`,
`planCost_eq_gen`, `recourseValue_eq_gen`: C's U, B and V^(R) are the generic values at
`c = subCost g`, by definition (`rfl`). `c_recourse_full_via_gen` re-derives C's `recourse_full`
from the generic one as a check of the instance.

**Satisfiability.** `genRecourseSet_nonempty`, `genTrue_image_nonempty` (the infima are over
inhabited sets at every `η ≥ 0`); `recourse_full_hyp_witness` (the hypothesis of `recourse_full`
holds for `m = 3`, `K = {1,2}`, `R = 1`); `vacuous_band_witness` (`η = m` is admissible and
`η ≥ 0`). A strict instance `B < U` is the XOR game (`LeanMarlXorGameV1`).
-/

namespace CIGAMF.P13.MarlGenericRecourse

open Finset
open CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCEndpoint
open CIGAMF.P13.PaperCStabilityEndgame CIGAMF.P13.PaperCLawPush CIGAMF.P13.PaperCBudgetAware

variable {m : ℕ}

/-! ## 0. Costs, per-budget optima, regret form -/

/-- **A set cost**: ending budget `k` with the final set `S` costs `c k S`. Arbitrary. -/
abbrev SetCost (m : ℕ) := Fin (m + 1) → Finset (Fin m) → ℝ

/-- The per-budget optimum of a loss over `k`-sets. -/
noncomputable def optLoss (ℓ : SetCost m) (k : Fin (m + 1)) : ℝ :=
  (univ.filter (fun S : Finset (Fin m) => S.card = k.val)).inf' (subsets_nonempty k) (ℓ k)

/-- **The regret form**: the loss minus its per-budget optimum. -/
noncomputable def regretOf (ℓ : SetCost m) : SetCost m := fun k S => ℓ k S - optLoss ℓ k

theorem optLoss_le (ℓ : SetCost m) (k : Fin (m + 1)) (S : Finset (Fin m))
    (hS : S.card = k.val) : optLoss ℓ k ≤ ℓ k S :=
  Finset.inf'_le _ (by simp [hS])

theorem exists_opt (ℓ : SetCost m) (k : Fin (m + 1)) :
    ∃ S : Finset (Fin m), S.card = k.val ∧ ℓ k S = optLoss ℓ k := by
  obtain ⟨S, hS, h⟩ := Finset.exists_mem_eq_inf' (subsets_nonempty k) (ℓ k)
  exact ⟨S, (Finset.mem_filter.mp hS).2, h.symm⟩

theorem regretOf_nonneg (ℓ : SetCost m) (k : Fin (m + 1)) (S : Finset (Fin m))
    (hS : S.card = k.val) : 0 ≤ regretOf ℓ k S :=
  sub_nonneg.mpr (optLoss_le ℓ k S hS)

/-- The regret form has per-budget optimum `0`. -/
theorem optLoss_regretOf (ℓ : SetCost m) (k : Fin (m + 1)) : optLoss (regretOf ℓ) k = 0 := by
  obtain ⟨S0, hS0, hopt⟩ := exists_opt ℓ k
  apply le_antisymm
  · calc optLoss (regretOf ℓ) k ≤ regretOf ℓ k S0 := optLoss_le _ k S0 hS0
      _ = 0 := by unfold regretOf; rw [hopt, sub_self]
  · exact Finset.le_inf' _ _ fun S hS => regretOf_nonneg ℓ k S (Finset.mem_filter.mp hS).2

/-- The least value of a cost at a budget over ALL sets (a crude floor, for boundedness). -/
noncomputable def costFloor (c : SetCost m) (k : Fin (m + 1)) : ℝ :=
  (univ : Finset (Finset (Fin m))).inf' univ_nonempty (c k)

theorem costFloor_le (c : SetCost m) (k : Fin (m + 1)) (S : Finset (Fin m)) :
    costFloor c k ≤ c k S :=
  Finset.inf'_le _ (mem_univ S)

/-- A probability average is at least any pointwise lower bound. -/
theorem le_expect {α : Type*} [Fintype α] (Q : α → ℝ) (hQ0 : ∀ x, 0 ≤ Q x)
    (hQ1 : ∑ x, Q x = 1) (f : α → ℝ) (a : ℝ) (ha : ∀ x, a ≤ f x) :
    a ≤ ∑ x, Q x * f x := by
  calc a = ∑ x, Q x * a := by rw [← Finset.sum_mul, hQ1, one_mul]
    _ ≤ ∑ x, Q x * f x :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (ha x) (hQ0 x)

/-- A probability average of `[0,1]`-valued terms lies in `[0,1]`. -/
theorem expect_mem_unit {α : Type*} [Fintype α] (Q : α → ℝ) (hQ0 : ∀ x, 0 ≤ Q x)
    (hQ1 : ∑ x, Q x = 1) (f : α → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    0 ≤ ∑ x, Q x * f x ∧ ∑ x, Q x * f x ≤ 1 := by
  refine ⟨Finset.sum_nonneg fun x _ => mul_nonneg (hQ0 x) (hf0 x), ?_⟩
  calc ∑ x, Q x * f x ≤ ∑ x, Q x * 1 :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hf1 x) (hQ0 x)
    _ = 1 := by rw [← Finset.sum_mul, hQ1, one_mul]

/-! ## 1. The three values for an arbitrary cost -/

/-- The worst-budget expected cost of a committed ranking law. -/
noncomputable def genObjective (c : SetCost m) (P : Equiv.Perm (Fin m) → ℝ)
    (K : Finset (Fin (m + 1))) (hK : K.Nonempty) : ℝ :=
  K.sup' hK (fun k => ∑ σ, P σ * c k (prefixSet σ k))

/-- **U**: one band-feasible ranking law for every budget. -/
noncomputable def genTrue (c : SetCost m) (η : ℝ) (K : Finset (Fin (m + 1)))
    (hK : K.Nonempty) : ℝ :=
  sInf ((fun P => genObjective c P K hK) '' FeasibleAt (id : Equiv.Perm (Fin m) → _) η)

/-- The layer value: the best band-feasible subset law at budget `k`. -/
noncomputable def genLayer (c : SetCost m) (η : ℝ) (k : Fin (m + 1)) : ℝ :=
  sInf ((fun Q => ∑ S, Q S * c k S) '' SubFeasible k.val η)

/-- **B**: the budget-aware value. -/
noncomputable def genAware (c : SetCost m) (η : ℝ) (K : Finset (Fin (m + 1)))
    (hK : K.Nonempty) : ℝ :=
  K.sup' hK (fun k => genLayer c η k)

/-- The expected cost of a recourse plan at budget `k`. -/
noncomputable def genPlanCost (c : SetCost m) (k : Fin (m + 1))
    (J : Equiv.Perm (Fin m) → Finset (Fin m) → ℝ) : ℝ :=
  ∑ σ, ∑ T, J σ T * c k T

/-- The achievable worst-budget costs with at most `R` exchanges after the reveal. -/
def genRecourseSet (c : SetCost m) (η : ℝ) (R : ℕ) (K : Finset (Fin (m + 1)))
    (hK : K.Nonempty) : Set ℝ :=
  {x | ∃ P ∈ FeasibleAt (id : Equiv.Perm (Fin m) → _) η,
    ∃ J : Fin (m + 1) → Equiv.Perm (Fin m) → Finset (Fin m) → ℝ,
      (∀ k ∈ K, J k ∈ PlanFeasible P k R η) ∧ x = K.sup' hK (fun k => genPlanCost c k (J k))}

/-- **V^(R)**: the recourse value. -/
noncomputable def genRecourse (c : SetCost m) (η : ℝ) (R : ℕ) (K : Finset (Fin (m + 1)))
    (hK : K.Nonempty) : ℝ :=
  sInf (genRecourseSet c η R K hK)

/-! ## 2. Boundedness and non-emptiness -/

theorem genLayer_bdd (c : SetCost m) (η : ℝ) (k : Fin (m + 1)) :
    BddBelow ((fun Q => ∑ S, Q S * c k S) '' SubFeasible k.val η) :=
  ⟨costFloor c k, by
    rintro _ ⟨Q, hQ, rfl⟩
    exact le_expect Q hQ.1 hQ.2.1 (c k) _ (costFloor_le c k)⟩

theorem genLayer_le (c : SetCost m) (η : ℝ) (k : Fin (m + 1)) (Q : Finset (Fin m) → ℝ)
    (hQ : Q ∈ SubFeasible k.val η) : genLayer c η k ≤ ∑ S, Q S * c k S :=
  csInf_le (genLayer_bdd c η k) ⟨Q, hQ, rfl⟩

theorem genTrue_image_nonempty [NeZero m] (c : SetCost m) (η : ℝ) (hη : 0 ≤ η)
    (K : Finset (Fin (m + 1))) (hK : K.Nonempty) :
    ((fun P => genObjective c P K hK) '' FeasibleAt (id : Equiv.Perm (Fin m) → _) η).Nonempty :=
  (allPerm_feasible_nonempty m η hη).image _

theorem genTrue_bdd (c : SetCost m) (η : ℝ) (K : Finset (Fin (m + 1))) (hK : K.Nonempty) :
    BddBelow ((fun P => genObjective c P K hK) ''
      FeasibleAt (id : Equiv.Perm (Fin m) → _) η) := by
  obtain ⟨k0, hk0⟩ := id hK
  refine ⟨costFloor c k0, ?_⟩
  rintro _ ⟨P, hP, rfl⟩
  refine le_trans ?_ (Finset.le_sup' (fun k => ∑ σ, P σ * c k (prefixSet σ k)) hk0)
  exact le_expect P hP.1 hP.2.1 _ _ fun σ => costFloor_le c k0 _

theorem genPlanCost_final (c : SetCost m) (k : Fin (m + 1))
    (J : Equiv.Perm (Fin m) → Finset (Fin m) → ℝ) :
    genPlanCost c k J = ∑ T, finalLaw J T * c k T := by
  unfold genPlanCost; rw [final_sum]

theorem genRecourse_bdd (c : SetCost m) (η : ℝ) (R : ℕ) (K : Finset (Fin (m + 1)))
    (hK : K.Nonempty) : BddBelow (genRecourseSet c η R K hK) := by
  obtain ⟨k0, hk0⟩ := id hK
  refine ⟨costFloor c k0, ?_⟩
  rintro _ ⟨P, hP, J, hJ, rfl⟩
  refine le_trans ?_ (Finset.le_sup' (fun k => genPlanCost c k (J k)) hk0)
  have hF := final_feasible P η hP k0 R (J k0) (hJ k0 hk0)
  rw [genPlanCost_final]
  exact le_expect _ hF.1 hF.2.1 _ _ (costFloor_le c k0)

theorem genIdPlan_cost (c : SetCost m) (P : Equiv.Perm (Fin m) → ℝ) (k : Fin (m + 1)) :
    genPlanCost c k (idPlan P k) = ∑ σ, P σ * c k (prefixSet σ k) := by
  unfold genPlanCost
  simp_rw [idPlan_sum]

/-- **The recourse value is an infimum over an inhabited set.** -/
theorem genRecourseSet_nonempty [NeZero m] (c : SetCost m) (η : ℝ) (hη : 0 ≤ η) (R : ℕ)
    (K : Finset (Fin (m + 1))) (hK : K.Nonempty) : (genRecourseSet c η R K hK).Nonempty := by
  obtain ⟨P, hP⟩ := allPerm_feasible_nonempty m η hη
  exact ⟨_, P, hP, fun k => idPlan P k, fun k _ => idPlan_feasible P η hP k R, rfl⟩

/-! ## 3. The order relations -/

theorem genLayer_le_obj (c : SetCost m) (η : ℝ) (P : Equiv.Perm (Fin m) → ℝ)
    (hP : P ∈ FeasibleAt (id : Equiv.Perm (Fin m) → _) η) (k : Fin (m + 1)) :
    genLayer c η k ≤ ∑ σ, P σ * c k (prefixSet σ k) := by
  rw [← push_sum]; exact genLayer_le c η k _ (push_feasible P η hP k)

/-- **Knowing the budget never hurts**: `B ≤ U`. -/
theorem aware_le_true [NeZero m] (c : SetCost m) (η : ℝ) (hη : 0 ≤ η)
    (K : Finset (Fin (m + 1))) (hK : K.Nonempty) :
    genAware c η K hK ≤ genTrue c η K hK := by
  refine le_csInf (genTrue_image_nonempty c η hη K hK) ?_
  rintro _ ⟨P, hP, rfl⟩
  refine Finset.sup'_le _ _ fun k hk => (genLayer_le_obj c η P hP k).trans ?_
  exact Finset.le_sup' (fun k => ∑ σ, P σ * c k (prefixSet σ k)) hk

theorem genLayer_le_plan (c : SetCost m) (η : ℝ) (P : Equiv.Perm (Fin m) → ℝ)
    (hP : P ∈ FeasibleAt (id : Equiv.Perm (Fin m) → _) η) (k : Fin (m + 1)) (R : ℕ)
    (J : Equiv.Perm (Fin m) → Finset (Fin m) → ℝ) (hJ : J ∈ PlanFeasible P k R η) :
    genLayer c η k ≤ genPlanCost c k J := by
  rw [genPlanCost_final]
  exact genLayer_le c η k _ (final_feasible P η hP k R J hJ)

/-- **Editing cannot beat knowing**: `B ≤ V^(R)`. -/
theorem aware_le_recourse [NeZero m] (c : SetCost m) (η : ℝ) (hη : 0 ≤ η) (R : ℕ)
    (K : Finset (Fin (m + 1))) (hK : K.Nonempty) :
    genAware c η K hK ≤ genRecourse c η R K hK := by
  refine le_csInf (genRecourseSet_nonempty c η hη R K hK) ?_
  rintro _ ⟨P, hP, J, hJ, rfl⟩
  refine Finset.sup'_le _ _ fun k hk => (genLayer_le_plan c η P hP k R (J k) (hJ k hk)).trans ?_
  exact Finset.le_sup' (fun k => genPlanCost c k (J k)) hk

/-- **Editing never hurts**: `V^(R) ≤ U`. -/
theorem recourse_le_true [NeZero m] (c : SetCost m) (η : ℝ) (hη : 0 ≤ η) (R : ℕ)
    (K : Finset (Fin (m + 1))) (hK : K.Nonempty) :
    genRecourse c η R K hK ≤ genTrue c η K hK := by
  refine le_csInf (genTrue_image_nonempty c η hη K hK) ?_
  rintro _ ⟨P, hP, rfl⟩
  refine csInf_le (genRecourse_bdd c η R K hK)
    ⟨P, hP, fun k => idPlan P k, fun k _ => idPlan_feasible P η hP k R, ?_⟩
  unfold genObjective
  simp_rw [genIdPlan_cost]

/-- **No exchange, no gain**: `V^(0) = U`. -/
theorem recourse_zero [NeZero m] (c : SetCost m) (η : ℝ) (hη : 0 ≤ η)
    (K : Finset (Fin (m + 1))) (hK : K.Nonempty) :
    genRecourse c η 0 K hK = genTrue c η K hK := by
  refine le_antisymm (recourse_le_true c η hη 0 K hK) ?_
  refine le_csInf (genRecourseSet_nonempty c η hη 0 K hK) ?_
  rintro _ ⟨P, hP, J, hJ, rfl⟩
  refine csInf_le (genTrue_bdd c η K hK) ⟨P, hP, ?_⟩
  unfold genObjective
  refine Finset.sup'_congr hK rfl fun k hk => ?_
  have hsupp : ∀ σ T, J k σ T ≠ 0 → T = prefixSet σ k := by
    intro σ T h
    obtain ⟨hc, hd⟩ := (hJ k hk).2.2.1 σ T h
    have hsub : prefixSet σ k ⊆ T := by
      rw [← Finset.sdiff_eq_empty_iff_subset]
      exact Finset.card_eq_zero.mp (Nat.le_zero.mp hd)
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [hc, prefixSet_card])).symm
  unfold genPlanCost
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h1 : ∀ T, J k σ T * c k T = J k σ T * c k (prefixSet σ k) := by
    intro T
    by_cases h : J k σ T = 0
    · rw [h, zero_mul, zero_mul]
    · rw [hsupp σ T h]
  simp_rw [h1]
  rw [← Finset.sum_mul, (hJ k hk).2.1 σ]

/-- **More exchanges never hurt**: `V^(R') ≤ V^(R)` for `R ≤ R'`. -/
theorem recourse_mono [NeZero m] (c : SetCost m) (η : ℝ) (hη : 0 ≤ η) (R R' : ℕ)
    (hRR : R ≤ R') (K : Finset (Fin (m + 1))) (hK : K.Nonempty) :
    genRecourse c η R' K hK ≤ genRecourse c η R K hK := by
  refine csInf_le_csInf (genRecourse_bdd c η R' K hK) (genRecourseSet_nonempty c η hη R K hK) ?_
  rintro _ ⟨P, hP, J, hJ, rfl⟩
  refine ⟨P, hP, J, fun k hk => ?_, rfl⟩
  obtain ⟨h1, h2, h3, h4⟩ := hJ k hk
  exact ⟨h1, h2, fun σ T h => ⟨(h3 σ T h).1, (h3 σ T h).2.trans hRR⟩, h4⟩

theorem genIndep_cost (c : SetCost m) (P : Equiv.Perm (Fin m) → ℝ) (hP1 : ∑ σ, P σ = 1)
    (k : Fin (m + 1)) (Q : Finset (Fin m) → ℝ) :
    genPlanCost c k (indepPlan P Q) = ∑ T, Q T * c k T := by
  unfold genPlanCost indepPlan
  simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, hP1, one_mul]

/-- **Enough exchanges reach the budget-aware value**: if `min(k, m-k) ≤ R` at every budget
of `K`, then `V^(R) = B`. -/
theorem recourse_full [NeZero m] (c : SetCost m) (η : ℝ) (hη : 0 ≤ η) (R : ℕ)
    (K : Finset (Fin (m + 1))) (hK : K.Nonempty) (hR : ∀ k ∈ K, k.val ≤ R ∨ m - k.val ≤ R) :
    genRecourse c η R K hK = genAware c η K hK := by
  refine le_antisymm ?_ (aware_le_recourse c η hη R K hK)
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  have hnear : ∀ k : Fin (m + 1), ∃ Q ∈ SubFeasible (m := m) k.val η,
      ∑ S, Q S * c k S < genLayer c η k + ε := by
    intro k
    obtain ⟨_, ⟨Q, hQ, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt ((sub_nonempty η hη k).image _)
      (show genLayer c η k < genLayer c η k + ε by linarith)
    exact ⟨Q, hQ, hlt⟩
  choose Qf hQf hQc using hnear
  obtain ⟨P, hP⟩ := allPerm_feasible_nonempty m η hη
  have hmem : K.sup' hK (fun k => genPlanCost c k (indepPlan P (Qf k)))
      ∈ genRecourseSet c η R K hK :=
    ⟨P, hP, fun k => indepPlan P (Qf k),
      fun k hk => indep_feasible P η hP k R (hR k hk) (Qf k) (hQf k), rfl⟩
  refine lt_of_le_of_lt (csInf_le (genRecourse_bdd c η R K hK) hmem) ?_
  rw [Finset.sup'_lt_iff]
  intro k hk
  rw [genIndep_cost c P hP.2.1]
  calc _ < genLayer c η k + ε := hQc k
    _ ≤ genAware c η K hK + ε := by
      have := Finset.le_sup' (fun k => genLayer c η k) hk
      unfold genAware; linarith

/-! ## 4. The band is vacuous once `η ≥ m` -/

theorem ind_mem_unit (i : Fin m) (S : Finset (Fin m)) : 0 ≤ ind i S ∧ ind i S ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

theorem inPrefixInd_mem_unit (σ : Equiv.Perm (Fin m)) (k : ℕ) (i : Fin m) :
    0 ≤ inPrefixInd σ k i ∧ inPrefixInd σ k i ≤ 1 := by
  unfold inPrefixInd; split_ifs <;> norm_num

/-- A number in `[0,1]` is within `η/m` of `k/m` once `η ≥ m` (`k ≤ m`). -/
theorem band_vacuous [NeZero m] {η : ℝ} (hη : (m : ℝ) ≤ η) (k : ℕ) (hk : k ≤ m) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : |x - (k : ℝ) / m| ≤ η / m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have ht0 : 0 ≤ (k : ℝ) / m := div_nonneg (Nat.cast_nonneg _) hmR.le
  have ht1 : (k : ℝ) / m ≤ 1 := (div_le_one hmR).mpr (by exact_mod_cast hk)
  have h1 : |x - (k : ℝ) / m| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have h2 : (1 : ℝ) ≤ η / m := (one_le_div hmR).mpr hη
  linarith

/-- **At `η ≥ m` every probability law on rankings is band-feasible.** -/
theorem feasibleAt_vacuous_iff [NeZero m] {η : ℝ} (hη : (m : ℝ) ≤ η)
    (P : Equiv.Perm (Fin m) → ℝ) :
    P ∈ FeasibleAt (id : Equiv.Perm (Fin m) → _) η ↔ (∀ σ, 0 ≤ P σ) ∧ ∑ σ, P σ = 1 := by
  refine ⟨fun hP => ⟨hP.1, hP.2.1⟩, fun ⟨h0, h1⟩ => ⟨h0, h1, fun k hk i => ?_⟩⟩
  obtain ⟨a, b⟩ := expect_mem_unit P h0 h1 (fun σ => inPrefixInd (id σ) k i)
    (fun σ => (inPrefixInd_mem_unit σ k i).1) (fun σ => (inPrefixInd_mem_unit σ k i).2)
  exact band_vacuous hη k hk a b

/-- **At `η ≥ m` every probability law on `k`-sets is band-feasible.** -/
theorem subFeasible_vacuous_iff [NeZero m] {η : ℝ} (hη : (m : ℝ) ≤ η) (k : ℕ) (hk : k ≤ m)
    (Q : Finset (Fin m) → ℝ) :
    Q ∈ SubFeasible k η ↔
      (∀ S, 0 ≤ Q S) ∧ ∑ S, Q S = 1 ∧ ∀ S, Q S ≠ 0 → S.card = k := by
  refine ⟨fun hQ => ⟨hQ.1, hQ.2.1, hQ.2.2.1⟩, fun ⟨h0, h1, h2⟩ => ⟨h0, h1, h2, fun i => ?_⟩⟩
  obtain ⟨a, b⟩ := expect_mem_unit Q h0 h1 (ind i) (fun S => (ind_mem_unit i S).1)
    (fun S => (ind_mem_unit i S).2)
  exact band_vacuous hη k hk a b

/-- **At `η ≥ m` the final-law band of a plan is vacuous.** -/
theorem planFeasible_vacuous_iff [NeZero m] {η : ℝ} (hη : (m : ℝ) ≤ η)
    (P : Equiv.Perm (Fin m) → ℝ) (hP1 : ∑ σ, P σ = 1) (k : Fin (m + 1)) (R : ℕ)
    (J : Equiv.Perm (Fin m) → Finset (Fin m) → ℝ) :
    J ∈ PlanFeasible P k R η ↔
      (∀ σ T, 0 ≤ J σ T) ∧ (∀ σ, ∑ T, J σ T = P σ) ∧
        ∀ σ T, J σ T ≠ 0 → T.card = k.val ∧ (prefixSet σ k \ T).card ≤ R := by
  refine ⟨fun hJ => ⟨hJ.1, hJ.2.1, hJ.2.2.1⟩, fun ⟨h0, h1, h2⟩ => ⟨h0, h1, h2, fun i => ?_⟩⟩
  have hF0 : ∀ T, 0 ≤ finalLaw J T := fun T => Finset.sum_nonneg fun σ _ => h0 σ T
  have hF1 : ∑ T, finalLaw J T = 1 := by
    have := final_sum J (fun _ => 1)
    simp only [mul_one] at this
    rw [this, Finset.sum_congr rfl fun σ _ => h1 σ, hP1]
  obtain ⟨a, b⟩ := expect_mem_unit (finalLaw J) hF0 hF1 (ind i)
    (fun S => (ind_mem_unit i S).1) (fun S => (ind_mem_unit i S).2)
  rw [final_sum] at a b
  exact band_vacuous hη k.val (Nat.lt_succ_iff.mp k.isLt) a b

/-- The point mass on one set. -/
noncomputable def ptSet (S0 : Finset (Fin m)) : Finset (Fin m) → ℝ :=
  fun S => if S = S0 then 1 else 0

theorem ptSet_expect (S0 : Finset (Fin m)) (f : Finset (Fin m) → ℝ) :
    ∑ S, ptSet S0 S * f S = f S0 := by
  unfold ptSet; simp [ite_mul]

/-- **At a vacuous band the layer is the plain per-budget optimum.** -/
theorem genLayer_vacuous [NeZero m] (c : SetCost m) {η : ℝ} (hη : (m : ℝ) ≤ η)
    (k : Fin (m + 1)) : genLayer c η k = optLoss c k := by
  have hk : k.val ≤ m := Nat.lt_succ_iff.mp k.isLt
  obtain ⟨S0, hS0, hopt⟩ := exists_opt c k
  apply le_antisymm
  · have hQ : ptSet S0 ∈ SubFeasible k.val η := by
      rw [subFeasible_vacuous_iff hη k.val hk]
      refine ⟨fun S => by unfold ptSet; split_ifs <;> norm_num, ?_, fun S hS => ?_⟩
      · have := ptSet_expect S0 (fun _ => 1)
        simpa only [mul_one] using this
      · have : S = S0 := by by_contra h; apply hS; unfold ptSet; simp [h]
        rw [this, hS0]
    calc genLayer c η k ≤ ∑ S, ptSet S0 S * c k S := genLayer_le c η k _ hQ
      _ = optLoss c k := by rw [ptSet_expect, hopt]
  · have hne : (SubFeasible (m := m) k.val η).Nonempty := sub_nonempty η
      (le_trans (Nat.cast_nonneg m) hη) k
    refine le_csInf (hne.image _) ?_
    rintro _ ⟨Q, hQ, rfl⟩
    calc optLoss c k = ∑ S, Q S * optLoss c k := by rw [← Finset.sum_mul, hQ.2.1, one_mul]
      _ ≤ ∑ S, Q S * c k S := by
        refine Finset.sum_le_sum fun S _ => ?_
        by_cases h : Q S = 0
        · rw [h, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left (optLoss_le c k S (hQ.2.2.1 S h)) (hQ.1 S)

/-- **At a vacuous band, B of a regret cost is `0`.** -/
theorem genAware_vacuous_regret [NeZero m] (ℓ : SetCost m) {η : ℝ} (hη : (m : ℝ) ≤ η)
    (K : Finset (Fin (m + 1))) (hK : K.Nonempty) : genAware (regretOf ℓ) η K hK = 0 := by
  unfold genAware
  have e : (fun k => genLayer (regretOf ℓ) η k) = fun _ => (0 : ℝ) :=
    funext fun k => by rw [genLayer_vacuous _ hη k, optLoss_regretOf]
  rw [e]; exact Finset.sup'_const hK 0

/-- A regret cost has nonnegative U. -/
theorem genTrue_regret_nonneg [NeZero m] (ℓ : SetCost m) (η : ℝ) (hη : 0 ≤ η)
    (K : Finset (Fin (m + 1))) (hK : K.Nonempty) : 0 ≤ genTrue (regretOf ℓ) η K hK := by
  refine le_csInf (genTrue_image_nonempty _ η hη K hK) ?_
  rintro _ ⟨P, hP, rfl⟩
  obtain ⟨k0, hk0⟩ := id hK
  refine le_trans ?_ (Finset.le_sup' (fun k => ∑ σ, P σ * regretOf ℓ k (prefixSet σ k)) hk0)
  exact le_expect P hP.1 hP.2.1 _ 0 fun σ => regretOf_nonneg ℓ k0 _ (prefixSet_card σ k0)

/-! ## 5. Paper C's signed objective is an instance -/

/-- **C's cost is the regret form of `|Σ_{i∈S} g_i| / ‖g‖₁`.** -/
theorem subCost_eq_regretOf (g : Fin m → ℝ) :
    subCost g = regretOf (fun _ S => |∑ i ∈ S, g i| / normMass g) := by
  funext k S
  unfold subCost regretOf optLoss trueBaseline CIGAMF.P13.PaperCFrontier.baseline
  have hD := normMass_nonneg g
  obtain ⟨S0, hS0, hmin⟩ := Finset.exists_mem_eq_inf' (subsets_nonempty k)
    (fun S : Finset (Fin m) => |∑ i ∈ S, g i|)
  have e : (univ.filter (fun S : Finset (Fin m) => S.card = k.val)).inf' (subsets_nonempty k)
      (fun S => |∑ i ∈ S, g i| / normMass g)
      = (univ.filter (fun S : Finset (Fin m) => S.card = k.val)).inf' (subsets_nonempty k)
          (fun S => |∑ i ∈ S, g i|) / normMass g := by
    apply le_antisymm
    · rw [hmin]; exact Finset.inf'_le _ hS0
    · refine Finset.le_inf' _ _ fun S hS => ?_
      exact div_le_div_of_nonneg_right (Finset.inf'_le _ hS) hD
  rw [e, sub_div]

theorem objective_eq_gen (g : Fin m → ℝ) (P : Equiv.Perm (Fin m) → ℝ)
    (K : Finset (Fin (m + 1))) (hK : K.Nonempty) :
    trueObjective g P K hK = genObjective (subCost g) P K hK := rfl

/-- **C's U is the generic U at `c = subCost g`.** -/
theorem trueValue_eq_gen (g : Fin m → ℝ) (η : ℝ) (K : Finset (Fin (m + 1))) (hK : K.Nonempty) :
    trueValue g η K hK = genTrue (subCost g) η K hK := rfl

theorem layerValue_eq_gen (g : Fin m → ℝ) (η : ℝ) (k : Fin (m + 1)) :
    layerValue g η k = genLayer (subCost g) η k := rfl

/-- **C's B is the generic B at `c = subCost g`.** -/
theorem awareValue_eq_gen (g : Fin m → ℝ) (η : ℝ) (K : Finset (Fin (m + 1)))
    (hK : K.Nonempty) : awareValue g η K hK = genAware (subCost g) η K hK := rfl

theorem planCost_eq_gen (g : Fin m → ℝ) (k : Fin (m + 1))
    (J : Equiv.Perm (Fin m) → Finset (Fin m) → ℝ) :
    planCost g k J = genPlanCost (subCost g) k J := rfl

/-- **C's V^(R) is the generic V^(R) at `c = subCost g`.** -/
theorem recourseValue_eq_gen (g : Fin m → ℝ) (η : ℝ) (R : ℕ) (K : Finset (Fin (m + 1)))
    (hK : K.Nonempty) : recourseValue g η R K hK = genRecourse (subCost g) η R K hK := rfl

/-- C's `recourse_full`, re-derived from the generic one through the instance. -/
theorem c_recourse_full_via_gen [NeZero m] (g : Fin m → ℝ) (η : ℝ) (hη : 0 ≤ η) (R : ℕ)
    (K : Finset (Fin (m + 1))) (hK : K.Nonempty) (hR : ∀ k ∈ K, k.val ≤ R ∨ m - k.val ≤ R) :
    recourseValue g η R K hK = awareValue g η K hK := by
  rw [recourseValue_eq_gen, awareValue_eq_gen]
  exact recourse_full (subCost g) η hη R K hK hR

/-- C's `recourse_zero`, re-derived from the generic one. -/
theorem c_recourse_zero_via_gen [NeZero m] (g : Fin m → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (K : Finset (Fin (m + 1))) (hK : K.Nonempty) :
    recourseValue g η 0 K hK = trueValue g η K hK := by
  rw [recourseValue_eq_gen, trueValue_eq_gen]
  exact recourse_zero (subCost g) η hη K hK

/-! ## 6. Satisfiability witnesses -/

/-- The interior budgets `{1, …, m-1}`. -/
def interior (m : ℕ) : Finset (Fin (m + 1)) := univ.filter (fun k => 1 ≤ k.val ∧ k.val ≤ m - 1)

theorem interior_nonempty (m : ℕ) (hm : 2 ≤ m) : (interior m).Nonempty :=
  ⟨⟨1, by omega⟩, by simp [interior]; omega⟩

/-- **The hypothesis of `recourse_full` is satisfiable**: `m = 3`, `K = {1,2}`, `R = 1`. -/
theorem recourse_full_hyp_witness :
    ∀ k ∈ interior 3, k.val ≤ 1 ∨ 3 - k.val ≤ 1 := by
  intro k hk
  simp only [interior, mem_filter, mem_univ, true_and] at hk
  omega

/-- For every `m ≥ 2`, `R = ⌊m/2⌋` satisfies the hypothesis of `recourse_full` on the interior. -/
theorem recourse_full_hyp_half (m : ℕ) : ∀ k ∈ interior m, k.val ≤ m / 2 ∨ m - k.val ≤ m / 2 := by
  intro k _
  omega

/-- **The vacuous band is admissible**: `η = m` is nonnegative and meets `m ≤ η`. -/
theorem vacuous_band_witness (m : ℕ) : 0 ≤ (m : ℝ) ∧ (m : ℝ) ≤ (m : ℝ) :=
  ⟨Nat.cast_nonneg m, le_rfl⟩

/-- **All hypotheses of the order theorems hold together** (`m = 3`, `η = 3`, `K = {1,2}`),
and the values are infima over inhabited sets there. -/
theorem order_hyps_witness (c : SetCost 3) :
    (genRecourseSet c 3 1 (interior 3) (interior_nonempty 3 (by norm_num))).Nonempty ∧
      ((fun P => genObjective c P (interior 3) (interior_nonempty 3 (by norm_num))) ''
        FeasibleAt (id : Equiv.Perm (Fin 3) → _) 3).Nonempty ∧
      (SubFeasible (m := 3) 1 3).Nonempty :=
  ⟨genRecourseSet_nonempty c 3 (by norm_num) 1 _ _,
    genTrue_image_nonempty c 3 (by norm_num) _ _,
    sub_nonempty (m := 3) 3 (by norm_num) ⟨1, by norm_num⟩⟩

#print axioms optLoss_regretOf
#print axioms aware_le_true
#print axioms aware_le_recourse
#print axioms recourse_le_true
#print axioms recourse_zero
#print axioms recourse_mono
#print axioms recourse_full
#print axioms feasibleAt_vacuous_iff
#print axioms subFeasible_vacuous_iff
#print axioms planFeasible_vacuous_iff
#print axioms genLayer_vacuous
#print axioms genAware_vacuous_regret
#print axioms genTrue_regret_nonneg
#print axioms subCost_eq_regretOf
#print axioms trueValue_eq_gen
#print axioms awareValue_eq_gen
#print axioms recourseValue_eq_gen
#print axioms c_recourse_full_via_gen
#print axioms c_recourse_zero_via_gen
#print axioms recourse_full_hyp_witness
#print axioms recourse_full_hyp_half
#print axioms order_hyps_witness

end CIGAMF.P13.MarlGenericRecourse
