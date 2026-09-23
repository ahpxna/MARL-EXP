import «LeanPaperCFlowLawV1»
import «LeanPaperCLawPushV1»
import «LeanPaperCRelabelV1»
import «LeanPaperCFamilyV1»

/-!
DRAFT — NOT COMPILED. The missing #15 join, with actual marginal constraints.
The reverse map is NOT the arbitrary section law: that law is uniformly relabelled inside
EACH type before being pushed onto all permutations. This preserves the entire count path
and hence the entire objective vector. No hconst, hocc, section or band-transfer premise
appears in the final equivalence. Zero-multiplicity types impose no divided constraint.
-/
namespace CIGAMF.P13.PaperCFlowBandJoin
open Finset
open CIGAMF.P13.CFinal CIGAMF.P13.PaperCFlow
open CIGAMF.P13.PaperCHorizon CIGAMF.P13.PaperCRankFlow
open CIGAMF.P13.PaperCFlowLaw CIGAMF.P13.PaperCNaming
open CIGAMF.P13.PaperCRelabel CIGAMF.P13.PaperCLawPush
open CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCBreakpoint
open CIGAMF.P13.PaperCRanking CIGAMF.P13.PaperCEndpoint
open CIGAMF.P13.PaperCFamily
open CIGAMF.P13.PaperCInstantiation
variable {d m : ℕ}

noncomputable def typeLabel (ty : Fin m → Fin d) : Ranking m :=
  fun i => ((ty i).val : ℝ)

lemma typeLabel_eq_iff (ty : Fin m → Fin d) (i j : Fin m) :
    typeLabel ty i = typeLabel ty j ↔ ty i = ty j := by
  simp only [typeLabel, Nat.cast_inj, Fin.ext_iff]

noncomputable def typeMean (ty : Fin m → Fin d) (F : LayeredFlow (CState d m))
    (k : Fin (m+1)) (τ : Fin d) : ℝ :=
  (∑ v, F.x k.val v * (v τ).val) / (mult ty τ : ℝ)

def FlowBand (ty : Fin m → Fin d) (F : LayeredFlow (CState d m)) (η : ℝ) : Prop :=
  ∀ k : Fin (m+1), ∀ τ, 0 < mult ty τ →
    |typeMean ty F k τ - (k.val : ℝ)/(m : ℝ)| ≤ η/(m : ℝ)

/-- Count positions inside `Fin m` first. Extending the prefix by one inserts exactly
one position; this removes the dependent `dite` from the later permutation reindexing. -/
lemma layerCount_eq_prefix_card (s : Fin m → Fin d) (τ : Fin d) :
    ∀ k : ℕ, k ≤ m →
      layerCount m s k τ =
        ((univ.filter (fun p : Fin m => p.val < k)).filter (fun p => s p = τ)).card := by
  classical
  intro k
  induction k with
  | zero =>
      intro hk
      simp [layerCount]
  | succ k ih =>
      intro hk
      have hkm : k < m := by omega
      have hprefix :
          univ.filter (fun p : Fin m => p.val < k + 1) =
            insert ⟨k, hkm⟩ (univ.filter (fun p : Fin m => p.val < k)) := by
        ext p
        simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
        omega
      rw [layerCount_succ m s k hkm τ, ih (by omega), hprefix, Finset.filter_insert]
      by_cases ht : s ⟨k, hkm⟩ = τ <;> simp [ht]

/-- Counts and item indicators count the SAME filtered prefix. The first half is a
cardinality identity; only after it is proved do we reindex positions by the permutation. -/
lemma count_eq_item_sum (ty : Fin m → Fin d) (σ : Equiv.Perm (Fin m))
    (k : Fin (m + 1)) (τ : Fin d) :
    ((rankLayer ty k σ τ).val : ℝ) =
      ∑ i ∈ univ.filter (fun i => ty i = τ), inPrefixInd σ k.val i := by
  classical
  change (layerCount m (fun p => ty (σ p)) k.val τ : ℝ) = _
  rw [layerCount_eq_prefix_card _ τ k.val (Nat.le_of_lt_succ k.isLt)]
  have hcard :
      (((univ.filter (fun p : Fin m => p.val < k.val)).filter
        (fun p => ty (σ p) = τ)).card : ℝ) =
      ∑ p ∈ univ.filter (fun p : Fin m => p.val < k.val),
        (if ty (σ p) = τ then (1 : ℝ) else 0) := by
    rw [Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro p hp
    split_ifs <;> norm_num
  rw [hcard, Finset.sum_filter, Finset.sum_filter,
    ← Equiv.sum_comp σ (fun i => if ty i = τ then inPrefixInd σ k.val i else 0)]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [inPrefixInd, Equiv.symm_apply_apply]
  by_cases hk : p.val < k.val <;> by_cases ht : ty (σ p) = τ <;> simp [hk, ht]

lemma mult_pos_at (ty : Fin m → Fin d) (i : Fin m) : 0 < mult ty (ty i) := by
  exact Finset.card_pos.mpr ⟨i, by simp [mult]⟩

lemma rankFlow_typeMean (ty : Fin m → Fin d) (P : Equiv.Perm (Fin m) → ℝ)
    (hP : ∀ σ, 0 ≤ P σ) (k : Fin (m+1)) (τ : Fin d) :
    typeMean ty (rankingFlow P hP ty) k τ =
      (∑ i ∈ univ.filter (fun i => ty i = τ),
        ∑ σ, P σ * inPrefixInd σ k.val i) / (mult ty τ : ℝ) := by
  unfold typeMean
  rw [← rankingFlow_budget_vector P hP ty (fun _ v => ((v τ).val : ℝ)) k]
  simp_rw [count_eq_item_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Average the item bands over a nonempty type. -/
theorem rankingFlow_band (ty : Fin m → Fin d) (η : ℝ)
    (P : Equiv.Perm (Fin m) → ℝ) (hP : P ∈ FeasibleAt id η) :
    FlowBand ty (rankingFlow P hP.1 ty) η := by
  classical
  intro k τ hτ
  rw [rankFlow_typeMean]
  have hc : (0 : ℝ) < mult ty τ := by exact_mod_cast hτ
  have heq :
      (∑ i ∈ univ.filter (fun i => ty i = τ),
        ∑ σ, P σ * inPrefixInd σ k.val i) / (mult ty τ : ℝ) - k.val / (m : ℝ)
      = (∑ i ∈ univ.filter (fun i => ty i = τ),
          ((∑ σ, P σ * inPrefixInd σ k.val i) - k.val / (m : ℝ))) /
          (mult ty τ : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    change _ = (_ - (mult ty τ : ℝ) * _) / _
    field_simp
  rw [heq, abs_div, abs_of_pos hc]
  apply (div_le_iff₀ hc).2
  calc |∑ i ∈ univ.filter (fun i => ty i = τ),
        ((∑ σ, P σ * inPrefixInd σ k.val i) - k.val / (m : ℝ))|
      ≤ ∑ i ∈ univ.filter (fun i => ty i = τ),
          |(∑ σ, P σ * inPrefixInd σ k.val i) - k.val / (m : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ univ.filter (fun i => ty i = τ), η/(m : ℝ) := by
      apply Finset.sum_le_sum; intro i hi
      simpa using hP.2.2 k.val (Nat.le_of_lt_succ k.isLt) i
    _ = η/(m : ℝ) * (mult ty τ : ℝ) := by simp [mult]; ring

noncomputable def symLaw (ty : Fin m → Fin d) (P : Equiv.Perm (Fin m) → ℝ) :=
  pushLaw (fun z : WPerm (typeLabel ty) × Equiv.Perm (Fin m) => z.1.val * z.2)
    (fun z => P z.2 / (Fintype.card (WPerm (typeLabel ty)) : ℝ))

lemma symLaw_probability (ty : Fin m → Fin d) (P : Equiv.Perm (Fin m) → ℝ)
    (hP : RankingLaw P) : RankingLaw (symLaw ty P) := by
  classical
  have hc : (0 : ℝ) < Fintype.card (WPerm (typeLabel ty)) := by
    exact_mod_cast Fintype.card_pos
  constructor
  · exact pushLaw_nonneg _ _ (fun z => div_nonneg (hP.1 z.2) hc.le)
  · rw [symLaw, pushLaw_sum, Fintype.sum_prod_type]
    simp_rw [← Finset.sum_div, hP.2]
    simp [ne_of_gt hc]

lemma relabel_layer (ty : Fin m → Fin d) (ρ : WPerm (typeLabel ty))
    (k : Fin (m+1)) (σ : Equiv.Perm (Fin m)) :
    rankLayer ty k (ρ.val * σ) = rankLayer ty k σ := by
  let ρ' : TypeStab ty := ⟨ρ.val, fun i =>
    (typeLabel_eq_iff ty (ρ.val i) i).mp (ρ.property i)⟩
  exact rankLayer_smul ty ρ' k σ

/-- Symmetrising changes individual labels, never a count-path objective. -/
lemma symLaw_objective (ty : Fin m → Fin d) (P : Equiv.Perm (Fin m) → ℝ)
    (c : Fin (m+1) → CState d m → ℝ) :
    rankObj ty c (symLaw ty P) = rankObj ty c P := by
  classical
  funext k
  unfold rankObj symLaw
  rw [pushLaw_expect, Fintype.sum_prod_type]
  simp_rw [relabel_layer, div_mul_eq_mul_div, ← Finset.sum_div]
  simp [Fintype.card_ne_zero]

lemma symLaw_marginal (ty : Fin m → Fin d) (P : Equiv.Perm (Fin m) → ℝ)
    (k : Fin (m+1)) (i : Fin m) :
    (∑ σ, symLaw ty P σ * inPrefixInd σ k.val i) =
      (∑ j ∈ univ.filter (fun j => ty j = ty i),
        ∑ σ, P σ * inPrefixInd σ k.val j) / (mult ty (ty i) : ℝ) := by
  classical
  let M := relMarg (fun ρ : WPerm (typeLabel ty) => ρ.val) id P k.val
  have hconst : ∀ j, ty j = ty i → M j = M i := by
    intro j hj
    obtain ⟨ρ, hρ⟩ := wperm_orbit (typeLabel ty) i j
      ((typeLabel_eq_iff ty i j).2 hj.symm)
    simpa [M, hρ] using relMarg_const_of_orbit
      (fun ρ : WPerm (typeLabel ty) => ρ.val) id P k.val
      (wperm_trans (typeLabel ty)) ρ i
  have hmass := relMarg_class_sum (typeLabel ty)
    (fun ρ : WPerm (typeLabel ty) => ρ.val) (fun ρ => ρ.property)
    id P k.val (typeLabel ty i)
  simp only [typeLabel_eq_iff, baseMarg, id_eq] at hmass
  have hsum : (∑ j ∈ univ.filter (fun j => ty j = ty i), M j)
      = (mult ty (ty i) : ℝ) * M i := by
    rw [Finset.sum_congr rfl (fun j hj => hconst j (by simpa using hj))]
    simp [mult]
  have hc : (mult ty (ty i) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (mult_pos_at ty i))
  change (∑ σ, symLaw ty P σ * inPrefixInd σ k.val i) = _
  rw [symLaw, pushLaw_expect]
  change M i = _
  apply (eq_div_iff hc).2
  simpa [hsum, mul_comm, M] using hmass

noncomputable def bandFlowLaw (ty : Fin m → Fin d) (F : LayeredFlow (CState d m)) :=
  symLaw ty (flowLaw ty F)

lemma bandFlowLaw_vector (ty : Fin m → Fin d) (F : LayeredFlow (CState d m))
    (hF : CountFeasibleH ty F) (c : Fin (m+1) → CState d m → ℝ) :
    rankObj ty c (bandFlowLaw ty F) = flowObj c F := by
  rw [bandFlowLaw, symLaw_objective]
  funext k
  unfold rankObj flowObj
  rw [objective_transports]
  apply Finset.sum_congr rfl
  intro v hv
  rw [show flowX (flowLaw ty F) ty k v = occ (flowLaw ty F) (rankLayer ty k) v from rfl,
    flowLaw_occ ty F hF k v]

lemma bandFlowLaw_marginal (ty : Fin m → Fin d) (F : LayeredFlow (CState d m))
    (hF : CountFeasibleH ty F) (k : Fin (m+1)) (i : Fin m) :
    (∑ σ, bandFlowLaw ty F σ * inPrefixInd σ k.val i) = typeMean ty F k (ty i) := by
  rw [bandFlowLaw, symLaw_marginal]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, ← count_eq_item_sum]
  have hv := congrFun (bandFlowLaw_vector ty F hF
    (fun _ v => ((v (ty i)).val : ℝ))) k
  rw [bandFlowLaw, symLaw_objective] at hv
  exact congrArg (fun x : ℝ => x / (mult ty (ty i) : ℝ)) hv

/-- The constructed law, not a hypothetical law, satisfies the ITEM band. -/
theorem bandFlowLaw_feasible (ty : Fin m → Fin d) (F : LayeredFlow (CState d m))
    (η : ℝ) (hF : CountFeasibleH ty F) (hband : FlowBand ty F η) :
    bandFlowLaw ty F ∈ FeasibleAt id η := by
  have hprob := symLaw_probability ty (flowLaw ty F)
    ⟨flowLaw_nonneg ty F, flowLaw_sum ty F hF.1⟩
  refine ⟨hprob.1, hprob.2, ?_⟩
  intro k hk i
  simp only [id_eq]
  rw [show k = (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (m+1)).val from rfl,
    bandFlowLaw_marginal ty F hF ⟨k, Nat.lt_succ_of_le hk⟩ i]
  exact hband _ (ty i) (mult_pos_at ty i)

/-- #15 WITH bands, in both directions, preserving all budgets simultaneously. -/
theorem banded_vectors_agree (ty : Fin m → Fin d) (η : ℝ)
    (c : Fin (m+1) → CState d m → ℝ) :
    {y | ∃ P ∈ FeasibleAt (id : Equiv.Perm (Fin m) → _) η, rankObj ty c P = y} =
    {y | ∃ F, CountFeasibleH ty F ∧ FlowBand ty F η ∧ flowObj c F = y} := by
  ext y
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨rankingFlow P hP.1 ty, rankingFlow_feasible P hP.1 hP.2.1 ty,
      rankingFlow_band ty η P hP, funext (fun k =>
        (rankingFlow_budget_vector P hP.1 ty c k).symm)⟩
  · rintro ⟨F, hF, hb, rfl⟩
    exact ⟨bandFlowLaw ty F, bandFlowLaw_feasible ty F η hF hb,
      bandFlowLaw_vector ty F hF c⟩

/-- Instantiation at the ACTUAL four-weight family and its signed-prefix objective. -/
def familyType (m : ℕ) (i : Fin m) : Fin 4 :=
  if i.val = 0 then 0 else if i.val = m-1 then 3
  else if i.val ≤ (m-1)/2 then 1 else 2

def typeWeight (τ : Fin 4) : ℝ := ![-3,-1,1,3] τ

lemma familyType_weight (m : ℕ) (i : Fin m) :
    typeWeight (familyType m i) = gFamily m i := by
  unfold familyType typeWeight gFamily gN
  split_ifs <;>
    first
      | rfl
      | norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_succ]

noncomputable def signedCost (D : ℝ) (k : Fin (m+1)) (v : CState 4 m) : ℝ :=
  (|∑ τ, typeWeight τ * ((v τ).val : ℝ)| - (k.val % 2 : ℕ)) / D

lemma typed_prefix_sum (ty : Fin m → Fin d) (w : Fin d → ℝ)
    (σ : Equiv.Perm (Fin m)) (k : Fin (m+1)) :
    ∑ τ, w τ * ((rankLayer ty k σ τ).val : ℝ) =
      prefixSum (fun p => w (ty (σ p))) k.val := by
  classical
  simp_rw [count_eq_item_sum, Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp only [mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Equiv.sum_comp σ]
  simp [prefixSum, inPrefixInd, Equiv.symm_apply_apply]

lemma signedCost_eq_regret (D : ℝ) (σ : Equiv.Perm (Fin m)) (k : Fin (m+1)) :
    signedCost D k (rankLayer (familyType m) k σ) = regret (gFamily m) σ D k.val := by
  unfold signedCost regret excess rankOf
  rw [typed_prefix_sum]
  simp_rw [familyType_weight]

/-- The count LP represents the paper's own regret, not a surrogate count objective. -/
theorem actual_banded_vectors (D η : ℝ) :
    {y : Fin (m+1) → ℝ | ∃ P ∈ FeasibleAt (id : Equiv.Perm (Fin m) → _) η,
      (fun k => ∑ σ, P σ * regret (gFamily m) σ D k.val) = y} =
    {y | ∃ F, CountFeasibleH (familyType m) F ∧ FlowBand (familyType m) F η ∧
      flowObj (signedCost D) F = y} := by
  convert banded_vectors_agree (familyType m) η (signedCost D) using 1
  ext y
  simp only [rankObj, signedCost_eq_regret]

/-- ANY functional of the vector, including max over the interior budgets, has equal infima. -/
theorem actual_banded_infima (D η : ℝ) (Φ : (Fin (m+1) → ℝ) → ℝ) :
    sInf (Φ '' {y : Fin (m+1) → ℝ | ∃ P ∈ FeasibleAt (id : Equiv.Perm (Fin m) → _) η,
      (fun k => ∑ σ, P σ * regret (gFamily m) σ D k.val) = y}) =
    sInf (Φ '' {y | ∃ F, CountFeasibleH (familyType m) F ∧ FlowBand (familyType m) F η ∧
      flowObj (signedCost D) F = y}) := by
  rw [actual_banded_vectors]

#print axioms layerCount_eq_prefix_card
#print axioms count_eq_item_sum
#print axioms rankingFlow_band
#print axioms bandFlowLaw_marginal
#print axioms bandFlowLaw_feasible
#print axioms actual_banded_vectors
#print axioms actual_banded_infima
end CIGAMF.P13.PaperCFlowBandJoin
