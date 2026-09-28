import «LeanStructuralStaircaseToleranceLowerV1»

namespace CIGAMF.P13.StructuralBudgetRecourse
open Finset
open scoped BigOperators
open CIGAMF.V4.SupportGeometry CIGAMF.V4.StructuralRankability
open CIGAMF.P13.StructuralPrefixCoverDimension CIGAMF.P13.StructuralStaircaseFamily
open CIGAMF.P13.StructuralStaircaseExactPrefixCover
open CIGAMF.P13.StructuralStaircaseToleranceLower
open CIGAMF.P13.StructuralUnboundedPrefixCoverFamily
noncomputable section
attribute [local instance] Classical.propDecidable
variable {r : ℕ}

def recourse {E : Type*} [DecidableEq E] (S T : Finset E) : ℕ :=
  (S \ T).card - (S.card-T.card)

lemma selected_difference (t u : Fin r) (hne : t ≠ u) :
    staircaseSelected t \ staircaseSelected u =
      insert (u,true) ((Ioc t u).image (fun i => (i,false))) := by
  ext ⟨i,b⟩
  cases b <;> simp [staircaseSelected,staircaseBlock,mem_sdiff,not_le,Prod.mk.injEq]
  · aesop

lemma deletion_card (t u : Fin r) (hne : t ≠ u) :
    (staircaseSelected t \ staircaseSelected u).card = u.val-t.val+1 := by
  rw [selected_difference t u hne,card_insert_of_notMem (by simp)]
  rw [card_image_of_injective _ (fun i j h => Prod.mk.inj h |>.1)]
  simp

theorem transition_law (t u : Fin r) :
    recourse (staircaseSelected t) (staircaseSelected u) = if t=u then 0 else 1 := by
  by_cases h : t=u
  · subst u; simp [recourse]
  · rw [if_neg h,recourse,deletion_card t u h,staircaseSelected_card,staircaseSelected_card]
    have ht := t.isLt
    have hu := u.isLt
    omega

theorem good_decision_forced (hr : 0 < r) (eps : ℝ) (heps : 2*(r:ℝ)*eps < 1)
    (t : Fin r) (S : Finset (StairRel r))
    (hS : EpsilonOptimalAt (fun T => selectedRadius staircaseF T/(r:ℝ)) eps
      (staircaseSelected t).card S) : S=staircaseSelected t := by
  exact staircaseSelected_unique_optimal hr t S
    (normalized_epsilon_exact hr eps heps _ S hS)

/-- Every admissible policy has the same total excess recourse on a finite sequence
of critical budgets. Thus its value is also the minimum over all such policies. -/
theorem policy_total (hr : 0 < r) (eps : ℝ) (heps : 2*(r:ℝ)*eps < 1)
    (n : ℕ) (t : ℕ → Fin r) (S : ℕ → Finset (StairRel r))
    (hS : ∀ i ≤ n,EpsilonOptimalAt (fun T => selectedRadius staircaseF T/(r:ℝ)) eps
      (staircaseSelected (t i)).card (S i)) :
    (∑ i ∈ range n,recourse (S i) (S (i+1))) =
      ∑ i ∈ range n,if t i=t (i+1) then 0 else 1 := by
  apply sum_congr rfl
  intro i hi
  have hil : i < n := mem_range.mp hi
  rw [good_decision_forced hr eps heps _ _ (hS i (by omega)),
    good_decision_forced hr eps heps _ _ (hS (i+1) (by omega)),transition_law]

#print axioms selected_difference
#print axioms deletion_card
#print axioms transition_law
#print axioms good_decision_forced
#print axioms policy_total
end
end CIGAMF.P13.StructuralBudgetRecourse
