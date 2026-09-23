import «LeanPaperCLawPushV1»
import «LeanPaperCRelabelV1»

/-! DRAFT source, not compiled. Transport of the same law between two rearranged bases.
The item labels move, positions do not. The per-item band and the entire regret vector
are preserved. This is used by the concrete even and odd witnesses below. -/
namespace CIGAMF.P13.PaperCLawRelabel
open Finset
open CIGAMF.P13.PaperCRanking CIGAMF.P13.PaperCInstantiation
open CIGAMF.P13.PaperCEndpoint CIGAMF.P13.PaperCValueSet
open CIGAMF.P13.PaperCLawPush CIGAMF.P13.PaperCRelabel
variable {m : ℕ} {R : Type*} [Fintype R]

theorem feasible_left_relabel (P : R → ℝ) (perm : R → Equiv.Perm (Fin m))
    (σ : Equiv.Perm (Fin m)) (η : ℝ) (hP : P ∈ FeasibleAt perm η) :
    P ∈ FeasibleAt (fun x => σ * perm x) η := by
  refine ⟨hP.1,hP.2.1,?_⟩
  intro k hk i
  simp_rw [inPrefixInd_relabel]
  exact hP.2.2 k hk (σ.symm i)

theorem rankOf_change_base (f g : Ranking m) (σ : Equiv.Perm (Fin m))
    (hσ : ∀ i, g (σ i) = f i) (π : Equiv.Perm (Fin m)) :
    rankOf g (σ * π) = rankOf f π := by
  funext p
  exact hσ (π p)

theorem maxRegret_change_base (f g : Ranking m) (σ : Equiv.Perm (Fin m))
    (hσ : ∀ i, g (σ i) = f i) (P : R → ℝ) (perm : R → Equiv.Perm (Fin m))
    (D : ℝ) (budgets : Finset ℕ) (hne : budgets.Nonempty) :
    maxRegret P g (fun x => σ * perm x) D budgets hne
      = maxRegret P f perm D budgets hne := by
  unfold maxRegret regret
  simp_rw [rankOf_change_base f g σ hσ]

/-- No menu-optimum shortcut: the constructed law lives on ALL permutations of g. -/
theorem actual_allPerm_witness_of_menu (f g : Ranking m) (σ : Equiv.Perm (Fin m))
    (hσ : ∀ i, g (σ i) = f i) (P : R → ℝ) (perm : R → Equiv.Perm (Fin m))
    (D η V : ℝ) (budgets : Finset ℕ) (hne : budgets.Nonempty)
    (hP : P ∈ FeasibleAt perm η) (hV : maxRegret P f perm D budgets hne = V) :
    ∃ Q ∈ FeasibleAt (id : Equiv.Perm (Fin m) → _) η,
      maxRegret Q g id D budgets hne = V := by
  refine ⟨pushLaw (fun x => σ * perm x) P,
    feasible_push _ _ _ (feasible_left_relabel P perm σ η hP),?_⟩
  rw [maxRegret_push, maxRegret_change_base f g σ hσ, hV]

#print axioms feasible_left_relabel
#print axioms rankOf_change_base
#print axioms actual_allPerm_witness_of_menu
end CIGAMF.P13.PaperCLawRelabel
