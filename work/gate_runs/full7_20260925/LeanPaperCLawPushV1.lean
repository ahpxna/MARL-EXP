import «LeanPaperCValueSetV1»

/-!
# Finite ranking menus as laws on ALL permutations

The pushforward preserves every marginal and every expected regret, not just an optimum
inside the construction's menu. In particular the all-permutation feasible set is inhabited
at every nonnegative band width. No band or objective identity is assumed in the transfer.
-/
namespace CIGAMF.P13.PaperCLawPush
open Finset
open CIGAMF.P13.PaperCRanking CIGAMF.P13.PaperCEndpoint
open CIGAMF.P13.PaperCValueSet
variable {R S : Type*} [Fintype R] [Fintype S] {m : ℕ}

open scoped Classical in
noncomputable def pushLaw (f : R → S) (P : R → ℝ) (y : S) : ℝ :=
  ∑ x, if f x = y then P x else 0

theorem pushLaw_expect (f : R → S) (P : R → ℝ) (v : S → ℝ) :
    ∑ y, pushLaw f P y * v y = ∑ x, P x * v (f x) := by
  classical
  simp only [pushLaw, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp only [ite_mul, zero_mul]
  simp

theorem pushLaw_nonneg (f : R → S) (P : R → ℝ) (hP : ∀ x, 0 ≤ P x) :
    ∀ y, 0 ≤ pushLaw f P y := by
  classical
  intro y
  exact Finset.sum_nonneg (fun x _ => by split_ifs <;> simp_all)

theorem pushLaw_sum (f : R → S) (P : R → ℝ) : ∑ y, pushLaw f P y = ∑ x, P x := by
  simpa using pushLaw_expect f P (fun _ => 1)

theorem feasible_push (perm : R → Equiv.Perm (Fin m)) (P : R → ℝ) (η : ℝ)
    (hP : P ∈ FeasibleAt perm η) :
    pushLaw perm P ∈ FeasibleAt (id : Equiv.Perm (Fin m) → _) η := by
  refine ⟨pushLaw_nonneg perm P hP.1, ?_, ?_⟩
  · rw [pushLaw_sum]; exact hP.2.1
  · intro k hk i
    simpa only [id_eq, pushLaw_expect] using hP.2.2 k hk i

theorem maxRegret_push (g : Ranking m) (perm : R → Equiv.Perm (Fin m))
    (P : R → ℝ) (D : ℝ) (budgets : Finset ℕ) (hne : budgets.Nonempty) :
    maxRegret (pushLaw perm P) g id D budgets hne = maxRegret P g perm D budgets hne := by
  unfold maxRegret
  congr 1
  funext k
  exact pushLaw_expect perm P (fun σ => regret g σ D k)

/-- The global optimization domain is nonempty, independently of any attainment claim. -/
theorem allPerm_feasible_nonempty (m : ℕ) [NeZero m] (η : ℝ) (hη : 0 ≤ η) :
    (FeasibleAt (id : Equiv.Perm (Fin m) → _) η).Nonempty := by
  have hzero := feasible_push (cyclicPerm m) (cyclicLaw m) 0 (feasible_zero_nonempty m)
  exact ⟨_, feasible_mono id 0 η (Nat.pos_of_ne_zero (NeZero.ne m)) hη hzero⟩

#print axioms pushLaw_expect
#print axioms feasible_push
#print axioms maxRegret_push
#print axioms allPerm_feasible_nonempty
end CIGAMF.P13.PaperCLawPush
