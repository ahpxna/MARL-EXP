import «LeanMarlEstimatedRevisionV1»

/-!
Submission bridge for T1. Candidate legality is an additional conclusion, not a
consequence of a regret inequality. Uniform value error transfers a score-local
bound; the same lemma applies to actor drift. These are deterministic statements
on a specified error event, NOT a probability-of-coverage theorem.
Written during the 2026-09-27 audit; compilation delegated to the worker.
-/
namespace CIGAMF.P13.MarlRevisionAuditBridge
open Finset CIGAMF.P13.MarlSubsetFrontier CIGAMF.P13.MarlEstimatedRevision
variable {m : ℕ}

theorem deployed_regret_feasible
    (f fh : Finset (Fin m) → ℝ) (delta u eps nu zeta : ℝ) (w : Fin m → ℝ)
    (h : LocalInteraction f delta) (hu : ∀ i, |w i - gain f i| ≤ u)
    (P T : Finset (Fin m)) (k R : ℕ) (hP : P.card = k) (hT : T.card = k)
    (hTop : ∀ i ∈ P, ∀ j ∉ P, w j ≤ w i)
    (C : Finset (Finset (Fin m))) (Shat : Finset (Fin m)) (hShat : Shat ∈ C)
    (hLegal : ∀ S ∈ C, Reach P k R S)
    (hEval : ∀ S ∈ C, |fh S - f S| ≤ eps)
    (hSearch : ∀ S ∈ C, fh S ≤ fh Shat + nu)
    (hCover : ∀ S, Reach P k R S → ∃ S' ∈ C, f S ≤ f S' + zeta) :
    Reach P k R Shat ∧
      f T - f Shat ≤ 2 * (((P \ T).card - R : ℕ) : ℝ) * (delta + u)
        + 2 * eps + nu + zeta := by
  exact ⟨hLegal Shat hShat,
    deployed_regret f fh delta u eps nu zeta w h hu P T k R hP hT hTop
      C Shat hShat hEval hSearch hCover⟩

/-- Also a drift transfer when fh is the OLD actor value and f the NEW value. -/
theorem scoreLocal_transfer
    (f fh : Finset (Fin m) → ℝ) (w : Fin m → ℝ) (eta eps : ℝ)
    (h : ScoreLocal fh w eta) (he : ∀ S, |f S - fh S| ≤ eps) :
    ScoreLocal f w (eta + 2 * eps) := by
  intro A i hi
  have h1 := abs_le.mp (h A i hi)
  have h2 := abs_le.mp (he (insert i A))
  have h3 := abs_le.mp (he A)
  apply abs_le.mpr
  constructor <;> linarith

/-- A complete-table uniform error yields delta_U = delta_hat + 4 eps. -/
theorem localInteraction_transfer
    (f fh : Finset (Fin m) → ℝ) (delta eps : ℝ)
    (h : LocalInteraction fh delta) (he : ∀ S, |f S - fh S| ≤ eps) :
    LocalInteraction f (delta + 4 * eps) := by
  intro A i hi
  have h1 := abs_le.mp (h A i hi)
  have h2 := abs_le.mp (he (insert i A))
  have h3 := abs_le.mp (he A)
  have h4 := abs_le.mp (he {i})
  have h5 := abs_le.mp (he ∅)
  unfold gain at h1 ⊢
  apply abs_le.mpr
  constructor <;> linarith

#print axioms deployed_regret_feasible
#print axioms scoreLocal_transfer
#print axioms localInteraction_transfer
end CIGAMF.P13.MarlRevisionAuditBridge
