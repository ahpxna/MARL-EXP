import «LeanD6BlindPhaseBlocksV1»
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Basic

/-! Sum law for the canonical product of independent unit Gaussians with
possibly different means. No path-law or independence premise is supplied. -/
namespace CIGAMF.P13.FiniteGaussianSumLaw
open scoped BigOperators
open Finset MeasureTheory ProbabilityTheory
noncomputable section
variable {T : Type*} [Fintype T] [DecidableEq T]

def law (m : T → ℝ) : Measure (T → ℝ) := Measure.pi (fun t => gaussianReal (m t) 1)

instance law_probability (m : T → ℝ) : IsProbabilityMeasure (law m) := by
  unfold law; infer_instance

theorem sum_finset_law (m : T → ℝ) (s : Finset T) :
    HasLaw (fun x : T → ℝ => ∑ t ∈ s,x t)
      (gaussianReal (∑ t ∈ s,m t) (s.card:NNReal)) (law m) := by
  have heval (t : T) : HasLaw (fun x : T → ℝ => x t) (gaussianReal (m t) 1) (law m) :=
    (measurePreserving_eval (fun t => gaussianReal (m t) 1) t).hasLaw
  have hind : iIndepFun (fun t (x : T → ℝ) => x t) (law m) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by fun_prop, ?_⟩
    simp [gaussianReal_zero_var]
  | @insert i s hi ih =>
    have hi' : IndepFun (fun x : T → ℝ => ∑ t ∈ s,x t) (fun x => x i) (law m) := by
      have he : (∑ t ∈ s, (fun x : T → ℝ => x t)) = (fun x => ∑ t ∈ s, x t) := by
        funext x; simp only [Finset.sum_apply]
      rw [← he]
      exact hind.indepFun_finsetSum_of_notMem (fun t => by fun_prop) hi
    have hadd := gaussianReal_add_gaussianReal_of_indepFun hi'.symm (heval i) ih
    refine ⟨by fun_prop, ?_⟩
    simpa [Finset.sum_insert,Finset.card_insert_of_notMem,hi,Nat.cast_add,Nat.cast_one,
      Pi.add_def,add_comm] using hadd

theorem sum_law (m : T → ℝ) :
    HasLaw (fun x : T → ℝ => ∑ t,x t)
      (gaussianReal (∑ t,m t) (Fintype.card T:NNReal)) (law m) := by
  simpa using sum_finset_law m univ

#print axioms sum_finset_law
#print axioms sum_law
end
end CIGAMF.P13.FiniteGaussianSumLaw
