import «LeanD6NuisanceFreeDiscoveryV1»
import «LeanFiniteGaussianSumLawV1»

/-! The actual four-query contrast has N(label difference,4) law on its
canonical product space. Neither independence nor a response law is assumed. -/
namespace CIGAMF.P13.D6NuisanceFreeDiscoveryLaw
open scoped BigOperators
open Finset MeasureTheory ProbabilityTheory
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6GaussianQueryDominance CIGAMF.P13.D6NuisanceFreeDiscovery
open CIGAMF.P13.FiniteGaussianSumLaw
noncomputable section

lemma signed_sum_law {T : Type*} [Fintype T] [DecidableEq T]
    (m w : T → ℝ) (hw : ∀ t, (w t)^2=1) (s : Finset T) :
    HasLaw (fun x : T → ℝ => ∑ t ∈ s,w t*x t)
      (gaussianReal (∑ t ∈ s,w t*m t) (s.card:NNReal)) (law m) := by
  have heval (t : T) : HasLaw (fun x : T → ℝ => w t*x t)
      (gaussianReal (w t*m t) 1) (law m) := by
    have he : HasLaw (fun x : T → ℝ => x t) (gaussianReal (m t) 1) (law m) :=
      (measurePreserving_eval (fun t => gaussianReal (m t) 1) t).hasLaw
    have hv : NNReal.mk ((w t)^2) (sq_nonneg (w t))*1=1 := by
      apply Subtype.ext;simpa using hw t
    simpa only [hv] using gaussianReal_const_mul he (w t)
  have hind : iIndepFun (fun t (x : T → ℝ) => w t*x t) (law m) := by
    have hh : iIndepFun (fun t (x : T → ℝ) => x t) (law m) :=
      iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
    exact hh.comp (fun t y => w t*y) (fun t => by fun_prop)
  have hmeas (s : Finset T) : Measurable (fun x : T → ℝ => ∑ t ∈ s,w t*x t) :=
    Finset.measurable_fun_sum (f := fun t (x : T → ℝ) => w t*x t) s
      (fun t _ => measurable_const.mul (measurable_pi_apply t))
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨(hmeas _).aemeasurable,?_⟩
    simp [gaussianReal_zero_var]
  | @insert i s hi ih =>
    have hi' : IndepFun (fun x : T → ℝ => ∑ t ∈ s,w t*x t)
        (fun x => w i*x i) (law m) := by
      have he : (∑ t ∈ s,fun x : T → ℝ => w t*x t) = (fun x => ∑ t ∈ s,w t*x t) := by
        funext x;simp only [Finset.sum_apply]
      rw [← he]
      exact hind.indepFun_finsetSum_of_notMem (fun t => by fun_prop) hi
    have hadd := gaussianReal_add_gaussianReal_of_indepFun hi'.symm (heval i) ih
    refine ⟨(hmeas _).aemeasurable,?_⟩
    simpa [Finset.sum_insert,Finset.card_insert_of_notMem,hi,Nat.cast_add,Nat.cast_one,
      Pi.add_def,add_comm] using hadd

variable {n : ℕ}
def queries (a i k : I n) : Fin 4 → Measurement n :=
  ![.inl a,.inl i,.inr ({i,k},false),.inr ({a,k},false)]

def signs : Fin 4 → ℝ := ![1,-1,1,-1]

theorem actual_contrast_law (A : Finset (I n)) (j a i k : I n) (hj : j ∉ A)
    (ha : a ≠ j) (hi : i ≠ j) (hk : k ≠ j) (hak : a ≠ k) (hik : i ≠ k)
    (mu : ℝ) :
    HasLaw (fun x : Fin 4 → ℝ => ∑ t,signs t*x t)
      (gaussianReal (label A i-label A a) 4)
      (law (fun t => actualMean A j mu (queries a i k t))) := by
  have hs : ∀ t, (signs t)^2=1 := by intro t;fin_cases t <;> norm_num [signs]
  have hm : (∑ t,signs t*actualMean A j mu (queries a i k t)) = label A i-label A a := by
    simpa [Fin.sum_univ_succ,signs,queries,sub_eq_add_neg,add_assoc] using
      actual_contrast A j a i k hj ha hi hk hak hik mu
  simpa [hm] using signed_sum_law (fun t => actualMean A j mu (queries a i k t)) signs hs univ

#print axioms signed_sum_law
#print axioms actual_contrast_law
end
end CIGAMF.P13.D6NuisanceFreeDiscoveryLaw
