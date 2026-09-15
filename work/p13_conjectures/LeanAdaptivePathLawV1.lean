import «LeanAdaptiveTranscriptKernelV1»
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.HasLaw

/-! A single infinite path probability space for the actual finite-step kernel
recursion. The finite-horizon marginals are proved, not supplied as premises. -/
namespace CIGAMF.P13.AdaptivePathLaw
open MeasureTheory ProbabilityTheory Finset Function Preorder
open CIGAMF.P13.AdaptiveTranscriptKernel
noncomputable section
variable {H : Type*} [MeasurableSpace H]

def historyStep (step : ℕ → Kernel H H) (t : ℕ) : Kernel (Finset.Iic t → H) H :=
  step t ∘ₖ Kernel.deterministic (fun h => h ⟨t,Finset.mem_Iic.mpr le_rfl⟩) (by fun_prop)

instance historyStepMarkov (step : ℕ → Kernel H H) [∀ t,IsMarkovKernel (step t)] (t : ℕ) :
    IsMarkovKernel (historyStep step t) := by unfold historyStep; infer_instance

def path (initial : Measure H) (step : ℕ → Kernel H H) [∀ t,IsMarkovKernel (step t)] :
    Measure (ℕ → H) := Kernel.trajMeasure initial (historyStep step)

instance pathProbability (initial : Measure H) [IsProbabilityMeasure initial]
    (step : ℕ → Kernel H H) [∀ t,IsMarkovKernel (step t)] : IsProbabilityMeasure (path initial step) := by
  unfold path
  infer_instance

lemma path_initial (initial : Measure H) (step : ℕ → Kernel H H)
    [∀ t,IsMarkovKernel (step t)] : (path initial step).map (fun h => h 0)=initial := by
  have hfun : (fun h : ℕ → H => h 0) =
      (fun h : Finset.Iic 0 → H => h ⟨0,Finset.mem_Iic.mpr le_rfl⟩) ∘ frestrictLe 0 := rfl
  rw [path,Kernel.trajMeasure,Measure.map_comp _ _ (measurable_pi_apply _),hfun,
    Kernel.map_comp_right _ (measurable_frestrictLe 0) (measurable_pi_apply _),Kernel.traj_map_frestrictLe,
    Kernel.partialTraj_self]
  rw [Kernel.id_map (measurable_pi_apply _),Measure.deterministic_comp_eq_map]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have he : ((fun h : Finset.Iic 0 → H => h ⟨0,Finset.mem_Iic.mpr le_rfl⟩) ∘
      (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => H)).symm) = id := by
    funext h
    simp [MeasurableEquiv.piUnique,Equiv.piUnique]
  rw [he,Measure.map_id]

lemma path_step (initial : Measure H) [IsProbabilityMeasure initial]
    (step : ℕ → Kernel H H) [∀ t,IsMarkovKernel (step t)] (N : ℕ) :
    (path initial step).map (fun h => h (N+1))=
      step N ∘ₘ (path initial step).map (fun h => h N) := by
  have he := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ => H) (μ₀ := initial) (κ := historyStep step) (a := N)
  have hs := congrArg (fun P => Measure.map Prod.snd P) he
  change ((path initial step).map (frestrictLe N) ⊗ₘ historyStep step N).snd = _ at hs
  rw [Measure.snd_compProd,Measure.map_map (by fun_prop) (by fun_prop)] at hs
  change historyStep step N ∘ₘ (path initial step).map (frestrictLe N) =
    (path initial step).map (fun h => h (N+1)) at hs
  rw [← hs,historyStep,← Measure.comp_assoc,Measure.deterministic_comp_eq_map]
  have hm := Measure.map_map (μ := path initial step)
    (measurable_pi_apply (⟨N,Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic N))
    (measurable_frestrictLe N)
  rw [hm]
  rfl

/-- Every finite transcript state distribution is the marginal of one actual
infinite path measure, including a randomized initial state. -/
theorem actual_path_marginals (initial : Kernel Unit H) [IsMarkovKernel initial]
    (step : ℕ → Kernel H H) [∀ t,IsMarkovKernel (step t)] (N : ℕ) :
    HasLaw (fun h : ℕ → H => h N) (trajectory initial step N ()) (path (initial ()) step) := by
  refine ⟨(measurable_pi_apply N).aemeasurable,?_⟩
  induction N with
  | zero => exact path_initial (initial ()) step
  | succ N ih =>
    rw [path_step,ih]
    rfl

#print axioms path_initial
#print axioms path_step
#print axioms actual_path_marginals
end
end CIGAMF.P13.AdaptivePathLaw
