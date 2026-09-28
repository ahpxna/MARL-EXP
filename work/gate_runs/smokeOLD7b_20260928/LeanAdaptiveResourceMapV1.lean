import «LeanAdaptiveTranscriptKernelV1»

/-! Independent per-observation randomization commutes with finite products.
Used to remove the ancillary Gaussian noise from the D6 resource experiment. -/
namespace CIGAMF.P13.AdaptiveResourceMap
open MeasureTheory ProbabilityTheory
open CIGAMF.P13.AdaptiveTranscriptKernel
noncomputable section
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]

def mapSamples (κ : Kernel X Y) : (N : ℕ) → Kernel (Samples X N) (Samples Y N)
  | 0 => Kernel.id
  | N+1 => mapSamples κ N ∥ₖ κ

instance mapSamplesMarkov (κ : Kernel X Y) [IsMarkovKernel κ] (N : ℕ) :
    IsMarkovKernel (mapSamples κ N) := by
  induction N with
  | zero => exact inferInstanceAs (IsMarkovKernel (Kernel.id : Kernel Unit Unit))
  | succ N ih =>
    letI := ih
    change IsMarkovKernel (mapSamples κ N ∥ₖ κ)
    infer_instance

/-- Exact product-law identity for arbitrary independent randomization channels. -/
theorem resource_map (κ : Kernel X Y) [IsMarkovKernel κ]
    (P : Measure X) [IsProbabilityMeasure P] (N : ℕ) :
    mapSamples κ N ∘ₖ resource P N = resource (κ ∘ₘ P) N := by
  induction N with
  | zero => exact Kernel.id_comp _
  | succ N ih =>
    change (mapSamples κ N ∥ₖ κ) ∘ₖ (resource P N ×ₖ Kernel.const Unit P) =
      resource (κ ∘ₘ P) N ×ₖ Kernel.const Unit (κ ∘ₘ P)
    rw [Kernel.parallelComp_comp_prod,ih,Kernel.comp_const]

/-- Transfer any simulation based on augmented observations back to the
original observations; no unknown parameter enters the constructed kernel. -/
theorem remove_ancillary {Θ H : Type*} [MeasurableSpace H]
    (κ : Kernel X Y) [IsMarkovKernel κ] (P : Θ → Measure X)
    [∀ θ,IsProbabilityMeasure (P θ)] (N : ℕ)
    (K : Kernel (Samples Y N) H) [IsMarkovKernel K]
    (target : Θ → Kernel Unit H)
    (h : ∀ θ,K ∘ₖ resource (κ ∘ₘ P θ) N=target θ) :
    ∃ L : Kernel (Samples X N) H, IsMarkovKernel L ∧
      ∀ θ,L ∘ₖ resource (P θ) N=target θ := by
  refine ⟨K ∘ₖ mapSamples κ N,inferInstance,?_⟩
  intro θ
  rw [Kernel.comp_assoc,resource_map,h]

#print axioms resource_map
#print axioms remove_ancillary
end
end CIGAMF.P13.AdaptiveResourceMap
