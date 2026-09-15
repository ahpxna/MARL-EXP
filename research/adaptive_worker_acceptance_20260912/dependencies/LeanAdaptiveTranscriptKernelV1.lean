import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Tactic

/-! Exact finite-horizon simulation in probability kernels. A state may retain
all past query labels, observations, and an independent policy seed. The
simulator is constructed without the unknown-parameter resource law. -/
namespace CIGAMF.P13.AdaptiveTranscriptKernel
open MeasureTheory ProbabilityTheory
noncomputable section

/-- Nested product of N observations, including a singleton at N=0. -/
@[reducible] def Samples (X : Type) : ℕ → Type
  | 0 => Unit
  | n+1 => Samples X n × X

instance samplesMeasurable (X : Type) [MeasurableSpace X] :
    (n : ℕ) → MeasurableSpace (Samples X n)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | n+1 => @Prod.instMeasurableSpace (Samples X n) X (samplesMeasurable X n) inferInstance

variable {X : Type} {H : Type*} [MeasurableSpace X] [MeasurableSpace H]

/-- N independent resource observations, as a kernel from a singleton. -/
def resource (P : Measure X) : (n : ℕ) → Kernel Unit (Samples X n)
  | 0 => Kernel.id
  | n+1 => resource P n ×ₖ Kernel.const Unit P

instance resourceMarkov (P : Measure X) [IsProbabilityMeasure P] (n : ℕ) :
    IsMarkovKernel (resource P n) := by
  induction n with
  | zero => exact inferInstanceAs (IsMarkovKernel (Kernel.id : Kernel Unit Unit))
  | succ n ih =>
    letI := ih
    change IsMarkovKernel (resource P n ×ₖ Kernel.const Unit P)
    infer_instance

/-- Real state/transcript distribution after N successive transition kernels. -/
def trajectory (initial : Kernel Unit H) (step : ℕ → Kernel H H) : ℕ → Kernel Unit H
  | 0 => initial
  | n+1 => step n ∘ₖ trajectory initial step n

/-- Parameter-free simulator: at each step use the previous simulated state
and one fresh resource observation. -/
def simulator (initial : Kernel Unit H) (sim : ℕ → Kernel (H × X) H) :
    (n : ℕ) → Kernel (Samples X n) H
  | 0 => initial
  | n+1 => sim n ∘ₖ (simulator initial sim n ∥ₖ Kernel.id)

instance simulatorMarkov (initial : Kernel Unit H) [IsMarkovKernel initial]
    (sim : ℕ → Kernel (H × X) H) [∀ n, IsMarkovKernel (sim n)] (n : ℕ) :
    IsMarkovKernel (simulator initial sim n) := by
  induction n with
  | zero => exact inferInstanceAs (IsMarkovKernel initial)
  | succ n ih =>
    letI := ih
    change IsMarkovKernel (sim n ∘ₖ (simulator initial sim n ∥ₖ Kernel.id))
    infer_instance

/-- One actual transition simulated from a fresh observation with law P. -/
def feed (P : Measure X) (sim : Kernel (H × X) H) : Kernel H H :=
  sim ∘ₖ (Kernel.id ×ₖ Kernel.const H P)

/-- Exact full-state law, not just the marginal distribution of each response. -/
theorem transcript_simulation (initial : Kernel Unit H) [IsMarkovKernel initial]
    (sim : ℕ → Kernel (H × X) H) [∀ n, IsMarkovKernel (sim n)]
    (P : Measure X) [IsProbabilityMeasure P] (step : ℕ → Kernel H H)
    (hstep : ∀ n, step n = feed P (sim n)) (N : ℕ) :
    simulator initial sim N ∘ₖ resource P N = trajectory initial step N := by
  induction N with
  | zero => exact Kernel.comp_id initial
  | succ N ih =>
    haveI : IsMarkovKernel (trajectory initial step N) := by
      rw [← ih]
      infer_instance
    simp only [simulator,resource,trajectory]
    rw [Kernel.comp_assoc,Kernel.parallelComp_comp_prod,Kernel.id_comp,ih]
    rw [hstep N]
    simp only [feed,Kernel.comp_assoc]
    rw [Kernel.prod_const_comp,Kernel.id_comp]

/-- The same simulator works simultaneously for every parameter. In particular
it is not allowed to change with the true parameter or the tested side. -/
theorem uniform_transcript_simulation {Θ : Type*}
    (initial : Kernel Unit H) [IsMarkovKernel initial]
    (sim : ℕ → Kernel (H × X) H) [∀ n, IsMarkovKernel (sim n)]
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)]
    (step : Θ → ℕ → Kernel H H)
    (hstep : ∀ θ n, step θ n = feed (P θ) (sim n)) (N : ℕ) :
    ∃ K : Kernel (Samples X N) H, IsMarkovKernel K ∧
      ∀ θ, K ∘ₖ resource (P θ) N = trajectory initial (step θ) N := by
  refine ⟨simulator initial sim N,inferInstance,?_⟩
  intro θ
  exact transcript_simulation initial sim (P θ) (step θ) (hstep θ) N

/-- A terminal randomized decision remains a garbling of the resource samples. -/
theorem terminal_simulation {D : Type*} [MeasurableSpace D]
    (initial : Kernel Unit H) [IsMarkovKernel initial]
    (sim : ℕ → Kernel (H × X) H) [∀ n, IsMarkovKernel (sim n)]
    (P : Measure X) [IsProbabilityMeasure P] (step : ℕ → Kernel H H)
    (hstep : ∀ n, step n = feed P (sim n)) (decision : Kernel H D) (N : ℕ) :
    (decision ∘ₖ simulator initial sim N) ∘ₖ resource P N =
      decision ∘ₖ trajectory initial step N := by
  rw [Kernel.comp_assoc,transcript_simulation initial sim P step hstep N]

#print axioms transcript_simulation
#print axioms uniform_transcript_simulation
#print axioms terminal_simulation
end
end CIGAMF.P13.AdaptiveTranscriptKernel
