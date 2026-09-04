import Mathlib

/-!
# Typed heterogeneous certificate completion

This is deterministic infrastructure.  Evidence can discharge an obligation
only through an explicitly typed discharge relation; the file does not attach
probabilistic coverage or acquisition-efficiency claims to that relation.
-/

namespace CIGAMF.P13.TypedCertificateCompletion

open scoped BigOperators

inductive SemanticType
| response | reference | support | interaction | query
deriving DecidableEq, Repr

def Compatible (evidence obligation : SemanticType) : Prop :=
  evidence = obligation

def TypedDischarges {E O : Type*}
    (evidenceType : E → SemanticType) (obligationType : O → SemanticType)
    (discharge : E → O → Prop) (e : E) (o : O) : Prop :=
  Compatible (evidenceType e) (obligationType o) ∧ discharge e o

theorem TCC0_discharge_type_safety {E O : Type*}
    (evidenceType : E → SemanticType) (obligationType : O → SemanticType)
    (discharge : E → O → Prop) (e : E) (o : O)
    (h : TypedDischarges evidenceType obligationType discharge e o) :
    Compatible (evidenceType e) (obligationType o) :=
  h.1

def Complete {E O : Type*} [DecidableEq E]
    (required : Finset O) (chosen : Finset E)
    (discharges : E → O → Prop) : Prop :=
  ∀ o ∈ required, ∃ e ∈ chosen, discharges e o

def ValidEvidence {E : Type*} (chosen : Finset E) (valid : E → Prop) : Prop :=
  ∀ e ∈ chosen, valid e

/- A scientific certificate contract says exactly which obligations imply its
downstream regret guarantee.  Completion supplies those obligations; it does
not silently add a new inequality. -/
structure CertificateContract (D O : Type*) where
  selected : D
  epsilon : ℝ
  regret : D → ℝ
  required : Finset O
  obligationHolds : O → Prop
  sound : (∀ o ∈ required, obligationHolds o) → regret selected ≤ epsilon

theorem TCC1_certificate_completion_safety
    {D O E : Type*} [DecidableEq E]
    (contract : CertificateContract D O)
    (chosen : Finset E) (valid : E → Prop) (discharges : E → O → Prop)
    (hValid : ValidEvidence chosen valid)
    (hComplete : Complete contract.required chosen discharges)
    (hLegitimate : ∀ e o, discharges e o → valid e → contract.obligationHolds o) :
    contract.regret contract.selected ≤ contract.epsilon := by
  apply contract.sound
  intro o ho
  rcases hComplete o ho with ⟨e, he, hdischarge⟩
  exact hLegitimate e o hdischarge (hValid e he)

def Good {M D : Type*} (regret : M → D → ℝ) (eps : ℝ) (m : M) : Set D :=
  {d | regret m d ≤ eps}

/- Umbrella impossibility theorem: identical evidence plus disjoint good-decision
sets rules out every deterministic evidence-only controller. -/
theorem TCC2_indistinguishability_impossibility
    {M S D : Type*} (observation : M → S) (regret : M → D → ℝ)
    (eps : ℝ) (m₁ m₂ : M)
    (hSame : observation m₁ = observation m₂)
    (hDisjoint : Disjoint (Good regret eps m₁) (Good regret eps m₂)) :
    ¬ ∃ controller : S → D,
      regret m₁ (controller (observation m₁)) ≤ eps ∧
      regret m₂ (controller (observation m₂)) ≤ eps := by
  rintro ⟨controller, h₁, h₂⟩
  have hmem₁ : controller (observation m₁) ∈ Good regret eps m₁ := h₁
  have hmem₂ : controller (observation m₁) ∈ Good regret eps m₂ := by
    change regret m₂ (controller (observation m₁)) ≤ eps
    rw [hSame]
    exact h₂
  exact Set.disjoint_left.1 hDisjoint hmem₁ hmem₂

def EvidenceCost {E : Type*} (cost : E → ℝ) (chosen : Finset E) : ℝ :=
  ∑ e ∈ chosen, cost e

/- Finite static completion has a minimum-cost solution whenever the full
catalogue is complete.  This is the exact weighted set-cover object, without
claiming an algorithmic complexity class. -/
theorem TCC3_minimum_cost_static_completion
    {E O : Type*} [DecidableEq E] [DecidableEq O]
    (catalogue : Finset E) (required : Finset O)
    (discharges : E → O → Prop) [DecidableRel discharges]
    (cost : E → ℝ)
    (hCatalogue : Complete required catalogue discharges) :
    ∃ chosen : Finset E,
      chosen ⊆ catalogue ∧ Complete required chosen discharges ∧
      ∀ alternative : Finset E,
        alternative ⊆ catalogue → Complete required alternative discharges →
          EvidenceCost cost chosen ≤ EvidenceCost cost alternative := by
  classical
  let feasible := catalogue.powerset.filter
    (fun chosen ↦ Complete required chosen discharges)
  have hFeasible : feasible.Nonempty := by
    refine ⟨catalogue, ?_⟩
    simp [feasible, hCatalogue]
  rcases feasible.exists_min_image (EvidenceCost cost) hFeasible with
    ⟨chosen, hChosen, hMinimum⟩
  refine ⟨chosen, ?_, ?_, ?_⟩
  · exact Finset.mem_powerset.1 (Finset.mem_filter.1 hChosen).1
  · exact Finset.mem_filter.1 hChosen |>.2
  · intro alternative hsub hcomplete
    exact hMinimum alternative (by
      simp [feasible, hsub, hcomplete])

theorem TCC3_minimum_completion_is_safe
    {D O E : Type*} [DecidableEq E]
    (contract : CertificateContract D O)
    (chosen : Finset E) (valid : E → Prop) (discharges : E → O → Prop)
    (hValid : ValidEvidence chosen valid)
    (hComplete : Complete contract.required chosen discharges)
    (hLegitimate : ∀ e o, discharges e o → valid e → contract.obligationHolds o) :
    contract.regret contract.selected ≤ contract.epsilon :=
  TCC1_certificate_completion_safety contract chosen valid discharges
    hValid hComplete hLegitimate

inductive RuntimeResult (D Capability : Type*)
| certified (decision : D) (epsilon : ℝ)
| moreEvidence
| blockedNA (missing : Capability)

theorem certified_result_sound
    {D Capability : Type*} (regret : D → ℝ)
    (run : RuntimeResult D Capability) (decision : D) (eps : ℝ)
    (hRun : run = .certified decision eps)
    (hCertificate : run = .certified decision eps → regret decision ≤ eps) :
    regret decision ≤ eps :=
  hCertificate hRun

end CIGAMF.P13.TypedCertificateCompletion
