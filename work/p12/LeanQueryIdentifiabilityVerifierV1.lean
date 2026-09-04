import Mathlib
import «LeanQuerySemanticCompilerV1»

/-! # Finite identifiability verifier with exact insufficiency witnesses -/

namespace CIGAMF.P13.QueryIdentifiabilityVerifier

def Identifiable {M S T : Type*} (models : Finset M)
    (summary : M → S) (target : M → T) : Prop :=
  ∀ m₁ ∈ models, ∀ m₂ ∈ models,
    summary m₁ = summary m₂ → target m₁ = target m₂

def BadPair {M S T : Type*} (summary : M → S) (target : M → T)
    (pair : M × M) : Prop :=
  summary pair.1 = summary pair.2 ∧ target pair.1 ≠ target pair.2

def badPairs {M S T : Type*}
    [DecidableEq M] [DecidableEq S] [DecidableEq T]
  (models : Finset M) (summary : M → S) (target : M → T) :
    Finset (M × M) :=
  (models ×ˢ models).filter fun pair ↦
    decide (summary pair.1 = summary pair.2 ∧
      target pair.1 ≠ target pair.2) = true

def verifyIdentifiable {M S T : Type*}
    [DecidableEq M] [DecidableEq S] [DecidableEq T]
    (models : Finset M) (summary : M → S) (target : M → T) : Bool :=
  decide (badPairs models summary target = ∅)

theorem QUERY_B1_finite_verifier_correct
    {M S T : Type*} [DecidableEq M] [DecidableEq S] [DecidableEq T]
    (models : Finset M) (summary : M → S) (target : M → T) :
    verifyIdentifiable models summary target = true ↔
      Identifiable models summary target := by
  constructor
  · intro hVerify m₁ hm₁ m₂ hm₂ hSame
    by_contra hDifferent
    have hEmpty : badPairs models summary target = ∅ := by
      simpa [verifyIdentifiable] using hVerify
    have hMem : (m₁, m₂) ∈ badPairs models summary target := by
      simp [badPairs, hm₁, hm₂, hSame, hDifferent]
    rw [hEmpty] at hMem
    simpa using hMem
  · intro hIdentifiable
    have hEmpty : badPairs models summary target = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.1
      rintro ⟨pair, hPair⟩
      rcases pair with ⟨m₁, m₂⟩
      simp [badPairs] at hPair
      exact hPair.2.2
        (hIdentifiable m₁ hPair.1.1 m₂ hPair.1.2 hPair.2.1)
    simp [verifyIdentifiable, hEmpty]

noncomputable def findInsufficiencyWitness {M S T : Type*}
    [DecidableEq M] [DecidableEq S] [DecidableEq T]
    (models : Finset M) (summary : M → S) (target : M → T) :
    Option (M × M) :=
  if h : (badPairs models summary target).Nonempty then
    some (Classical.choose h)
  else none

theorem QUERY_B2_witness_sound
    {M S T : Type*} [DecidableEq M] [DecidableEq S] [DecidableEq T]
    (models : Finset M) (summary : M → S) (target : M → T)
    (m₁ m₂ : M)
    (hFound : findInsufficiencyWitness models summary target = some (m₁, m₂)) :
    m₁ ∈ models ∧ m₂ ∈ models ∧
      summary m₁ = summary m₂ ∧ target m₁ ≠ target m₂ := by
  unfold findInsufficiencyWitness at hFound
  split at hFound
  · rename_i hNonempty
    have hEq : Classical.choose hNonempty = (m₁, m₂) :=
      Option.some.inj hFound
    have hMem := Classical.choose_spec hNonempty
    rw [hEq] at hMem
    simp [badPairs] at hMem
    exact ⟨hMem.1.1, hMem.1.2, hMem.2.1, hMem.2.2⟩
  · simp at hFound

theorem no_witness_iff_identifiable
    {M S T : Type*} [DecidableEq M] [DecidableEq S] [DecidableEq T]
    (models : Finset M) (summary : M → S) (target : M → T) :
    findInsufficiencyWitness models summary target = none ↔
      Identifiable models summary target := by
  constructor
  · intro hNone m₁ hm₁ m₂ hm₂ hSame
    by_contra hDifferent
    have hPair : (m₁, m₂) ∈ badPairs models summary target := by
      simp [badPairs, hm₁, hm₂, hSame, hDifferent]
    have hNonempty : (badPairs models summary target).Nonempty :=
      ⟨(m₁, m₂), hPair⟩
    unfold findInsufficiencyWitness at hNone
    rw [dif_pos hNonempty] at hNone
    contradiction
  · intro hIdentifiable
    unfold findInsufficiencyWitness
    split
    · rename_i hNonempty
      rcases hNonempty with ⟨pair, hPair⟩
      rcases pair with ⟨m₁, m₂⟩
      simp [badPairs] at hPair
      exact (hPair.2.2
        (hIdentifiable m₁ hPair.1.1 m₂ hPair.1.2 hPair.2.1)).elim
    · rfl

inductive SemanticStatus (M Capability : Type*)
| identifiable
| insufficient (model₁ model₂ : M)
| blockedNA (missing : Capability)
deriving DecidableEq

noncomputable def assess {M S T Capability : Type*}
    [DecidableEq M] [DecidableEq S] [DecidableEq T]
    (models : Finset M) (summary : M → S) (target : M → T)
    (missing : Option Capability) : SemanticStatus M Capability :=
  match missing with
  | some capability => .blockedNA capability
  | none =>
      match findInsufficiencyWitness models summary target with
      | some pair => .insufficient pair.1 pair.2
      | none => .identifiable

theorem QUERY_B3_identifiable_status_sound
    {M S T Capability : Type*}
    [DecidableEq M] [DecidableEq S] [DecidableEq T]
    (models : Finset M) (summary : M → S) (target : M → T)
    (hStatus : assess models summary target (none : Option Capability) =
      .identifiable) :
    Identifiable models summary target := by
  cases hWitness : findInsufficiencyWitness models summary target with
  | none =>
      exact (no_witness_iff_identifiable models summary target).1 hWitness
  | some pair =>
      simp [assess, hWitness] at hStatus

theorem QUERY_B3_insufficient_status_sound
    {M S T Capability : Type*}
    [DecidableEq M] [DecidableEq S] [DecidableEq T]
    (models : Finset M) (summary : M → S) (target : M → T)
    (m₁ m₂ : M)
    (hStatus : assess models summary target (none : Option Capability) =
      .insufficient m₁ m₂) :
    m₁ ∈ models ∧ m₂ ∈ models ∧
      summary m₁ = summary m₂ ∧ target m₁ ≠ target m₂ := by
  cases hWitness : findInsufficiencyWitness models summary target with
  | none => simp [assess, hWitness] at hStatus
  | some pair =>
      rcases pair with ⟨w₁, w₂⟩
      simp [assess, hWitness] at hStatus
      rcases hStatus with ⟨rfl, rfl⟩
      exact QUERY_B2_witness_sound models summary target w₁ w₂ hWitness

theorem QUERY_B3_blocked_status_exact
    {M S T Capability : Type*}
    [DecidableEq M] [DecidableEq S] [DecidableEq T]
    (models : Finset M) (summary : M → S) (target : M → T)
    (capability : Capability) :
    assess models summary target (some capability) = .blockedNA capability :=
  rfl

theorem QUERY_B4_quantitative_witness
    {S : Type*} (summaryValue : S) (target₁ target₂ : ℝ)
    (predictor : S → ℝ) :
    |target₁ - target₂| / 2 ≤
      max |predictor summaryValue - target₁|
        |predictor summaryValue - target₂| :=
  CIGAMF.P13.QuerySemanticCompiler.QUERY_A8_quantitative_lower_bound
    summaryValue target₁ target₂ predictor

end CIGAMF.P13.QueryIdentifiabilityVerifier
