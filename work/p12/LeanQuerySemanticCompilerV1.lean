import Mathlib
import «LeanQuerySufficiencyV4»
import «LeanQuerySufficiencyQuantitativeV1»
import «LeanQueryRepresentationNecessityV1»

/-! # Typed semantic query compiler and fail-closed routing -/

namespace CIGAMF.P13.QuerySemanticCompiler

inductive Target
| response | signedEffect | removal | communication | information | causal
deriving DecidableEq

inductive Intervention
| forceAction | noop | randomize | deleteMessage | maskObservation | coalition
deriving DecidableEq

inductive Capability
| cloneRestore | interventionAuthority | fixedContinuation | noopAction
| randomization | messageMask | observationMask | policyLogits
| valueFunction | attentionTensor | coalitionIntervention
deriving DecidableEq

inductive QuerySemantics
| response | signedEffect | removal | communication | information | causal
deriving DecidableEq

inductive Method
| responseSpan | signedProjection | differenceReward | randomizedImportance
| interventionalATE | coalitionShapley | attention | messageDeletion | valueOfInformation
deriving DecidableEq

structure TypedQuery where
  target : Target
  intervention : Intervention
  horizon : ℕ
  candidateBudget : ℕ
  utilityId : ℕ
  oracleId : ℕ
deriving DecidableEq

structure RawQuery where
  target : Option Target
  intervention : Option Intervention
  horizon : Option ℕ
  candidateBudget : Option ℕ
  utilityId : Option ℕ
  oracleId : Option ℕ

def WellFormed (q : TypedQuery) : Prop :=
  0 < q.candidateBudget

def validate (r : RawQuery) : Option TypedQuery := do
  let target ← r.target
  let intervention ← r.intervention
  let horizon ← r.horizon
  let candidateBudget ← r.candidateBudget
  let utilityId ← r.utilityId
  let oracleId ← r.oracleId
  if 0 < candidateBudget then
    some ⟨target, intervention, horizon, candidateBudget, utilityId, oracleId⟩
  else none

theorem QUERY_A1_validator_soundness (r : RawQuery) (q : TypedQuery)
    (h : validate r = some q) : WellFormed q := by
  rcases htarget : r.target with _ | target
  · simp [validate, htarget] at h
  rcases hintervention : r.intervention with _ | intervention
  · simp [validate, htarget, hintervention] at h
  rcases hhorizon : r.horizon with _ | horizon
  · simp [validate, htarget, hintervention, hhorizon] at h
  rcases hbudget : r.candidateBudget with _ | candidateBudget
  · simp [validate, htarget, hintervention, hhorizon, hbudget] at h
  rcases hutility : r.utilityId with _ | utilityId
  · simp [validate, htarget, hintervention, hhorizon, hbudget, hutility] at h
  rcases horacle : r.oracleId with _ | oracleId
  · simp [validate, htarget, hintervention, hhorizon, hbudget, hutility,
      horacle] at h
  simp [validate, htarget, hintervention, hhorizon, hbudget, hutility,
    horacle] at h
  rcases h with ⟨hpos, rfl⟩
  exact hpos

def requires : Method → Finset Capability
| .responseSpan => {.cloneRestore, .interventionAuthority, .fixedContinuation}
| .signedProjection => {.policyLogits, .fixedContinuation}
| .differenceReward => {.noopAction, .cloneRestore}
| .randomizedImportance => {.randomization, .cloneRestore}
| .interventionalATE => {.interventionAuthority, .cloneRestore}
| .coalitionShapley => {.coalitionIntervention, .cloneRestore}
| .attention => {.attentionTensor}
| .messageDeletion => {.messageMask, .cloneRestore}
| .valueOfInformation => {.observationMask, .valueFunction, .cloneRestore}

def answers : Method → QuerySemantics
| .responseSpan => .response
| .signedProjection => .signedEffect
| .differenceReward => .removal
| .randomizedImportance => .causal
| .interventionalATE => .causal
| .coalitionShapley => .causal
| .attention => .information
| .messageDeletion => .communication
| .valueOfInformation => .information

def semanticsOfTarget : Target → QuerySemantics
| .response => .response
| .signedEffect => .signedEffect
| .removal => .removal
| .communication => .communication
| .information => .information
| .causal => .causal

def SemanticallyCompatible (m : Method) (q : TypedQuery) : Prop :=
  answers m = semanticsOfTarget q.target

structure EnvironmentCapabilities where
  supported : Finset Capability

def Admissible (m : Method) (q : TypedQuery)
    (env : EnvironmentCapabilities) : Prop :=
  SemanticallyCompatible m q ∧ requires m ⊆ env.supported

inductive RouteResult
| enabled | blockedNA
deriving DecidableEq

noncomputable def route (q : TypedQuery) (env : EnvironmentCapabilities)
    (m : Method) : RouteResult := by
  classical
  exact if Admissible m q env then .enabled else .blockedNA

theorem QUERY_A2_capability_routing_soundness
    (q : TypedQuery) (env : EnvironmentCapabilities) (m : Method)
    (h : route q env m = .enabled) :
    requires m ⊆ env.supported := by
  classical
  unfold route at h
  split at h
  · rename_i hadmissible
    exact hadmissible.2
  · contradiction

theorem QUERY_A3_semantic_routing_soundness
    (q : TypedQuery) (env : EnvironmentCapabilities) (m : Method)
    (h : route q env m = .enabled) :
    SemanticallyCompatible m q := by
  classical
  unfold route at h
  split at h
  · rename_i hadmissible
    exact hadmissible.1
  · contradiction

theorem QUERY_A4_fail_closed_missing_capability
    (q : TypedQuery) (env : EnvironmentCapabilities) (m : Method)
    (hmiss : ∃ c ∈ requires m, c ∉ env.supported) :
    route q env m ≠ .enabled := by
  intro henabled
  have hsub := QUERY_A2_capability_routing_soundness q env m henabled
  rcases hmiss with ⟨c, hc, hnot⟩
  exact hnot (hsub hc)

theorem QUERY_A4_fail_closed_semantic_mismatch
    (q : TypedQuery) (env : EnvironmentCapabilities) (m : Method)
    (hbad : ¬ SemanticallyCompatible m q) :
    route q env m ≠ .enabled := by
  intro h
  exact hbad (QUERY_A3_semantic_routing_soundness q env m h)

structure CompiledPlan where
  query : TypedQuery
  method : Method

def compile (q : TypedQuery) (m : Method) : CompiledPlan := ⟨q, m⟩

theorem QUERY_A5_no_silent_substitution (q : TypedQuery) (m : Method) :
    (compile q m).query = q := rfl

def Sufficient {M S T : Type*} (summary : M → S) (target : M → T)
    (models : Set M) : Prop :=
  ∀ m₁ ∈ models, ∀ m₂ ∈ models,
    summary m₁ = summary m₂ → target m₁ = target m₂

theorem QUERY_A6_sufficient_iff
    {M S T : Type*} (summary : M → S) (target : M → T)
    (models : Set M) :
    Sufficient summary target models ↔
      ∀ m₁ ∈ models, ∀ m₂ ∈ models,
        summary m₁ = summary m₂ → target m₁ = target m₂ := by
  rfl

theorem QUERY_A7_witness_blocks_exact_summary_predictor
    {M S T : Type*} (summary : M → S) (target : M → T)
    (m₁ m₂ : M)
    (hsame : summary m₁ = summary m₂)
    (hdiff : target m₁ ≠ target m₂) :
    ¬ ∃ psi : S → T, ∀ m, psi (summary m) = target m := by
  rintro ⟨psi, hpsi⟩
  apply hdiff
  rw [← hpsi m₁, ← hpsi m₂, hsame]

theorem QUERY_A8_quantitative_lower_bound
    {S : Type*} (s : S) (t₁ t₂ : ℝ) (psi : S → ℝ) :
    |t₁ - t₂| / 2 ≤ max |psi s - t₁| |psi s - t₂| := by
  have htri : |t₁ - t₂| ≤ |psi s - t₁| + |psi s - t₂| := by
    rw [show t₁ - t₂ = -(psi s - t₁) + (psi s - t₂) by ring]
    calc
      _ ≤ |-(psi s - t₁)| + |psi s - t₂| := abs_add_le _ _
      _ = _ := by rw [abs_neg]
  have h₁ := le_max_left |psi s - t₁| |psi s - t₂|
  have h₂ := le_max_right |psi s - t₁| |psi s - t₂|
  linarith

def Good {M D : Type*} (loss : M → D → ℝ) (opt : M → ℝ)
    (eps : ℝ) (m : M) : Set D :=
  {d | loss m d - opt m ≤ eps}

theorem QUERY_A9_empty_fibre_intersection_blocks_uniform_rule
    {M S D : Type*} (summary : M → S)
    (loss : M → D → ℝ) (opt : M → ℝ) (eps : ℝ) (s : S)
    (hempty : ⋂₀ (Set.range fun m : {m : M // summary m = s} ↦
      Good loss opt eps m.1) = ∅) :
    ¬ ∃ rule : S → D, ∀ m, summary m = s →
      loss m (rule s) - opt m ≤ eps := by
  rintro ⟨rule, hrule⟩
  have hmem : rule s ∈ ⋂₀ (Set.range fun m : {m : M // summary m = s} ↦
      Good loss opt eps m.1) := by
    rw [Set.mem_sInter]
    intro family hfamily
    rcases hfamily with ⟨m, rfl⟩
    exact hrule m.1 m.2
  rw [hempty] at hmem
  exact hmem

end CIGAMF.P13.QuerySemanticCompiler
