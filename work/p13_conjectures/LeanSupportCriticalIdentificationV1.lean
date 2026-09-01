import Mathlib
import «LeanTypedCertificateCompletionV1»

/-! # Decision-critical joint-support identification -/

namespace CIGAMF.P13.SupportCriticalIdentification

open scoped symmDiff BigOperators

variable {A D : Type*} [Fintype A] [DecidableEq A]

def SupportGood (regret : Finset A → D → ℝ) (eps : ℝ)
    (omega : Finset A) : Set D :=
  {decision | regret omega decision ≤ eps}

def Incompatible (regret : Finset A → D → ℝ) (eps : ℝ)
    (omega₁ omega₂ : Finset A) : Prop :=
  Disjoint (SupportGood regret eps omega₁) (SupportGood regret eps omega₂)

def CriticalCell (regret : Finset A → D → ℝ) (eps : ℝ) (a : A) : Prop :=
  ∃ omega₁ omega₂ : Finset A,
    omega₁ ∆ omega₂ ⊆ {a} ∧ Incompatible regret eps omega₁ omega₂

def CannotDistinguishCell {S : Type*}
    (observation : Finset A → S) (a : A) : Prop :=
  ∀ omega₁ omega₂ : Finset A,
    omega₁ ∆ omega₂ ⊆ {a} → observation omega₁ = observation omega₂

theorem SUP_B1_critical_cell_necessity
    {S : Type*} (regret : Finset A → D → ℝ) (eps : ℝ)
    (observation : Finset A → S) (a : A)
    (hCritical : CriticalCell regret eps a)
    (hBlind : CannotDistinguishCell observation a) :
    ¬ ∃ controller : S → D,
      ∀ omega : Finset A,
        regret omega (controller (observation omega)) ≤ eps := by
  rcases hCritical with ⟨omega₁, omega₂, hDiff, hIncompatible⟩
  rintro ⟨controller, hController⟩
  have hSame := hBlind omega₁ omega₂ hDiff
  exact CIGAMF.P13.TypedCertificateCompletion.TCC2_indistinguishability_impossibility
    observation regret eps omega₁ omega₂ hSame hIncompatible
    ⟨controller, hController omega₁, hController omega₂⟩

def Distinguishes (a : A) (omega₁ omega₂ : Finset A) : Prop :=
  (a ∈ omega₁ ∧ a ∉ omega₂) ∨ (a ∈ omega₂ ∧ a ∉ omega₁)

def Separates (regret : Finset A → D → ℝ) (eps : ℝ)
    (queries : Finset A) : Prop :=
  ∀ omega₁ omega₂ : Finset A,
    Incompatible regret eps omega₁ omega₂ →
      ∃ a ∈ queries, Distinguishes a omega₁ omega₂

def QueryObservation (queries omega : Finset A) : A → Bool :=
  fun a ↦ if a ∈ queries then decide (a ∈ omega) else false

theorem queryObservation_eq_of_no_distinguishing_query
    (queries omega₁ omega₂ : Finset A)
    (hNone : ¬ ∃ a ∈ queries, Distinguishes a omega₁ omega₂) :
    QueryObservation queries omega₁ = QueryObservation queries omega₂ := by
  funext a
  by_cases ha : a ∈ queries
  · have hiff : a ∈ omega₁ ↔ a ∈ omega₂ := by
      constructor
      · intro h₁
        by_contra h₂
        exact hNone ⟨a, ha, Or.inl ⟨h₁, h₂⟩⟩
      · intro h₂
        by_contra h₁
        exact hNone ⟨a, ha, Or.inr ⟨h₂, h₁⟩⟩
    simp [QueryObservation, ha, decide_eq_decide, hiff]
  · simp [QueryObservation, ha]

theorem SUP_B2_universal_query_set_must_separate
    (regret : Finset A → D → ℝ) (eps : ℝ) (queries : Finset A)
    (hUniversal : ∃ controller : (A → Bool) → D,
      ∀ omega : Finset A,
        regret omega (controller (QueryObservation queries omega)) ≤ eps) :
    Separates regret eps queries := by
  rcases hUniversal with ⟨controller, hController⟩
  intro omega₁ omega₂ hIncompatible
  by_contra hNoQuery
  have hSame := queryObservation_eq_of_no_distinguishing_query
    queries omega₁ omega₂ hNoQuery
  have h₁ : controller (QueryObservation queries omega₁) ∈
      SupportGood regret eps omega₁ := hController omega₁
  have h₂ : controller (QueryObservation queries omega₁) ∈
      SupportGood regret eps omega₂ := by
    change regret omega₂ (controller (QueryObservation queries omega₁)) ≤ eps
    rw [hSame]
    exact hController omega₂
  exact Set.disjoint_left.1 hIncompatible h₁ h₂

theorem SUP_B3_minimum_support_evidence_exists
    (regret : Finset A → D → ℝ) (eps : ℝ)
    (hExists : ∃ queries : Finset A, Separates regret eps queries) :
    ∃ optimal : Finset A,
      Separates regret eps optimal ∧
      ∀ queries : Finset A, Separates regret eps queries →
        optimal.card ≤ queries.card := by
  classical
  let feasible := Finset.univ.powerset.filter
    (fun queries ↦ Separates regret eps queries)
  have hFeasible : feasible.Nonempty := by
    rcases hExists with ⟨queries, hQueries⟩
    refine ⟨queries, ?_⟩
    simp [feasible, hQueries]
  rcases feasible.exists_min_image Finset.card hFeasible with
    ⟨optimal, hOptimal, hMinimum⟩
  refine ⟨optimal, (Finset.mem_filter.1 hOptimal).2, ?_⟩
  intro queries hQueries
  exact hMinimum queries (by simp [feasible, hQueries])

theorem positive_update_preserves_support_bracket
    (omegaMinus omega omegaPlus : Finset A) (a : A)
    (hInner : omegaMinus ⊆ omega) (hOuter : omega ⊆ omegaPlus)
    (hPositive : a ∈ omega) :
    insert a omegaMinus ⊆ omega ∧ omega ⊆ omegaPlus := by
  constructor
  · intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact hPositive
    · exact hInner hx
  · exact hOuter

theorem negative_update_preserves_support_bracket
    (omegaMinus omega omegaPlus : Finset A) (a : A)
    (hInner : omegaMinus ⊆ omega) (hOuter : omega ⊆ omegaPlus)
    (hNegative : a ∉ omega) :
    omegaMinus ⊆ omega ∧ omega ⊆ omegaPlus.erase a := by
  constructor
  · exact hInner
  · intro x hx
    exact Finset.mem_erase.2 ⟨by rintro rfl; exact hNegative hx, hOuter hx⟩

end CIGAMF.P13.SupportCriticalIdentification
