import Mathlib
import «LeanTypedObstructionActualSeparationsV3»

/-!
# Direct-product indispensability calculus for typed obstructions

The five concrete obstruction witnesses remain in their original modules.
This file supplies the next generic theorem: independent obstruction scopes
may be assembled into one product instance, and deleting any one unresolved
scope leaves two globally incompatible worlds indistinguishable.  No claim
about additive sample cost or computational complexity is made.
-/

namespace CIGAMF.P13.TypedObstructionIndispensabilityCalculus

open CIGAMF.P13.TypedCertificateCompletion
open CIGAMF.P13.TCCResponseScoreSeparation
open CIGAMF.P13.TCCReferenceSeparation
open CIGAMF.P13.SupportCompressionCriticalWitness
open CIGAMF.P13.SupportCriticalIdentification
open CIGAMF.P13.D6FirstOrderInsufficiencyWitness
open CIGAMF.P13.TCCQuerySeparation

/-- One exact local indistinguishability obstruction. -/
structure ObstructionComponent where
  Model : Type
  Evidence : Type
  Decision : Type
  observe : Model → Evidence
  good : Model → Decision → Prop
  left : Model
  right : Model
  sameEvidence : observe left = observe right
  disjointGood : Disjoint {d | good left d} {d | good right d}

variable {I : Type*} [DecidableEq I]

abbrev ProductWorld (family : I → ObstructionComponent) :=
  (i : I) → (family i).Model

abbrev ProductDecision (family : I → ObstructionComponent) :=
  (i : I) → (family i).Decision

/-- A global decision is good only when every independent component decision
is locally good. -/
def ProductGood (family : I → ObstructionComponent)
    (world : ProductWorld family) (decision : ProductDecision family) : Prop :=
  ∀ i, (family i).good (world i) (decision i)

/-- Evidence after one semantic scope `t` is unresolved: all other component
worlds are known, while scope `t` contributes only its reduced evidence. -/
@[ext] structure EvidenceWithout
    (family : I → ObstructionComponent) (t : I) where
  context : ∀ i, i ≠ t → (family i).Model
  omitted : (family t).Evidence

def observeWithout (family : I → ObstructionComponent) (t : I)
    (world : ProductWorld family) : EvidenceWithout family t where
  context := fun i _ ↦ world i
  omitted := (family t).observe (world t)

def leftWorld (family : I → ObstructionComponent)
    (base : ProductWorld family) (t : I) : ProductWorld family :=
  Function.update base t (family t).left

def rightWorld (family : I → ObstructionComponent)
    (base : ProductWorld family) (t : I) : ProductWorld family :=
  Function.update base t (family t).right

theorem observeWithout_left_eq_right
    (family : I → ObstructionComponent)
    (base : ProductWorld family) (t : I) :
    observeWithout family t (leftWorld family base t) =
      observeWithout family t (rightWorld family base t) := by
  apply EvidenceWithout.ext
  · funext i hi
    simp [observeWithout, leftWorld, rightWorld, hi]
  · simpa [observeWithout, leftWorld, rightWorld] using
      (family t).sameEvidence

theorem productGood_sets_disjoint_at_component
    (family : I → ObstructionComponent)
    (base : ProductWorld family) (t : I) :
    Disjoint
      {d : ProductDecision family | ProductGood family (leftWorld family base t) d}
      {d : ProductDecision family | ProductGood family (rightWorld family base t) d} := by
  rw [Set.disjoint_left]
  intro decision hLeft hRight
  have hLocalLeft : (family t).good (family t).left (decision t) := by
    simpa [ProductGood, leftWorld] using hLeft t
  have hLocalRight : (family t).good (family t).right (decision t) := by
    simpa [ProductGood, rightWorld] using hRight t
  exact Set.disjoint_left.1 (family t).disjointGood hLocalLeft hLocalRight

/-- Direct-product indispensability: in a family of independent exact
obstructions, a controller that sees only reduced evidence for component `t`
cannot be correct on both worlds that differ solely in that component. -/
theorem directProduct_component_indispensable
    (family : I → ObstructionComponent)
    (base : ProductWorld family) (t : I) :
    ¬ ∃ controller : EvidenceWithout family t → ProductDecision family,
      ProductGood family (leftWorld family base t)
        (controller (observeWithout family t (leftWorld family base t))) ∧
      ProductGood family (rightWorld family base t)
        (controller (observeWithout family t (rightWorld family base t))) := by
  rintro ⟨controller, hLeft, hRight⟩
  have hSame := observeWithout_left_eq_right family base t
  have hRight' :
      ProductGood family (rightWorld family base t)
        (controller (observeWithout family t (leftWorld family base t))) := by
    rw [hSame]
    exact hRight
  exact Set.disjoint_left.1
    (productGood_sets_disjoint_at_component family base t) hLeft hRight'

/-- Uniform form: every scope in the direct product is indispensable. -/
theorem every_directProduct_component_indispensable
    (family : I → ObstructionComponent)
    (base : ProductWorld family) :
    ∀ t : I,
      ¬ ∃ controller : EvidenceWithout family t → ProductDecision family,
        ProductGood family (leftWorld family base t)
          (controller (observeWithout family t (leftWorld family base t))) ∧
        ProductGood family (rightWorld family base t)
          (controller (observeWithout family t (rightWorld family base t))) := by
  intro t
  exact directProduct_component_indispensable family base t

/-! ## Exact five-type direct product -/

def responseObstruction : ObstructionComponent where
  Model := Bool
  Evidence := Unit
  Decision := Bool
  observe := observationWithoutResponse
  good := fun m d ↦ responseScoreRegret m d ≤ 0
  left := false
  right := true
  sameEvidence := rfl
  disjointGood := by
    change Disjoint (Good responseScoreRegret 0 false)
      (Good responseScoreRegret 0 true)
    exact RESPONSE_TCC_zero_good_decisions_disjoint

def referenceObstruction : ObstructionComponent where
  Model := Bool
  Evidence := ObservedKernelRows
  Decision := Bool
  observe := referenceObservation
  good := fun m d ↦ referenceRegret m d ≤ 0
  left := false
  right := true
  sameEvidence := RI_TCC_same_observed_reference_evidence
  disjointGood := by
    change Disjoint (Good referenceRegret 0 false)
      (Good referenceRegret 0 true)
    exact RI_TCC_zero_good_decisions_disjoint

def supportObstruction : ObstructionComponent where
  Model := Finset (Fin 3)
  Evidence := Finset (Fin 3)
  Decision := Bool
  observe := eraseCell2Observation
  good := fun omega d ↦ supportCompressionRegret omega d ≤ 0
  left := smallSupport
  right := largeSupport
  sameEvidence := by
    exact eraseCell2_blind_to_cell2 smallSupport largeSupport
      actual_support_worlds_differ_only_at_cell2
  disjointGood := by
    simpa [Good, Incompatible, SupportGood] using
      actual_support_zero_good_sets_disjoint

noncomputable def interactionObstruction : ObstructionComponent where
  Model := Bool
  Evidence := FirstOrderObservation3
  Decision := SingletonDecisionSpace3
  observe := firstOrderObservation3
  good := fun m d ↦ fullSingletonRegret3 m d ≤ 0
  left := false
  right := true
  sameEvidence := D6_B7_observation_worlds_equal
  disjointGood := by
    change Disjoint (Good fullSingletonRegret3 0 false)
      (Good fullSingletonRegret3 0 true)
    exact D6_B7_full_singleton_zero_good_decisions_disjoint

noncomputable def queryObstruction : ObstructionComponent where
  Model := Bool
  Evidence := CIGAMF.V7.QuerySufficiencyQuantitative.BoolPairwiseSummary
  Decision := ℝ
  observe := queryObservation
  good := fun m d ↦ interactionPredictionRegret m d ≤ 1
  left := false
  right := true
  sameEvidence := QUERY_TCC_same_response_evidence
  disjointGood := by
    change Disjoint (Good interactionPredictionRegret 1 false)
      (Good interactionPredictionRegret 1 true)
    exact QUERY_TCC_unit_good_predictions_disjoint

/-- One exact obstruction component for each scientific evidence type. -/
noncomputable def exactFiveObstruction : SemanticType → ObstructionComponent
  | .response => responseObstruction
  | .reference => referenceObstruction
  | .support => supportObstruction
  | .interaction => interactionObstruction
  | .query => queryObstruction

noncomputable def exactFiveBase : ProductWorld exactFiveObstruction :=
  fun t ↦ (exactFiveObstruction t).left

/-- The five concrete CIG obstructions coexist in one direct product.  For
every semantic type, replacing full access to that component by its reduced
evidence makes the two local worlds indistinguishable and globally
incompatible. -/
theorem exact_five_directProduct_each_type_indispensable :
    ∀ t : SemanticType,
      ¬ ∃ controller :
          EvidenceWithout exactFiveObstruction t →
            ProductDecision exactFiveObstruction,
        ProductGood exactFiveObstruction
            (leftWorld exactFiveObstruction exactFiveBase t)
            (controller (observeWithout exactFiveObstruction t
              (leftWorld exactFiveObstruction exactFiveBase t))) ∧
        ProductGood exactFiveObstruction
            (rightWorld exactFiveObstruction exactFiveBase t)
            (controller (observeWithout exactFiveObstruction t
              (rightWorld exactFiveObstruction exactFiveBase t))) := by
  exact every_directProduct_component_indispensable
    exactFiveObstruction exactFiveBase

end CIGAMF.P13.TypedObstructionIndispensabilityCalculus
