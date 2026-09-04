import Mathlib
import «LeanD6FirstOrderInsufficiencyWitnessV1»

/-!
# D6-B7: full-singleton first-order insufficiency

This extension closes the presentation loophole in the original two-decision
witness.  A controller is now allowed to return *any* singleton retained set
over `Fin 3`.  The two worlds still have the identical complete first-order
product-response table, while their zero-regret singleton fibres are disjoint.
-/

namespace CIGAMF.P13.D6FirstOrderInsufficiencyWitness

open scoped BigOperators Matrix
open CIGAMF.V4.SupportGeometry
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.TypedCertificateCompletion

def alternative2 : Finset (Fin 3) := {2}

private theorem alternative2_sum (g : Fin 3 → ℝ) :
    alternative2.sum g = g 2 := by
  rw [show alternative2 = {2} from rfl, Finset.sum_singleton]

private theorem fin2_zero_or_one_v2 (u : Fin 2) : u = 0 ∨ u = 1 := by
  fin_cases u <;> simp

private theorem compressionLoss_eq_of_bounds_v2
    (F : (Fin 3 → Fin 2) → ℝ) (S : Finset (Fin 3)) (lo hi : ℝ)
    (hbound : ∀ x, lo ≤ F x -
        S.sum (fun j ↦ productResponse pointMass3 F j (x j)) ∧
      F x - S.sum (fun j ↦ productResponse pointMass3 F j (x j)) ≤ hi)
    (xmin xmax : Fin 3 → Fin 2)
    (hmin : F xmin - S.sum
      (fun j ↦ productResponse pointMass3 F j (xmin j)) = lo)
    (hmax : F xmax - S.sum
      (fun j ↦ productResponse pointMass3 F j (xmax j)) = hi) :
    productCompressionLoss F (productResponse pointMass3 F) S =
      (hi - lo) / 2 := by
  let residual : (Fin 3 → Fin 2) → ℝ := fun x ↦ F x -
    S.sum (fun j ↦ productResponse pointMass3 F j (x j))
  have hrmax : maxVal residual = hi := by
    apply le_antisymm
    · exact maxVal_le residual (fun x ↦ (hbound x).2)
    · simpa [residual, hmax] using le_maxVal residual xmax
  have hrmin : minVal residual = lo := by
    apply le_antisymm
    · simpa [residual, hmin] using minVal_le residual xmin
    · exact le_minVal residual (fun x ↦ (hbound x).1)
  simp [productCompressionLoss, residual, osc, hrmax, hrmin]

private theorem additive_alternative2_bounds (x : Fin 3 → Fin 2) :
    0 ≤ additiveWorld3 x - alternative2.sum
      (fun j ↦ productResponse pointMass3 additiveWorld3 j (x j)) ∧
    additiveWorld3 x - alternative2.sum
      (fun j ↦ productResponse pointMass3 additiveWorld3 j (x j)) ≤ 1 := by
  rw [alternative2_sum, additive_response]
  rcases fin2_zero_or_one_v2 (x 0) with h0 | h0 <;>
    simp [additiveWorld3, h0]

private theorem interaction_alternative2_bounds (x : Fin 3 → Fin 2) :
    0 ≤ interactionWorld3 x - alternative2.sum
      (fun j ↦ productResponse pointMass3 interactionWorld3 j (x j)) ∧
    interactionWorld3 x - alternative2.sum
      (fun j ↦ productResponse pointMass3 interactionWorld3 j (x j)) ≤ 1 := by
  rw [alternative2_sum, interaction_response]
  rcases fin2_zero_or_one_v2 (x 0) with h0 | h0 <;>
    rcases fin2_zero_or_one_v2 (x 1) with h1 | h1 <;>
    rcases fin2_zero_or_one_v2 (x 2) with h2 | h2 <;>
    simp [interactionWorld3, h0, h1, h2] <;> norm_num

theorem additive_alternative2_loss :
    productCompressionLoss additiveWorld3
      (productResponse pointMass3 additiveWorld3) alternative2 = 1 / 2 := by
  convert compressionLoss_eq_of_bounds_v2 additiveWorld3 alternative2 0 1
    additive_alternative2_bounds a000 a100 (by
      rw [alternative2_sum, additive_response]
      have h20 : (2 : Fin 3) ≠ 0 := by decide
      norm_num [a000, additiveWorld3, anchor3, h20]) (by
      rw [alternative2_sum, additive_response]
      have h20 : (2 : Fin 3) ≠ 0 := by decide
      norm_num [a100, additiveWorld3, anchor3, Function.update, h20]) using 1 <;> norm_num

theorem interaction_alternative2_loss :
    productCompressionLoss interactionWorld3
      (productResponse pointMass3 interactionWorld3) alternative2 = 1 / 2 := by
  convert compressionLoss_eq_of_bounds_v2 interactionWorld3 alternative2 0 1
    interaction_alternative2_bounds a000 a100 (by
      rw [alternative2_sum, interaction_response]
      have h20 : (2 : Fin 3) ≠ 0 := by decide
      norm_num [a000, interactionWorld3, anchor3, h20]) (by
      rw [alternative2_sum, interaction_response]
      have h20 : (2 : Fin 3) ≠ 0 := by decide
      norm_num [a100, interactionWorld3, anchor3, Function.update, h20]) using 1 <;> norm_num

theorem D6_B7_full_singleton_opposite_strict_ordering :
    productCompressionLoss additiveWorld3
        (productResponse pointMass3 additiveWorld3) selected0 <
      productCompressionLoss additiveWorld3
        (productResponse pointMass3 additiveWorld3) alternative1 ∧
    productCompressionLoss additiveWorld3
        (productResponse pointMass3 additiveWorld3) selected0 <
      productCompressionLoss additiveWorld3
        (productResponse pointMass3 additiveWorld3) alternative2 ∧
    productCompressionLoss interactionWorld3
        (productResponse pointMass3 interactionWorld3) alternative1 <
      productCompressionLoss interactionWorld3
        (productResponse pointMass3 interactionWorld3) selected0 ∧
    productCompressionLoss interactionWorld3
        (productResponse pointMass3 interactionWorld3) alternative2 <
      productCompressionLoss interactionWorld3
        (productResponse pointMass3 interactionWorld3) selected0 := by
  rw [additive_selected_loss, additive_alternative_loss,
    additive_alternative2_loss, interaction_selected_loss,
    interaction_alternative_loss, interaction_alternative2_loss]
  norm_num

abbrev SingletonDecisionSpace3 := {S : Finset (Fin 3) // S.card = 1}

def singletonDecision3 (i : Fin 3) : SingletonDecisionSpace3 :=
  ⟨{i}, by simp⟩

theorem singletonDecision3_complete (d : SingletonDecisionSpace3) :
    ∃ i : Fin 3, d.1 = (singletonDecision3 i).1 := by
  exact Finset.card_eq_one.mp d.2

@[simp] theorem singletonDecision3_zero : (singletonDecision3 0).1 = selected0 := rfl
@[simp] theorem singletonDecision3_one : (singletonDecision3 1).1 = alternative1 := rfl
@[simp] theorem singletonDecision3_two : (singletonDecision3 2).1 = alternative2 := rfl

noncomputable def fullSingletonRegret3
    (interaction : Bool) (decision : SingletonDecisionSpace3) : ℝ :=
  if interaction then
    productCompressionLoss interactionWorld3
        (productResponse pointMass3 interactionWorld3) decision.1 - (1 / 2)
  else
    productCompressionLoss additiveWorld3
        (productResponse pointMass3 additiveWorld3) decision.1

private theorem fullSingletonRegret3_at_zero (interaction : Bool) :
    fullSingletonRegret3 interaction (singletonDecision3 0) =
      if interaction then 1 / 2 else 0 := by
  cases interaction
  · change productCompressionLoss additiveWorld3
      (productResponse pointMass3 additiveWorld3) (singletonDecision3 0).1 = 0
    rw [singletonDecision3_zero, additive_selected_loss]
  · change productCompressionLoss interactionWorld3
        (productResponse pointMass3 interactionWorld3) (singletonDecision3 0).1 - 1 / 2 = 1 / 2
    rw [singletonDecision3_zero, interaction_selected_loss]
    norm_num

private theorem fullSingletonRegret3_at_one (interaction : Bool) :
    fullSingletonRegret3 interaction (singletonDecision3 1) =
      if interaction then 0 else 1 / 2 := by
  cases interaction
  · change productCompressionLoss additiveWorld3
      (productResponse pointMass3 additiveWorld3) (singletonDecision3 1).1 = 1 / 2
    rw [singletonDecision3_one, additive_alternative_loss]
  · change productCompressionLoss interactionWorld3
        (productResponse pointMass3 interactionWorld3) (singletonDecision3 1).1 - 1 / 2 = 0
    rw [singletonDecision3_one, interaction_alternative_loss]
    norm_num

private theorem fullSingletonRegret3_at_two (interaction : Bool) :
    fullSingletonRegret3 interaction (singletonDecision3 2) =
      if interaction then 0 else 1 / 2 := by
  cases interaction
  · change productCompressionLoss additiveWorld3
      (productResponse pointMass3 additiveWorld3) (singletonDecision3 2).1 = 1 / 2
    rw [singletonDecision3_two, additive_alternative2_loss]
  · change productCompressionLoss interactionWorld3
        (productResponse pointMass3 interactionWorld3) (singletonDecision3 2).1 - 1 / 2 = 0
    rw [singletonDecision3_two, interaction_alternative2_loss]
    norm_num

theorem D6_B7_full_singleton_zero_good_decisions_disjoint :
    Disjoint (Good fullSingletonRegret3 0 false)
      (Good fullSingletonRegret3 0 true) := by
  rw [Set.disjoint_left]
  intro d hAdditive hInteraction
  rcases singletonDecision3_complete d with ⟨i, hi⟩
  have hd : d = singletonDecision3 i := Subtype.ext hi
  subst d
  fin_cases i
  · have hA : fullSingletonRegret3 false (singletonDecision3 0) = 0 :=
      fullSingletonRegret3_at_zero false
    have hI : fullSingletonRegret3 true (singletonDecision3 0) = 1 / 2 :=
      fullSingletonRegret3_at_zero true
    change fullSingletonRegret3 false (singletonDecision3 0) ≤ 0 at hAdditive
    change fullSingletonRegret3 true (singletonDecision3 0) ≤ 0 at hInteraction
    rw [hA] at hAdditive
    rw [hI] at hInteraction
    norm_num at hInteraction
  · have hA : fullSingletonRegret3 false (singletonDecision3 1) = 1 / 2 := by
      simpa using fullSingletonRegret3_at_one false
    change fullSingletonRegret3 false (singletonDecision3 1) ≤ 0 at hAdditive
    rw [hA] at hAdditive
    norm_num at hAdditive
  · have hA : fullSingletonRegret3 false (singletonDecision3 2) = 1 / 2 := by
      simpa using fullSingletonRegret3_at_two false
    change fullSingletonRegret3 false (singletonDecision3 2) ≤ 0 at hAdditive
    rw [hA] at hAdditive
    norm_num at hAdditive

theorem D6_B7_full_singleton_response_only_not_universally_zero_regret :
    ¬ ∃ controller : FirstOrderObservation3 → SingletonDecisionSpace3,
      fullSingletonRegret3 false
          (controller (firstOrderObservation3 false)) ≤ 0 ∧
      fullSingletonRegret3 true
          (controller (firstOrderObservation3 true)) ≤ 0 := by
  exact TCC2_indistinguishability_impossibility
    firstOrderObservation3 fullSingletonRegret3 0 false true
    D6_B7_observation_worlds_equal
    D6_B7_full_singleton_zero_good_decisions_disjoint

/- The `Fin 3` encoding covers exactly the full set of singleton retained
decisions.  This form exposes the result to a controller API which returns an
ordinary `Finset`, while the cardinality invariant remains explicit. -/
theorem D6_B7_no_finset_singleton_controller_universally_zero_regret :
    ¬ ∃ (controller : FirstOrderObservation3 → Finset (Fin 3))
      (hcard : ∀ observation, (controller observation).card = 1),
      fullSingletonRegret3 false
          ⟨controller (firstOrderObservation3 false),
            hcard (firstOrderObservation3 false)⟩ ≤ 0 ∧
      fullSingletonRegret3 true
          ⟨controller (firstOrderObservation3 true),
            hcard (firstOrderObservation3 true)⟩ ≤ 0 := by
  rintro ⟨controller, hcard, hAdditive, hInteraction⟩
  let encoded : FirstOrderObservation3 → SingletonDecisionSpace3 :=
    fun observation ↦ ⟨controller observation, hcard observation⟩
  apply D6_B7_full_singleton_response_only_not_universally_zero_regret
  refine ⟨encoded, ?_, ?_⟩
  · exact hAdditive
  · exact hInteraction

end CIGAMF.P13.D6FirstOrderInsufficiencyWitness
