import Mathlib
import «LeanProductMixedDifferenceV4»
import «LeanTypedCertificateCompletionV1»

/-!
# Exact first-order insufficiency witness for D6 escalation

Two finite worlds have identical product-reference first-order responses under
the same normalized point-mass product reference, but their optimal retained
singleton decisions differ.  This justifies escalation to interaction evidence;
it is independent of the open universal PAEC-existence theorem.
-/

namespace CIGAMF.P13.D6FirstOrderInsufficiencyWitness

open scoped BigOperators Matrix
open CIGAMF.V4.SupportGeometry
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.TypedCertificateCompletion

def anchor3 : Fin 3 → Fin 2 := fun _ ↦ 0

def pointMass3 (_i : Fin 3) (u : Fin 2) : ℝ :=
  if u = 0 then 1 else 0

def additiveWorld3 (x : Fin 3 → Fin 2) : ℝ :=
  if x 0 = 1 then 1 else 0

def interactionWorld3 (x : Fin 3 → Fin 2) : ℝ :=
  if x 0 = 0 then
    if x 1 = 1 ∧ x 2 = 1 then 1 else 0
  else
    if x 1 = 0 ∧ x 2 = 0 then 1 else 0

def selected0 : Finset (Fin 3) := {0}
def alternative1 : Finset (Fin 3) := {1}

private theorem selected0_sum (g : Fin 3 → ℝ) :
    selected0.sum g = g 0 := by
  rw [show selected0 = {0} from rfl, Finset.sum_singleton]

private theorem alternative1_sum (g : Fin 3 → ℝ) :
    alternative1.sum g = g 1 := by
  rw [show alternative1 = {1} from rfl, Finset.sum_singleton]

private theorem fin2_zero_or_one (u : Fin 2) : u = 0 ∨ u = 1 := by
  fin_cases u <;> simp

theorem pointMass3_jointWeight (c : Fin 3 → Fin 2) :
    jointWeight pointMass3 c = if c = anchor3 then 1 else 0 := by
  classical
  by_cases h : c = anchor3
  · subst c
    norm_num [jointWeight, pointMass3, anchor3, Fin.prod_univ_three]
  · have hc : c 0 ≠ 0 ∨ c 1 ≠ 0 ∨ c 2 ≠ 0 := by
      by_contra hn
      push_neg at hn
      apply h
      funext i
      fin_cases i <;> simp [anchor3, hn.1, hn.2.1, hn.2.2]
    rcases hc with hc | hc | hc <;>
      simp [jointWeight, pointMass3, Fin.prod_univ_three, hc, h]

theorem pointMass3_expectation (G : (Fin 3 → Fin 2) → ℝ) :
    productExpectation pointMass3 G = G anchor3 := by
  classical
  unfold productExpectation
  simp_rw [pointMass3_jointWeight]
  rw [Finset.sum_eq_single anchor3]
  · simp
  · intro b hb hne
    simp [hne]
  · simp

theorem pointMass3_response (F : (Fin 3 → Fin 2) → ℝ)
    (i : Fin 3) (u : Fin 2) :
    productResponse pointMass3 F i u = F (Function.update anchor3 i u) := by
  unfold productResponse
  rw [pointMass3_expectation]

@[simp] theorem additive_response (i : Fin 3) (u : Fin 2) :
    productResponse pointMass3 additiveWorld3 i u =
      if i = 0 ∧ u = 1 then 1 else 0 := by
  rw [pointMass3_response]
  fin_cases i <;> fin_cases u <;>
    simp [anchor3, additiveWorld3, Function.update]

@[simp] theorem interaction_response (i : Fin 3) (u : Fin 2) :
    productResponse pointMass3 interactionWorld3 i u =
      if i = 0 ∧ u = 1 then 1 else 0 := by
  rw [pointMass3_response]
  fin_cases i <;> fin_cases u <;>
    simp [anchor3, interactionWorld3, Function.update]

theorem D6_B7_same_first_order_responses :
    ∀ i u,
      productResponse pointMass3 additiveWorld3 i u =
        productResponse pointMass3 interactionWorld3 i u := by
  intro i u
  rw [additive_response, interaction_response]

private theorem compressionLoss_eq_of_bounds
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

private theorem additive_selected_bounds (x : Fin 3 → Fin 2) :
    0 ≤ additiveWorld3 x - selected0.sum
      (fun j ↦ productResponse pointMass3 additiveWorld3 j (x j)) ∧
    additiveWorld3 x - selected0.sum
      (fun j ↦ productResponse pointMass3 additiveWorld3 j (x j)) ≤ 0 := by
  rw [selected0_sum, additive_response]
  rcases fin2_zero_or_one (x 0) with h0 | h0 <;>
    simp [additiveWorld3, h0]

private theorem additive_alternative_bounds (x : Fin 3 → Fin 2) :
    0 ≤ additiveWorld3 x - alternative1.sum
      (fun j ↦ productResponse pointMass3 additiveWorld3 j (x j)) ∧
    additiveWorld3 x - alternative1.sum
      (fun j ↦ productResponse pointMass3 additiveWorld3 j (x j)) ≤ 1 := by
  rw [alternative1_sum, additive_response]
  rcases fin2_zero_or_one (x 0) with h0 | h0 <;>
    simp [additiveWorld3, h0]

private theorem interaction_selected_bounds (x : Fin 3 → Fin 2) :
    -1 ≤ interactionWorld3 x - selected0.sum
      (fun j ↦ productResponse pointMass3 interactionWorld3 j (x j)) ∧
    interactionWorld3 x - selected0.sum
      (fun j ↦ productResponse pointMass3 interactionWorld3 j (x j)) ≤ 1 := by
  rw [selected0_sum, interaction_response]
  rcases fin2_zero_or_one (x 0) with h0 | h0 <;>
    rcases fin2_zero_or_one (x 1) with h1 | h1 <;>
    rcases fin2_zero_or_one (x 2) with h2 | h2 <;>
    simp [interactionWorld3, h0, h1, h2] <;> norm_num

private theorem interaction_alternative_bounds (x : Fin 3 → Fin 2) :
    0 ≤ interactionWorld3 x - alternative1.sum
      (fun j ↦ productResponse pointMass3 interactionWorld3 j (x j)) ∧
    interactionWorld3 x - alternative1.sum
      (fun j ↦ productResponse pointMass3 interactionWorld3 j (x j)) ≤ 1 := by
  rw [alternative1_sum, interaction_response]
  rcases fin2_zero_or_one (x 0) with h0 | h0 <;>
    rcases fin2_zero_or_one (x 1) with h1 | h1 <;>
    rcases fin2_zero_or_one (x 2) with h2 | h2 <;>
    simp [interactionWorld3, h0, h1, h2] <;> norm_num

def a000 : Fin 3 → Fin 2 := anchor3
def a100 : Fin 3 → Fin 2 := Function.update anchor3 0 1
def a110 : Fin 3 → Fin 2 := Function.update a100 1 1
def a011 : Fin 3 → Fin 2 :=
  Function.update (Function.update anchor3 1 1) 2 1

@[simp] private theorem a000_0 : a000 0 = 0 := by decide
@[simp] private theorem a000_1 : a000 1 = 0 := by decide
@[simp] private theorem a000_2 : a000 2 = 0 := by decide
@[simp] private theorem a100_0 : a100 0 = 1 := by decide
@[simp] private theorem a100_1 : a100 1 = 0 := by decide
@[simp] private theorem a100_2 : a100 2 = 0 := by decide
@[simp] private theorem a110_0 : a110 0 = 1 := by decide
@[simp] private theorem a110_1 : a110 1 = 1 := by decide
@[simp] private theorem a110_2 : a110 2 = 0 := by decide
@[simp] private theorem a011_0 : a011 0 = 0 := by decide
@[simp] private theorem a011_1 : a011 1 = 1 := by decide
@[simp] private theorem a011_2 : a011 2 = 1 := by decide

theorem additive_selected_loss :
    productCompressionLoss additiveWorld3
      (productResponse pointMass3 additiveWorld3) selected0 = 0 := by
  convert compressionLoss_eq_of_bounds additiveWorld3 selected0 0 0
    additive_selected_bounds a000 a000 (by
      rw [selected0_sum, additive_response]
      norm_num [a000, additiveWorld3, anchor3]) (by
      rw [selected0_sum, additive_response]
      norm_num [a000, additiveWorld3, anchor3]) using 1 <;> norm_num

theorem additive_alternative_loss :
    productCompressionLoss additiveWorld3
      (productResponse pointMass3 additiveWorld3) alternative1 = 1 / 2 := by
  convert compressionLoss_eq_of_bounds additiveWorld3 alternative1 0 1
    additive_alternative_bounds a000 a100 (by
      rw [alternative1_sum, additive_response]
      norm_num [a000, additiveWorld3, anchor3]) (by
      rw [alternative1_sum, additive_response]
      norm_num [a100, additiveWorld3, anchor3, Function.update]) using 1 <;> norm_num

theorem interaction_selected_loss :
    productCompressionLoss interactionWorld3
      (productResponse pointMass3 interactionWorld3) selected0 = 1 := by
  convert compressionLoss_eq_of_bounds interactionWorld3 selected0 (-1) 1
    interaction_selected_bounds a110 a011 (by
      rw [selected0_sum, interaction_response]
      norm_num [interactionWorld3]) (by
      rw [selected0_sum, interaction_response]
      norm_num [interactionWorld3]) using 1 <;> norm_num

theorem interaction_alternative_loss :
    productCompressionLoss interactionWorld3
      (productResponse pointMass3 interactionWorld3) alternative1 = 1 / 2 := by
  convert compressionLoss_eq_of_bounds interactionWorld3 alternative1 0 1
    interaction_alternative_bounds a000 a100 (by
      rw [alternative1_sum, interaction_response]
      norm_num [interactionWorld3]) (by
      rw [alternative1_sum, interaction_response]
      norm_num [interactionWorld3]) using 1 <;> norm_num

theorem D6_B7_same_first_order_different_compression_decision :
    productCompressionLoss additiveWorld3
        (productResponse pointMass3 additiveWorld3) selected0 <
      productCompressionLoss additiveWorld3
        (productResponse pointMass3 additiveWorld3) alternative1 ∧
    productCompressionLoss interactionWorld3
        (productResponse pointMass3 interactionWorld3) alternative1 <
      productCompressionLoss interactionWorld3
        (productResponse pointMass3 interactionWorld3) selected0 := by
  rw [additive_selected_loss, additive_alternative_loss,
    interaction_selected_loss, interaction_alternative_loss]
  norm_num

/-! ## Generic response-only impossibility wrapper

`false` is the additive world and `true` is the interaction world.  The
controller observes the complete first-order product-response table but must
choose between the two retained singleton decisions.  Regret is normalized by
the exact best decision in each world, so the zero-good decision fibres are
disjoint.
-/

abbrev FirstOrderObservation3 := (i : Fin 3) → Fin 2 → ℝ

noncomputable def firstOrderObservation3 (interaction : Bool) : FirstOrderObservation3 :=
  if interaction then
    productResponse pointMass3 interactionWorld3
  else
    productResponse pointMass3 additiveWorld3

def witnessDecision3 (chooseAlternative : Bool) : Finset (Fin 3) :=
  if chooseAlternative then alternative1 else selected0

noncomputable def witnessRegret3 (interaction chooseAlternative : Bool) : ℝ :=
  if interaction then
    productCompressionLoss interactionWorld3
        (productResponse pointMass3 interactionWorld3)
        (witnessDecision3 chooseAlternative) - (1 / 2)
  else
    productCompressionLoss additiveWorld3
        (productResponse pointMass3 additiveWorld3)
        (witnessDecision3 chooseAlternative)

theorem D6_B7_observation_worlds_equal :
    firstOrderObservation3 false = firstOrderObservation3 true := by
  funext i u
  exact D6_B7_same_first_order_responses i u

@[simp] theorem witnessRegret3_additive_selected :
    witnessRegret3 false false = 0 := by
  simp [witnessRegret3, witnessDecision3, additive_selected_loss]

@[simp] theorem witnessRegret3_additive_alternative :
    witnessRegret3 false true = 1 / 2 := by
  simp [witnessRegret3, witnessDecision3, additive_alternative_loss]

@[simp] theorem witnessRegret3_interaction_selected :
    witnessRegret3 true false = 1 / 2 := by
  norm_num [witnessRegret3, witnessDecision3, interaction_selected_loss]

@[simp] theorem witnessRegret3_interaction_alternative :
    witnessRegret3 true true = 0 := by
  simp [witnessRegret3, witnessDecision3, interaction_alternative_loss]

theorem D6_B7_zero_good_decisions_disjoint :
    Disjoint (Good witnessRegret3 0 false) (Good witnessRegret3 0 true) := by
  rw [Set.disjoint_left]
  intro decision hAdditive hInteraction
  cases decision <;> norm_num [Good, witnessRegret3, witnessDecision3,
    additive_selected_loss, additive_alternative_loss,
    interaction_selected_loss, interaction_alternative_loss] at *

theorem D6_B7_first_order_response_only_not_universally_exact :
    ¬ ∃ controller : FirstOrderObservation3 → Bool,
      witnessRegret3 false (controller (firstOrderObservation3 false)) ≤ 0 ∧
      witnessRegret3 true (controller (firstOrderObservation3 true)) ≤ 0 := by
  exact TCC2_indistinguishability_impossibility
    firstOrderObservation3 witnessRegret3 0 false true
    D6_B7_observation_worlds_equal D6_B7_zero_good_decisions_disjoint

end CIGAMF.P13.D6FirstOrderInsufficiencyWitness
