import Mathlib

/-! Exact finite semantic witnesses for Chain E. -/

namespace CIGAMF.V4.QuerySufficiency

def zeroWorld : Bool → Bool → ℝ := fun _ _ => 0

def interactionWorld : Bool → Bool → ℝ := fun a b =>
  if a = b then 1 else -1

noncomputable def responseFirst (F : Bool → Bool → ℝ) (a : Bool) : ℝ :=
  (F a false + F a true) / 2

noncomputable def responseSecond (F : Bool → Bool → ℝ) (b : Bool) : ℝ :=
  (F false b + F true b) / 2

def interactionQuery (F : Bool → Bool → ℝ) : ℝ :=
  F false false - F true false - F false true + F true true

theorem E1_same_pairwise_response :
    (∀ a, responseFirst zeroWorld a = responseFirst interactionWorld a) ∧
      (∀ b, responseSecond zeroWorld b = responseSecond interactionWorld b) := by
  constructor
  · intro a
    cases a <;> norm_num [responseFirst, zeroWorld, interactionWorld]
  · intro b
    cases b <;> norm_num [responseSecond, zeroWorld, interactionWorld]

theorem E2_same_response_different_information :
    interactionQuery zeroWorld ≠ interactionQuery interactionWorld := by
  norm_num [interactionQuery, zeroWorld, interactionWorld]

theorem E3_pairwise_response_not_sufficient_for_interaction :
    ∃ F G : Bool → Bool → ℝ,
      (∀ a, responseFirst F a = responseFirst G a) ∧
      (∀ b, responseSecond F b = responseSecond G b) ∧
      interactionQuery F ≠ interactionQuery G := by
  exact ⟨zeroWorld, interactionWorld, E1_same_pairwise_response.1,
    E1_same_pairwise_response.2, E2_same_response_different_information⟩

theorem E4_xor_synergy_witness :
    (∀ a, responseFirst interactionWorld a = 0) ∧
      (∀ b, responseSecond interactionWorld b = 0) ∧
      interactionQuery interactionWorld = 4 := by
  constructor
  · intro a
    cases a <;> norm_num [responseFirst, interactionWorld]
  constructor
  · intro b
    cases b <;> norm_num [responseSecond, interactionWorld]
  · norm_num [interactionQuery, interactionWorld]

end CIGAMF.V4.QuerySufficiency
