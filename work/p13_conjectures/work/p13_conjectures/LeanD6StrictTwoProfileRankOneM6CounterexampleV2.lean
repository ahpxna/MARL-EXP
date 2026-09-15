import Mathlib
import «LeanD6ContrastRankPhaseDefinitionsV2»
import «LeanD6InteractionContrastAnchorInvarianceV1»
import «LeanD6InteractionContrastProfileReductionV1»
import «LeanD6PolyhedralActiveCellV1»
import «LeanD6ResidualCentering»

/-!
# A small exact strict two-profile / rank-one m=6 counterexample

This file is an independent exact integer/rational witness.  It does not rely
on the earlier floating B3 optimizer output.  The unscaled world has

* response spans `(13,13,13,12,12,12)`, hence strict Top-3 `{0,1,2}`;
* selected compression loss `87/2`;
* competitor `{3,4,5}` compression loss `13/2`;
* doubled decision gap `74`;
* every mixed difference bounded by `14`;
* all centered interaction profiles rank one and, in fact, at most two-profile.

After positive rescaling by `1/14`, the world has unit interaction bound and

    2D = 37/7 > 5 = m-1.

Thus RankOne + TwoProfile + StrictTopC does not recover the old m-1 law.
All arithmetic is exact over `ℝ` numerals; no numerical optimizer is used in
this formal witness.
-/

namespace CIGAMF.P13.D6StrictTwoProfileRankOneM6CounterexampleV2

set_option maxHeartbeats 120000000
set_option maxRecDepth 10000

open scoped BigOperators Matrix
open CIGAMF.V4.SupportGeometry
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6ActiveDecisionCell
open CIGAMF.P13.D6PolyhedralActiveCell
open CIGAMF.P13.D6DecisionInteractionComplexity
open CIGAMF.P13.D6InteractionContrastProfile
open CIGAMF.P13.D6InteractionContrastRankOne
open CIGAMF.P13.D6InteractionContrastAnchorInvariance
open CIGAMF.P13.D6InteractionContrastProfileReduction
open CIGAMF.P13.D6ContrastRankPhaseDefinitionsV2
open CIGAMF.P13.D6ResidualCentering

/-! ## Finite actions and point-mass reference -/

def a6t (a b c d e f : Fin 3) : Fin 6 → Fin 3 := ![a,b,c,d,e,f]
def z6t : Fin 6 → Fin 3 := a6t 0 0 0 0 0 0

@[simp] theorem a6t_0 (a b c d e f : Fin 3) : a6t a b c d e f 0 = a := by rfl
@[simp] theorem a6t_1 (a b c d e f : Fin 3) : a6t a b c d e f 1 = b := by rfl
@[simp] theorem a6t_2 (a b c d e f : Fin 3) : a6t a b c d e f 2 = c := by rfl
@[simp] theorem a6t_3 (a b c d e f : Fin 3) : a6t a b c d e f 3 = d := by rfl
@[simp] theorem a6t_4 (a b c d e f : Fin 3) : a6t a b c d e f 4 = e := by rfl
@[simp] theorem a6t_5 (a b c d e f : Fin 3) : a6t a b c d e f 5 = f := by rfl

def cornerQ6 (_i : Fin 6) (u : Fin 3) : ℝ := if u = 0 then 1 else 0

private theorem fin3_cases (u : Fin 3) : u = 0 ∨ u = 1 ∨ u = 2 := by
  fin_cases u <;> simp

theorem cornerQ6_jointWeight (c : Fin 6 → Fin 3) :
    jointWeight cornerQ6 c = if c = z6t then 1 else 0 := by
  classical
  by_cases h : c = z6t
  · subst c
    simp [jointWeight, cornerQ6, z6t, a6t, Fin.prod_univ_six]
  · have hc : c 0 ≠ 0 ∨ c 1 ≠ 0 ∨ c 2 ≠ 0 ∨ c 3 ≠ 0 ∨ c 4 ≠ 0 ∨ c 5 ≠ 0 := by
      by_contra hn
      push_neg at hn
      apply h
      funext i
      fin_cases i <;>
        simp [hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1,
          hn.2.2.2.2.1, hn.2.2.2.2.2, z6t, a6t]
    rcases hc with h0 | h1 | h2 | h3 | h4 | h5
    · simp [jointWeight, cornerQ6, Fin.prod_univ_six, h0, h]
    · simp [jointWeight, cornerQ6, Fin.prod_univ_six, h1, h]
    · simp [jointWeight, cornerQ6, Fin.prod_univ_six, h2, h]
    · simp [jointWeight, cornerQ6, Fin.prod_univ_six, h3, h]
    · simp [jointWeight, cornerQ6, Fin.prod_univ_six, h4, h]
    · simp [jointWeight, cornerQ6, Fin.prod_univ_six, h5, h]

theorem cornerQ6_nonnegative : ∀ c, 0 ≤ jointWeight cornerQ6 c := by
  intro c
  rw [cornerQ6_jointWeight]
  split <;> norm_num

theorem cornerQ6_normalized : ∑ c, jointWeight cornerQ6 c = 1 := by
  classical
  simp_rw [cornerQ6_jointWeight]
  rw [Finset.sum_eq_single z6t]
  · simp
  · intro c hc hne
    simp [hne]
  · simp

theorem cornerQ6_expectation (G : (Fin 6 → Fin 3) → ℝ) :
    productExpectation cornerQ6 G = G z6t := by
  classical
  unfold productExpectation
  simp_rw [cornerQ6_jointWeight]
  rw [Finset.sum_eq_single z6t]
  · simp
  · intro c hc hne
    simp [hne]
  · simp

theorem cornerQ6_response (F : (Fin 6 → Fin 3) → ℝ) (i : Fin 6) (u : Fin 3) :
    productResponse cornerQ6 F i u = F (Function.update z6t i u) := by
  unfold productResponse
  rw [cornerQ6_expectation]

/-! ## Exact rank-one multiaffine witness -/

/-- Latent interaction symbol: actions 0 and 2 share the zero interaction fibre. -/
def phi (u : Fin 3) : ℝ := if u = 1 then 1 else 0

/-- Purely additive action-2 direction used only at coordinate 5. -/
def eta (u : Fin 3) : ℝ := if u = 2 then 1 else 0

@[simp] theorem phi_zero : phi 0 = 0 := by norm_num [phi]
@[simp] theorem phi_one : phi 1 = 1 := by norm_num [phi]
@[simp] theorem phi_two : phi 2 = 0 := by norm_num [phi]
@[simp] theorem eta_zero : eta 0 = 0 := by norm_num [eta]
@[simp] theorem eta_one : eta 1 = 0 := by norm_num [eta]
@[simp] theorem eta_two : eta 2 = 1 := by norm_num [eta]

def additiveComponent (i : Fin 6) (u : Fin 3) : ℝ :=
  match i with
  | ⟨0, _⟩ => 13 * phi u
  | ⟨1, _⟩ => 13 * phi u
  | ⟨2, _⟩ => 13 * phi u
  | ⟨3, _⟩ => 12 * phi u
  | ⟨4, _⟩ => 12 * phi u
  | ⟨5, _⟩ => 12 * eta u

noncomputable def rawAdditive (x : Fin 6 → Fin 3) : ℝ :=
  coordinateAdditiveWorld additiveComponent 0 x

/-- The interaction part lies in the scalar multiaffine fibre phi=(0,1,0). -/
def rawInteraction (x : Fin 6 → Fin 3) : ℝ :=
    - 13 * phi (x 0) * phi (x 1)
    - 13 * phi (x 0) * phi (x 2)
    - 13 * phi (x 0) * phi (x 5)
    - 13 * phi (x 1) * phi (x 2)
    - 13 * phi (x 1) * phi (x 5)
    - 13 * phi (x 2) * phi (x 5)
    + 12 * phi (x 3) * phi (x 4)
    + 13 * phi (x 0) * phi (x 1) * phi (x 2)
    + 13 * phi (x 0) * phi (x 1) * phi (x 5)
    + 13 * phi (x 0) * phi (x 2) * phi (x 5)
    - 12 * phi (x 0) * phi (x 3) * phi (x 4)
    + 14 * phi (x 1) * phi (x 2) * phi (x 5)
    - 12 * phi (x 1) * phi (x 3) * phi (x 4)
    - 12 * phi (x 2) * phi (x 3) * phi (x 4)
    - 12 * phi (x 3) * phi (x 4) * phi (x 5)
    - 14 * phi (x 0) * phi (x 1) * phi (x 2) * phi (x 5)
    + 12 * phi (x 0) * phi (x 1) * phi (x 3) * phi (x 4)
    + 11 * phi (x 0) * phi (x 1) * phi (x 3) * phi (x 5)
    + 12 * phi (x 0) * phi (x 1) * phi (x 4) * phi (x 5)
    + 12 * phi (x 0) * phi (x 2) * phi (x 3) * phi (x 4)
    + 12 * phi (x 0) * phi (x 2) * phi (x 3) * phi (x 5)
    + 12 * phi (x 0) * phi (x 2) * phi (x 4) * phi (x 5)
    + 24 * phi (x 0) * phi (x 3) * phi (x 4) * phi (x 5)
    + 12 * phi (x 1) * phi (x 2) * phi (x 3) * phi (x 4)
    + 11 * phi (x 1) * phi (x 2) * phi (x 3) * phi (x 5)
    + 11 * phi (x 1) * phi (x 2) * phi (x 4) * phi (x 5)
    + 12 * phi (x 1) * phi (x 3) * phi (x 4) * phi (x 5)
    + 24 * phi (x 2) * phi (x 3) * phi (x 4) * phi (x 5)
    - 12 * phi (x 0) * phi (x 1) * phi (x 2) * phi (x 3) * phi (x 4)
    - 23 * phi (x 0) * phi (x 1) * phi (x 2) * phi (x 3) * phi (x 5)
    - 23 * phi (x 0) * phi (x 1) * phi (x 2) * phi (x 4) * phi (x 5)
    - 36 * phi (x 0) * phi (x 1) * phi (x 3) * phi (x 4) * phi (x 5)
    - 49 * phi (x 0) * phi (x 2) * phi (x 3) * phi (x 4) * phi (x 5)
    - 35 * phi (x 1) * phi (x 2) * phi (x 3) * phi (x 4) * phi (x 5)
    + 60 * phi (x 0) * phi (x 1) * phi (x 2) * phi (x 3) * phi (x 4) * phi (x 5)

def rawWorld (x : Fin 6 → Fin 3) : ℝ := rawInteraction x + rawAdditive x

def scaledComponent (i : Fin 6) (u : Fin 3) : ℝ := additiveComponent i u / 14

noncomputable def witnessWorld (x : Fin 6 → Fin 3) : ℝ :=
  rawInteraction x / 14 + coordinateAdditiveWorld scaledComponent 0 x

private theorem witnessWorld_eq_rawWorld_div (x : Fin 6 → Fin 3) :
    witnessWorld x = rawWorld x / 14 := by
  unfold witnessWorld rawWorld rawAdditive scaledComponent coordinateAdditiveWorld
  simp only [Finset.sum_div]
  ring

/-- Context coefficient of phi(x_i) in the interaction polynomial. -/
def contextCoeff (i : Fin 6) (x : Fin 6 → Fin 3) : ℝ :=
  match i with
  | ⟨0, _⟩ =>
      - 13 * phi (x 1) - 13 * phi (x 2) - 13 * phi (x 5)
      + 13 * phi (x 1) * phi (x 2) + 13 * phi (x 1) * phi (x 5)
      + 13 * phi (x 2) * phi (x 5) - 12 * phi (x 3) * phi (x 4)
      - 14 * phi (x 1) * phi (x 2) * phi (x 5)
      + 12 * phi (x 1) * phi (x 3) * phi (x 4)
      + 11 * phi (x 1) * phi (x 3) * phi (x 5)
      + 12 * phi (x 1) * phi (x 4) * phi (x 5)
      + 12 * phi (x 2) * phi (x 3) * phi (x 4)
      + 12 * phi (x 2) * phi (x 3) * phi (x 5)
      + 12 * phi (x 2) * phi (x 4) * phi (x 5)
      + 24 * phi (x 3) * phi (x 4) * phi (x 5)
      - 12 * phi (x 1) * phi (x 2) * phi (x 3) * phi (x 4)
      - 23 * phi (x 1) * phi (x 2) * phi (x 3) * phi (x 5)
      - 23 * phi (x 1) * phi (x 2) * phi (x 4) * phi (x 5)
      - 36 * phi (x 1) * phi (x 3) * phi (x 4) * phi (x 5)
      - 49 * phi (x 2) * phi (x 3) * phi (x 4) * phi (x 5)
      + 60 * phi (x 1) * phi (x 2) * phi (x 3) * phi (x 4) * phi (x 5)
  | ⟨1, _⟩ =>
      - 13 * phi (x 0) - 13 * phi (x 2) - 13 * phi (x 5)
      + 13 * phi (x 0) * phi (x 2) + 13 * phi (x 0) * phi (x 5)
      + 14 * phi (x 2) * phi (x 5) - 12 * phi (x 3) * phi (x 4)
      - 14 * phi (x 0) * phi (x 2) * phi (x 5)
      + 12 * phi (x 0) * phi (x 3) * phi (x 4)
      + 11 * phi (x 0) * phi (x 3) * phi (x 5)
      + 12 * phi (x 0) * phi (x 4) * phi (x 5)
      + 12 * phi (x 2) * phi (x 3) * phi (x 4)
      + 11 * phi (x 2) * phi (x 3) * phi (x 5)
      + 11 * phi (x 2) * phi (x 4) * phi (x 5)
      + 12 * phi (x 3) * phi (x 4) * phi (x 5)
      - 12 * phi (x 0) * phi (x 2) * phi (x 3) * phi (x 4)
      - 23 * phi (x 0) * phi (x 2) * phi (x 3) * phi (x 5)
      - 23 * phi (x 0) * phi (x 2) * phi (x 4) * phi (x 5)
      - 36 * phi (x 0) * phi (x 3) * phi (x 4) * phi (x 5)
      - 35 * phi (x 2) * phi (x 3) * phi (x 4) * phi (x 5)
      + 60 * phi (x 0) * phi (x 2) * phi (x 3) * phi (x 4) * phi (x 5)
  | ⟨2, _⟩ =>
      - 13 * phi (x 0) - 13 * phi (x 1) - 13 * phi (x 5)
      + 13 * phi (x 0) * phi (x 1) + 13 * phi (x 0) * phi (x 5)
      + 14 * phi (x 1) * phi (x 5) - 12 * phi (x 3) * phi (x 4)
      - 14 * phi (x 0) * phi (x 1) * phi (x 5)
      + 12 * phi (x 0) * phi (x 3) * phi (x 4)
      + 12 * phi (x 0) * phi (x 3) * phi (x 5)
      + 12 * phi (x 0) * phi (x 4) * phi (x 5)
      + 12 * phi (x 1) * phi (x 3) * phi (x 4)
      + 11 * phi (x 1) * phi (x 3) * phi (x 5)
      + 11 * phi (x 1) * phi (x 4) * phi (x 5)
      + 24 * phi (x 3) * phi (x 4) * phi (x 5)
      - 12 * phi (x 0) * phi (x 1) * phi (x 3) * phi (x 4)
      - 23 * phi (x 0) * phi (x 1) * phi (x 3) * phi (x 5)
      - 23 * phi (x 0) * phi (x 1) * phi (x 4) * phi (x 5)
      - 49 * phi (x 0) * phi (x 3) * phi (x 4) * phi (x 5)
      - 35 * phi (x 1) * phi (x 3) * phi (x 4) * phi (x 5)
      + 60 * phi (x 0) * phi (x 1) * phi (x 3) * phi (x 4) * phi (x 5)
  | ⟨3, _⟩ =>
      12 * phi (x 4) - 12 * phi (x 0) * phi (x 4)
      - 12 * phi (x 1) * phi (x 4) - 12 * phi (x 2) * phi (x 4)
      - 12 * phi (x 4) * phi (x 5)
      + 12 * phi (x 0) * phi (x 1) * phi (x 4)
      + 11 * phi (x 0) * phi (x 1) * phi (x 5)
      + 12 * phi (x 0) * phi (x 2) * phi (x 4)
      + 12 * phi (x 0) * phi (x 2) * phi (x 5)
      + 24 * phi (x 0) * phi (x 4) * phi (x 5)
      + 12 * phi (x 1) * phi (x 2) * phi (x 4)
      + 11 * phi (x 1) * phi (x 2) * phi (x 5)
      + 12 * phi (x 1) * phi (x 4) * phi (x 5)
      + 24 * phi (x 2) * phi (x 4) * phi (x 5)
      - 12 * phi (x 0) * phi (x 1) * phi (x 2) * phi (x 4)
      - 23 * phi (x 0) * phi (x 1) * phi (x 2) * phi (x 5)
      - 36 * phi (x 0) * phi (x 1) * phi (x 4) * phi (x 5)
      - 49 * phi (x 0) * phi (x 2) * phi (x 4) * phi (x 5)
      - 35 * phi (x 1) * phi (x 2) * phi (x 4) * phi (x 5)
      + 60 * phi (x 0) * phi (x 1) * phi (x 2) * phi (x 4) * phi (x 5)
  | ⟨4, _⟩ =>
      12 * phi (x 3) - 12 * phi (x 0) * phi (x 3)
      - 12 * phi (x 1) * phi (x 3) - 12 * phi (x 2) * phi (x 3)
      - 12 * phi (x 3) * phi (x 5)
      + 12 * phi (x 0) * phi (x 1) * phi (x 3)
      + 12 * phi (x 0) * phi (x 1) * phi (x 5)
      + 12 * phi (x 0) * phi (x 2) * phi (x 3)
      + 12 * phi (x 0) * phi (x 2) * phi (x 5)
      + 24 * phi (x 0) * phi (x 3) * phi (x 5)
      + 12 * phi (x 1) * phi (x 2) * phi (x 3)
      + 11 * phi (x 1) * phi (x 2) * phi (x 5)
      + 12 * phi (x 1) * phi (x 3) * phi (x 5)
      + 24 * phi (x 2) * phi (x 3) * phi (x 5)
      - 12 * phi (x 0) * phi (x 1) * phi (x 2) * phi (x 3)
      - 23 * phi (x 0) * phi (x 1) * phi (x 2) * phi (x 5)
      - 36 * phi (x 0) * phi (x 1) * phi (x 3) * phi (x 5)
      - 49 * phi (x 0) * phi (x 2) * phi (x 3) * phi (x 5)
      - 35 * phi (x 1) * phi (x 2) * phi (x 3) * phi (x 5)
      + 60 * phi (x 0) * phi (x 1) * phi (x 2) * phi (x 3) * phi (x 5)
  | ⟨5, _⟩ =>
      - 13 * phi (x 0) - 13 * phi (x 1) - 13 * phi (x 2)
      + 13 * phi (x 0) * phi (x 1) + 13 * phi (x 0) * phi (x 2)
      + 14 * phi (x 1) * phi (x 2) - 12 * phi (x 3) * phi (x 4)
      - 14 * phi (x 0) * phi (x 1) * phi (x 2)
      + 11 * phi (x 0) * phi (x 1) * phi (x 3)
      + 12 * phi (x 0) * phi (x 1) * phi (x 4)
      + 12 * phi (x 0) * phi (x 2) * phi (x 3)
      + 12 * phi (x 0) * phi (x 2) * phi (x 4)
      + 24 * phi (x 0) * phi (x 3) * phi (x 4)
      + 11 * phi (x 1) * phi (x 2) * phi (x 3)
      + 11 * phi (x 1) * phi (x 2) * phi (x 4)
      + 12 * phi (x 1) * phi (x 3) * phi (x 4)
      + 24 * phi (x 2) * phi (x 3) * phi (x 4)
      - 23 * phi (x 0) * phi (x 1) * phi (x 2) * phi (x 3)
      - 23 * phi (x 0) * phi (x 1) * phi (x 2) * phi (x 4)
      - 36 * phi (x 0) * phi (x 1) * phi (x 3) * phi (x 4)
      - 49 * phi (x 0) * phi (x 2) * phi (x 3) * phi (x 4)
      - 35 * phi (x 1) * phi (x 2) * phi (x 3) * phi (x 4)
      + 60 * phi (x 0) * phi (x 1) * phi (x 2) * phi (x 3) * phi (x 4)

def coeffLo (i : Fin 6) : ℝ := ![-14, -14, -14, -1, -1, -13] i
def coeffHi (i : Fin 6) : ℝ := ![0, 0, 0, 12, 12, 0] i

private theorem contextCoeff_bounds (i : Fin 6) (x : Fin 6 → Fin 3) :
    coeffLo i ≤ contextCoeff i x ∧ contextCoeff i x ≤ coeffHi i := by
  fin_cases i
  · rcases fin3_cases (x 1) with h1 | h1 | h1 <;>
      rcases fin3_cases (x 2) with h2 | h2 | h2 <;>
      rcases fin3_cases (x 3) with h3 | h3 | h3 <;>
      rcases fin3_cases (x 4) with h4 | h4 | h4 <;>
      rcases fin3_cases (x 5) with h5 | h5 | h5 <;>
      simp [contextCoeff, coeffLo, coeffHi, phi, h1, h2, h3, h4, h5] <;> norm_num
  · rcases fin3_cases (x 0) with h0 | h0 | h0 <;>
      rcases fin3_cases (x 2) with h2 | h2 | h2 <;>
      rcases fin3_cases (x 3) with h3 | h3 | h3 <;>
      rcases fin3_cases (x 4) with h4 | h4 | h4 <;>
      rcases fin3_cases (x 5) with h5 | h5 | h5 <;>
      simp [contextCoeff, coeffLo, coeffHi, phi, h0, h2, h3, h4, h5] <;> norm_num
  · rcases fin3_cases (x 0) with h0 | h0 | h0 <;>
      rcases fin3_cases (x 1) with h1 | h1 | h1 <;>
      rcases fin3_cases (x 3) with h3 | h3 | h3 <;>
      rcases fin3_cases (x 4) with h4 | h4 | h4 <;>
      rcases fin3_cases (x 5) with h5 | h5 | h5 <;>
      simp [contextCoeff, coeffLo, coeffHi, phi, h0, h1, h3, h4, h5] <;> norm_num
  · rcases fin3_cases (x 0) with h0 | h0 | h0 <;>
      rcases fin3_cases (x 1) with h1 | h1 | h1 <;>
      rcases fin3_cases (x 2) with h2 | h2 | h2 <;>
      rcases fin3_cases (x 4) with h4 | h4 | h4 <;>
      rcases fin3_cases (x 5) with h5 | h5 | h5 <;>
      simp [contextCoeff, coeffLo, coeffHi, phi, h0, h1, h2, h4, h5] <;> norm_num
  · rcases fin3_cases (x 0) with h0 | h0 | h0 <;>
      rcases fin3_cases (x 1) with h1 | h1 | h1 <;>
      rcases fin3_cases (x 2) with h2 | h2 | h2 <;>
      rcases fin3_cases (x 3) with h3 | h3 | h3 <;>
      rcases fin3_cases (x 5) with h5 | h5 | h5 <;>
      simp [contextCoeff, coeffLo, coeffHi, phi, h0, h1, h2, h3, h5] <;> norm_num
  · rcases fin3_cases (x 0) with h0 | h0 | h0 <;>
      rcases fin3_cases (x 1) with h1 | h1 | h1 <;>
      rcases fin3_cases (x 2) with h2 | h2 | h2 <;>
      rcases fin3_cases (x 3) with h3 | h3 | h3 <;>
      rcases fin3_cases (x 4) with h4 | h4 | h4 <;>
      simp [contextCoeff, coeffLo, coeffHi, phi, h0, h1, h2, h3, h4] <;> norm_num

private theorem coeff_width_le_fourteen (i : Fin 6) : coeffHi i - coeffLo i ≤ 14 := by
  fin_cases i <;> norm_num [coeffHi, coeffLo]

private theorem contextCoeff_diff_abs_le_fourteen (i : Fin 6)
    (x c : Fin 6 → Fin 3) : |contextCoeff i x - contextCoeff i c| ≤ 14 := by
  have hx := contextCoeff_bounds i x
  have hc := contextCoeff_bounds i c
  have hw := coeff_width_le_fourteen i
  rw [abs_le]
  constructor <;> linarith

private theorem rawInteraction_update_difference (i : Fin 6) (u v : Fin 3)
    (z : Fin 6 → Fin 3) :
    rawInteraction (Function.update z i u) - rawInteraction (Function.update z i v) =
      (phi u - phi v) * contextCoeff i z := by
  fin_cases i <;>
    simp [rawInteraction, contextCoeff, Function.update] <;> ring

private theorem rawInteraction_mixed_factor (i : Fin 6)
    (x c : Fin 6 → Fin 3) :
    mixedDifference rawInteraction i x c =
      (phi (x i) - phi (c i)) * (contextCoeff i x - contextCoeff i c) := by
  unfold mixedDifference
  have h1 := rawInteraction_update_difference i (x i) (c i) x
  have h2 := rawInteraction_update_difference i (x i) (c i) c
  have hxx : Function.update x i (x i) = x := Function.update_eq_self_iff.mpr rfl
  have hcc : Function.update c i (c i) = c := Function.update_eq_self_iff.mpr rfl
  rw [hxx] at h1
  rw [hcc] at h2
  linarith

private theorem phi_diff_abs_le_one (u v : Fin 3) : |phi u - phi v| ≤ 1 := by
  fin_cases u <;> fin_cases v <;> norm_num [phi]

private theorem rawInteraction_mixed_le_fourteen (i : Fin 6)
    (x c : Fin 6 → Fin 3) : |mixedDifference rawInteraction i x c| ≤ 14 := by
  rw [rawInteraction_mixed_factor, abs_mul]
  have hφ := phi_diff_abs_le_one (x i) (c i)
  have hH := contextCoeff_diff_abs_le_fourteen i x c
  calc
    |phi (x i) - phi (c i)| * |contextCoeff i x - contextCoeff i c| ≤
        1 * 14 := mul_le_mul hφ hH (abs_nonneg _) (by norm_num)
    _ = 14 := by norm_num

private theorem rawWorld_mixed_eq_interaction (i : Fin 6)
    (x c : Fin 6 → Fin 3) :
    mixedDifference rawWorld i x c = mixedDifference rawInteraction i x c := by
  have hz := mixedDifference_sum_coordinates_zero additiveComponent (0 : ℝ) i x c
  unfold rawWorld rawAdditive
  unfold mixedDifference at hz ⊢
  linarith

private theorem witnessWorld_mixed_scale (i : Fin 6)
    (x c : Fin 6 → Fin 3) :
    mixedDifference witnessWorld i x c = mixedDifference rawWorld i x c / 14 := by
  simp_rw [witnessWorld_eq_rawWorld_div]
  unfold mixedDifference
  ring

theorem witnessWorld_unitInteraction : UnitInteractionBound witnessWorld := by
  intro i x c
  have hraw := rawInteraction_mixed_le_fourteen i x c
  have heq := rawWorld_mixed_eq_interaction i x c
  rw [witnessWorld_mixed_scale, heq, abs_div]
  norm_num
  nlinarith [abs_nonneg (mixedDifference rawInteraction i x c)]

/-! ## Product responses and strict Top-C -/

def responseTable (i : Fin 6) (u : Fin 3) : ℝ :=
  match i with
  | ⟨0, _⟩ => if u = 1 then 13 / 14 else 0
  | ⟨1, _⟩ => if u = 1 then 13 / 14 else 0
  | ⟨2, _⟩ => if u = 1 then 13 / 14 else 0
  | ⟨3, _⟩ => if u = 1 then 6 / 7 else 0
  | ⟨4, _⟩ => if u = 1 then 6 / 7 else 0
  | ⟨5, _⟩ => if u = 2 then 6 / 7 else 0

private theorem witnessWorld_insert_zero (i : Fin 6) (u : Fin 3) :
    witnessWorld (Function.update z6t i u) = responseTable i u := by
  fin_cases i <;> fin_cases u <;>
    norm_num [witnessWorld, rawInteraction, coordinateAdditiveWorld,
      scaledComponent, additiveComponent, responseTable,
      phi, eta, z6t, a6t, Function.update, Fin.sum_univ_six]

@[simp] theorem witness_response_table (i : Fin 6) (u : Fin 3) :
    productResponse cornerQ6 witnessWorld i u = responseTable i u := by
  rw [cornerQ6_response, witnessWorld_insert_zero]

def selected6 : Finset (Fin 6) := {0,1,2}
def competitor6 : Finset (Fin 6) := {3,4,5}

def responseMax6 : Fin 6 → Fin 3 := a6t 1 1 1 1 1 2
def responseMin6 : Fin 6 → Fin 3 := z6t

private theorem response_max (i : Fin 6) (u : Fin 3) :
    productResponse cornerQ6 witnessWorld i u ≤
      productResponse cornerQ6 witnessWorld i (responseMax6 i) := by
  fin_cases i <;> fin_cases u <;>
    norm_num [witness_response_table, responseTable, responseMax6, a6t]

private theorem response_min (i : Fin 6) (u : Fin 3) :
    productResponse cornerQ6 witnessWorld i (responseMin6 i) ≤
      productResponse cornerQ6 witnessWorld i u := by
  fin_cases i <;> fin_cases u <;>
    norm_num [witness_response_table, responseTable, responseMin6, z6t, a6t]

private theorem response_osc (i : Fin 6) :
    osc (productResponse cornerQ6 witnessWorld i) =
      productResponse cornerQ6 witnessWorld i (responseMax6 i) -
        productResponse cornerQ6 witnessWorld i (responseMin6 i) := by
  unfold osc
  rw [le_antisymm (maxVal_le _ (response_max i)) (le_maxVal _ (responseMax6 i)),
    le_antisymm (minVal_le _ (responseMin6 i)) (le_minVal _ (response_min i))]

 theorem witness_response_spans :
    osc (productResponse cornerQ6 witnessWorld 0) = 13 / 14 ∧
    osc (productResponse cornerQ6 witnessWorld 1) = 13 / 14 ∧
    osc (productResponse cornerQ6 witnessWorld 2) = 13 / 14 ∧
    osc (productResponse cornerQ6 witnessWorld 3) = 6 / 7 ∧
    osc (productResponse cornerQ6 witnessWorld 4) = 6 / 7 ∧
    osc (productResponse cornerQ6 witnessWorld 5) = 6 / 7 := by
  constructor
  · rw [response_osc]
    norm_num [witness_response_table, responseTable, responseMax6,
      responseMin6, z6t, a6t]
  constructor
  · rw [response_osc]
    norm_num [witness_response_table, responseTable, responseMax6,
      responseMin6, z6t, a6t]
  constructor
  · rw [response_osc]
    norm_num [witness_response_table, responseTable, responseMax6,
      responseMin6, z6t, a6t]
  constructor
  · rw [response_osc]
    norm_num [witness_response_table, responseTable, responseMax6,
      responseMin6, z6t, a6t]
  constructor
  · rw [response_osc]
    norm_num [witness_response_table, responseTable, responseMax6,
      responseMin6, z6t, a6t]
  · rw [response_osc]
    norm_num [witness_response_table, responseTable, responseMax6,
      responseMin6, z6t, a6t]

 theorem witness_strictTopC :
    ∀ i ∈ selected6, ∀ j ∉ selected6,
      osc (productResponse cornerQ6 witnessWorld j) <
        osc (productResponse cornerQ6 witnessWorld i) := by
  intro i hi j hj
  rcases witness_response_spans with ⟨h0,h1,h2,h3,h4,h5⟩
  fin_cases i <;> fin_cases j <;>
    simp [selected6] at hi hj ⊢ <;> linarith

/-! ## Exact decision losses -/

private theorem selected_sum (g : Fin 6 → ℝ) : selected6.sum g = g 0 + g 1 + g 2 := by
  simp [selected6]
  ring

private theorem competitor_sum (g : Fin 6 → ℝ) : competitor6.sum g = g 3 + g 4 + g 5 := by
  simp [competitor6]
  ring

noncomputable def rawResidualS (x : Fin 6 → Fin 3) : ℝ :=
  rawWorld x - 13 * phi (x 0) - 13 * phi (x 1) - 13 * phi (x 2)

noncomputable def rawResidualT (x : Fin 6 → Fin 3) : ℝ :=
  rawWorld x - 12 * phi (x 3) - 12 * phi (x 4) - 12 * eta (x 5)

private theorem selected_residual_eq (x : Fin 6 → Fin 3) :
    witnessWorld x - selected6.sum
      (fun j ↦ productResponse cornerQ6 witnessWorld j (x j)) = rawResidualS x / 14 := by
  rw [selected_sum]
  rcases fin3_cases (x 0) with h0 | h0 | h0 <;>
    rcases fin3_cases (x 1) with h1 | h1 | h1 <;>
    rcases fin3_cases (x 2) with h2 | h2 | h2 <;>
    rw [witnessWorld_eq_rawWorld_div]
    simp [witness_response_table, responseTable, rawResidualS,
      phi, eta, h0, h1, h2] <;> ring

private theorem competitor_residual_eq (x : Fin 6 → Fin 3) :
    witnessWorld x - competitor6.sum
      (fun j ↦ productResponse cornerQ6 witnessWorld j (x j)) = rawResidualT x / 14 := by
  rw [competitor_sum]
  rcases fin3_cases (x 3) with h3 | h3 | h3 <;>
    rcases fin3_cases (x 4) with h4 | h4 | h4 <;>
    rcases fin3_cases (x 5) with h5 | h5 | h5 <;>
    rw [witnessWorld_eq_rawWorld_div]
    simp [witness_response_table, responseTable, rawResidualT,
      phi, eta, h3, h4, h5] <;> ring

private theorem rawSelected_bounds (x : Fin 6 → Fin 3) :
    (-39 : ℝ) ≤ rawResidualS x ∧ rawResidualS x ≤ 48 := by
  rcases fin3_cases (x 0) with h0 | h0 | h0 <;>
    rcases fin3_cases (x 1) with h1 | h1 | h1 <;>
    rcases fin3_cases (x 2) with h2 | h2 | h2 <;>
    rcases fin3_cases (x 3) with h3 | h3 | h3 <;>
    rcases fin3_cases (x 4) with h4 | h4 | h4 <;>
    rcases fin3_cases (x 5) with h5 | h5 | h5 <;>
    simp [rawResidualS, rawWorld, rawInteraction, rawAdditive,
      coordinateAdditiveWorld, additiveComponent, phi, eta,
      h0,h1,h2,h3,h4,h5, Fin.sum_univ_six] <;> norm_num

private theorem rawCompetitor_bounds (x : Fin 6 → Fin 3) :
    (0 : ℝ) ≤ rawResidualT x ∧ rawResidualT x ≤ 13 := by
  rcases fin3_cases (x 0) with h0 | h0 | h0 <;>
    rcases fin3_cases (x 1) with h1 | h1 | h1 <;>
    rcases fin3_cases (x 2) with h2 | h2 | h2 <;>
    rcases fin3_cases (x 3) with h3 | h3 | h3 <;>
    rcases fin3_cases (x 4) with h4 | h4 | h4 <;>
    rcases fin3_cases (x 5) with h5 | h5 | h5 <;>
    simp [rawResidualT, rawWorld, rawInteraction, rawAdditive,
      coordinateAdditiveWorld, additiveComponent, phi, eta,
      h0,h1,h2,h3,h4,h5, Fin.sum_univ_six] <;> norm_num

private theorem selected_bounds (x : Fin 6 → Fin 3) :
    (-39 / 14 : ℝ) ≤ witnessWorld x - selected6.sum
      (fun j ↦ productResponse cornerQ6 witnessWorld j (x j)) ∧
    witnessWorld x - selected6.sum
      (fun j ↦ productResponse cornerQ6 witnessWorld j (x j)) ≤ 24 / 7 := by
  rw [selected_residual_eq]
  have h := rawSelected_bounds x
  constructor <;> nlinarith

private theorem competitor_bounds (x : Fin 6 → Fin 3) :
    (0 : ℝ) ≤ witnessWorld x - competitor6.sum
      (fun j ↦ productResponse cornerQ6 witnessWorld j (x j)) ∧
    witnessWorld x - competitor6.sum
      (fun j ↦ productResponse cornerQ6 witnessWorld j (x j)) ≤ 13 / 14 := by
  rw [competitor_residual_eq]
  have h := rawCompetitor_bounds x
  constructor <;> nlinarith

def selectedMin6 : Fin 6 → Fin 3 := a6t 1 1 1 0 0 1
def selectedMax6 : Fin 6 → Fin 3 := a6t 2 2 2 1 1 2
def competitorMin6 : Fin 6 → Fin 3 := z6t
def competitorMax6 : Fin 6 → Fin 3 := a6t 2 2 1 2 2 2

private theorem selected_min_eval :
    witnessWorld selectedMin6 - selected6.sum
      (fun j ↦ productResponse cornerQ6 witnessWorld j (selectedMin6 j)) = -39 / 14 := by
  rw [selected_residual_eq]
  norm_num [rawResidualS, rawWorld, rawInteraction, rawAdditive,
    coordinateAdditiveWorld, additiveComponent, selectedMin6, a6t, phi, eta,
    Fin.sum_univ_six]

private theorem selected_max_eval :
    witnessWorld selectedMax6 - selected6.sum
      (fun j ↦ productResponse cornerQ6 witnessWorld j (selectedMax6 j)) = 24 / 7 := by
  rw [selected_residual_eq]
  norm_num [rawResidualS, rawWorld, rawInteraction, rawAdditive,
    coordinateAdditiveWorld, additiveComponent, selectedMax6, a6t, phi, eta,
    Fin.sum_univ_six]

private theorem competitor_min_eval :
    witnessWorld competitorMin6 - competitor6.sum
      (fun j ↦ productResponse cornerQ6 witnessWorld j (competitorMin6 j)) = 0 := by
  rw [competitor_residual_eq]
  norm_num [rawResidualT, rawWorld, rawInteraction, rawAdditive,
    coordinateAdditiveWorld, additiveComponent, competitorMin6, z6t, a6t, phi, eta,
    Fin.sum_univ_six]

private theorem competitor_max_eval :
    witnessWorld competitorMax6 - competitor6.sum
      (fun j ↦ productResponse cornerQ6 witnessWorld j (competitorMax6 j)) = 13 / 14 := by
  rw [competitor_residual_eq]
  norm_num [rawResidualT, rawWorld, rawInteraction, rawAdditive,
    coordinateAdditiveWorld, additiveComponent, competitorMax6, a6t, phi, eta,
    Fin.sum_univ_six]

private theorem compressionLoss_eq_of_bounds
    (S : Finset (Fin 6)) (lo hi : ℝ)
    (hbound : ∀ x, lo ≤ witnessWorld x -
        S.sum (fun j ↦ productResponse cornerQ6 witnessWorld j (x j)) ∧
      witnessWorld x -
        S.sum (fun j ↦ productResponse cornerQ6 witnessWorld j (x j)) ≤ hi)
    (xmin xmax : Fin 6 → Fin 3)
    (hmin : witnessWorld xmin -
        S.sum (fun j ↦ productResponse cornerQ6 witnessWorld j (xmin j)) = lo)
    (hmax : witnessWorld xmax -
        S.sum (fun j ↦ productResponse cornerQ6 witnessWorld j (xmax j)) = hi) :
    productCompressionLoss witnessWorld
      (productResponse cornerQ6 witnessWorld) S = (hi - lo) / 2 := by
  let r : (Fin 6 → Fin 3) → ℝ := fun x ↦ witnessWorld x -
    S.sum (fun j ↦ productResponse cornerQ6 witnessWorld j (x j))
  have hrmax : maxVal r = hi := by
    apply le_antisymm
    · exact maxVal_le r (fun x ↦ (hbound x).2)
    · calc
        hi = r xmax := hmax.symm
        _ ≤ maxVal r := le_maxVal r xmax
  have hrmin : minVal r = lo := by
    apply le_antisymm
    · calc
        minVal r ≤ r xmin := minVal_le r xmin
        _ = lo := hmin
    · exact le_minVal r (fun x ↦ (hbound x).1)
  unfold productCompressionLoss
  change (maxVal r - minVal r) / 2 = (hi - lo) / 2
  rw [hrmax, hrmin]

 theorem witness_selected_loss :
    productCompressionLoss witnessWorld
      (productResponse cornerQ6 witnessWorld) selected6 = 87 / 28 := by
  convert compressionLoss_eq_of_bounds selected6 (-39 / 14) (24 / 7)
    selected_bounds selectedMin6 selectedMax6 selected_min_eval selected_max_eval using 1 <;>
    norm_num

 theorem witness_competitor_loss :
    productCompressionLoss witnessWorld
      (productResponse cornerQ6 witnessWorld) competitor6 = 13 / 28 := by
  convert compressionLoss_eq_of_bounds competitor6 0 (13 / 14)
    competitor_bounds competitorMin6 competitorMax6 competitor_min_eval competitor_max_eval using 1 <;>
    norm_num

 theorem witness_doubled_gap :
    2 * (productCompressionLoss witnessWorld
        (productResponse cornerQ6 witnessWorld) selected6 -
      productCompressionLoss witnessWorld
        (productResponse cornerQ6 witnessWorld) competitor6) = 37 / 7 := by
  rw [witness_selected_loss, witness_competitor_loss]
  norm_num

 theorem witness_violates_five :
    (5 : ℝ) < 2 * (productCompressionLoss witnessWorld
        (productResponse cornerQ6 witnessWorld) selected6 -
      productCompressionLoss witnessWorld
        (productResponse cornerQ6 witnessWorld) competitor6) := by
  rw [witness_doubled_gap]
  norm_num

/-! ## Rank one and two-profile geometry -/

private theorem rawInteraction_zero : rawInteraction z6t = 0 := by
  norm_num [rawInteraction, z6t, a6t, phi]

private theorem contextCoeff_zero (i : Fin 6) : contextCoeff i z6t = 0 := by
  fin_cases i <;> norm_num [contextCoeff, z6t, a6t, phi]

private theorem scaledInteraction_update_difference (i : Fin 6) (u v : Fin 3)
    (z : Fin 6 → Fin 3) :
    rawInteraction (Function.update z i u) / 14 -
        rawInteraction (Function.update z i v) / 14 =
      (phi u - phi v) * (contextCoeff i z / 14) := by
  have h := rawInteraction_update_difference i u v z
  linarith

private theorem interaction_profile_factor_at_zero (i : Fin 6) (u : Fin 3)
    (z : Fin 6 → Fin 3) :
    interactionContrastProfile cornerQ6 witnessWorld i 0 u z =
      phi u * (contextCoeff i z / 14) := by
  have hnorm := cornerQ6_normalized
  unfold witnessWorld
  rw [interactionContrastProfile_coordinateAdditive_invariant
    cornerQ6 (fun x ↦ rawInteraction x / 14)
    scaledComponent 0 hnorm i 0 u z]
  unfold interactionContrastProfile
  rw [cornerQ6_response, cornerQ6_response]
  have hloc := scaledInteraction_update_difference i u 0 z
  have hanchor := scaledInteraction_update_difference i u 0 z6t
  have hz : contextCoeff i z6t = 0 := contextCoeff_zero i
  have hφ0 : phi (0 : Fin 3) = 0 := phi_zero
  have hupd : Function.update z6t i 0 = z6t := by
    funext j
    fin_cases i <;> fin_cases j <;> rfl
  simp only [hφ0, zero_mul, sub_zero] at hloc hanchor
  rw [hupd, hz] at hanchor
  norm_num at hanchor
  linarith

 theorem witness_rankOne_at_zero (i : Fin 6) :
    InteractionContrastRankOne cornerQ6 witnessWorld i 0 := by
  refine ⟨(fun z ↦ contextCoeff i z / 14), phi, ?_, ?_⟩
  · norm_num [phi]
  · intro u z
    exact interaction_profile_factor_at_zero i u z

 theorem witness_allCoordinatesRankOne :
    AllCoordinatesInteractionContrastRankOne cornerQ6 witnessWorld := by
  intro i
  exact interactionContrastRankOne_anchor cornerQ6 witnessWorld i 0
    canonicalInteractionContrastAnchor (witness_rankOne_at_zero i)

private theorem interaction_profile_factor_any_anchor
    (i : Fin 6) (u0 u : Fin 3) (z : Fin 6 → Fin 3) :
    interactionContrastProfile cornerQ6 witnessWorld i u0 u z =
      (phi u - phi u0) * (contextCoeff i z / 14) := by
  rw [interactionContrastProfile_change_anchor
    (q := cornerQ6) (F := witnessWorld) (i := i) (u0 := 0) (v0 := u0)
    (u := u) (z := z)]
  rw [interaction_profile_factor_at_zero i u z,
    interaction_profile_factor_at_zero i u0 z]
  ring

 theorem witness_atMostTwoProfiles (i : Fin 6) :
    HasAtMostTwoInteractionProfiles cornerQ6 witnessWorld i
      canonicalInteractionContrastAnchor := by
  refine ⟨0, 1, ?_⟩
  intro u
  fin_cases u
  · left
    intro z
    rfl
  · right
    intro z
    rfl
  · left
    intro z
    rw [interaction_profile_factor_any_anchor,
      interaction_profile_factor_any_anchor]
    norm_num [phi]

/-! ## Active cell and final formal falsification -/

def witnessCell : ActiveDecisionCell 5 (Fin 3) where
  q := cornerQ6
  selected := selected6
  competitor := competitor6
  selectedMax := selectedMax6
  selectedMin := selectedMin6
  competitorMax := competitorMax6
  competitorMin := competitorMin6
  responseMax := responseMax6
  responseMin := responseMin6

 theorem witness_balanced : witnessCell.BalancedComplement := by
  simp [witnessCell, ActiveDecisionCell.BalancedComplement,
    selected6, competitor6] <;> decide

 theorem witness_cell_valid : witnessCell.Valid witnessWorld := by
  rw [activeDecisionCell_valid_iff_polyhedral]
  refine ⟨by simp [witnessCell, selected6, competitor6], ?_, ?_, ?_, ?_,
    response_max, response_min, ?_⟩
  · intro z
    change witnessWorld z - selected6.sum
        (fun j ↦ productResponse cornerQ6 witnessWorld j (z j)) ≤
      witnessWorld selectedMax6 - selected6.sum
        (fun j ↦ productResponse cornerQ6 witnessWorld j (selectedMax6 j))
    rw [selected_max_eval]
    exact (selected_bounds z).2
  · intro z
    change witnessWorld selectedMin6 - selected6.sum
        (fun j ↦ productResponse cornerQ6 witnessWorld j (selectedMin6 j)) ≤
      witnessWorld z - selected6.sum
        (fun j ↦ productResponse cornerQ6 witnessWorld j (z j))
    rw [selected_min_eval]
    exact (selected_bounds z).1
  · intro z
    change witnessWorld z - competitor6.sum
        (fun j ↦ productResponse cornerQ6 witnessWorld j (z j)) ≤
      witnessWorld competitorMax6 - competitor6.sum
        (fun j ↦ productResponse cornerQ6 witnessWorld j (competitorMax6 j))
    rw [competitor_max_eval]
    exact (competitor_bounds z).2
  · intro z
    change witnessWorld competitorMin6 - competitor6.sum
        (fun j ↦ productResponse cornerQ6 witnessWorld j (competitorMin6 j)) ≤
      witnessWorld z - competitor6.sum
        (fun j ↦ productResponse cornerQ6 witnessWorld j (z j))
    rw [competitor_min_eval]
    exact (competitor_bounds z).1
  · intro i hi j hj
    have h := witness_strictTopC i hi j hj
    rw [response_osc i, response_osc j] at h
    exact h.le

 theorem witness_rankOneNormalizedBalanced :
    RankOneNormalizedBalancedWorld witnessCell witnessWorld := by
  exact ⟨cornerQ6_nonnegative, cornerQ6_normalized, witness_balanced,
    witness_cell_valid, witnessWorld_unitInteraction, witness_allCoordinatesRankOne⟩

 theorem strict_twoProfile_rankOne_m6_violates_m_minus_one :
    RankOneNormalizedBalancedWorld witnessCell witnessWorld ∧
    StrictTopC witnessCell witnessWorld ∧
    (∀ i, HasAtMostTwoInteractionProfiles cornerQ6 witnessWorld i
      canonicalInteractionContrastAnchor) ∧
    (5 : ℝ) < 2 * (productCompressionLoss witnessWorld
        (productResponse cornerQ6 witnessWorld) selected6 -
      productCompressionLoss witnessWorld
        (productResponse cornerQ6 witnessWorld) competitor6) := by
  refine ⟨witness_rankOneNormalizedBalanced, ?_, witness_atMostTwoProfiles,
    witness_violates_five⟩
  simpa [StrictTopC, witnessCell] using witness_strictTopC

 theorem witness_rankOne_constant_five_false :
    ¬ RankOneDecisionInteractionConstantAtMost witnessCell 5 := by
  intro h
  have hbad := h witnessWorld witness_rankOneNormalizedBalanced
  change 2 * (productCompressionLoss witnessWorld
      (productResponse cornerQ6 witnessWorld) selected6 -
    productCompressionLoss witnessWorld
      (productResponse cornerQ6 witnessWorld) competitor6) ≤ 5 at hbad
  rw [witness_doubled_gap] at hbad
  norm_num at hbad

end CIGAMF.P13.D6StrictTwoProfileRankOneM6CounterexampleV2
